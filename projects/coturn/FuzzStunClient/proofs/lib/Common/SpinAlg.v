(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the relation carries a flag after curl/fuzz_fnmatch's Reusable/YK18.v (srealizesE, srealizesM, srealizes_fo), with a node's dead refusal arm at the flag false, and for LPS 727298f3 srz_node asks the read-only-backing premise (RomBase.sys_rob) and the runs are over run_segments. *)
(* The relation carries a flag, after curl/fuzz_fnmatch Reusable/YK18.v
   (srealizesE, srealizesM, srealizes_fo): [srealizesM b] is one inductive whose node may leave an arm at the
   flag [false] when the arm is a dead refusal ([Corpus/HaltsFO.dead_sib]); [srealizesE] is [srealizesM false],
   and [srealizesM true] gives [HaltsFO.fo_exits] ([srealizes_fo]).  The lemma names are kept; each is stated
   at every flag, the spin case and the off-path spin lemmas at [false]. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import
  SimInv ExitSim CatSim MmapSim ShapeAlg DivergeSim LazyFrame SymTac.
(* (B2): [srz_node] asks [RomBase.sys_rob] at each node, exactly as [ShapeAlg.rz_node] does,
   so that the read-only-backing widening ([Cfg/RomStable.realizes_wrom]) has an srealizes
   twin.  Required without Import, as in ShapeAlg.v:16, so none of RomBase's short names
   ([wrom], [mem_ext], [memfree]) enters this file's scope. *)
Require OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.Cfg.RomBase.
(* The forced-only exit obligation and the dead refusal arm. *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Corpus Require HaltsFO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

(* The flagged relation.  A node may give an arm the flag [false] where it has the flag [true] only when that
   arm is a refusal of an allocation call whose node also has an arm that is no refusal: under
   [forced_only_cfg] such an arm is no step ([HaltsFO.fo_dead_of_sib]).  The spin case has the flag [false]. *)
Inductive srealizesM : bool -> config -> TSet -> Prop :=
| srzM_node : forall b c (I : Type) (evs : I -> list event) (nx : I -> config)
                     (T : I -> TSet) (i0 : I) (bi : I -> bool),
    node_ok segs c I evs nx ->
    RomBase.sys_rob segs c ->
    (forall i, srealizesM (bi i) (nx i) (T i)) ->
    (forall i, b = true -> bi i = false -> exists j, HaltsFO.dead_sib c (nx j) (nx i)) ->
    srealizesM b c (t_alt (fun i => t_emit (evs i) (T i)))
| srzM_halt : forall b c,
    m_halted (cfg_model c) <> None ->
    srealizesM b c t_nil
| srzM_spin : forall c,
    to_spin segs (cfg_ms c) (cfg_model c) ->
    m_halted (cfg_model c) = None ->
    srealizesM false c t_nil
| srzM_conseq : forall b c T T',
    srealizesM b c T -> t_eq T T' -> srealizesM b c T'.

(* The constructors at one flag throughout, under their old names. *)
Lemma srz_node {b : bool} : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                    (T : I -> TSet) (i0 : I),
    node_ok segs c I evs nx ->
    RomBase.sys_rob segs c ->
    (forall i, srealizesM b (nx i) (T i)) ->
    srealizesM b c (t_alt (fun i => t_emit (evs i) (T i))).
Proof.
  intros c I evs nx T i0 Hnode Hrob Hc.
  apply (srzM_node b c I evs nx T i0 (fun _ => b) Hnode Hrob Hc).
  intros i Hb Hbi. cbv beta in Hbi. congruence.
Qed.

Lemma srz_halt {b : bool} : forall c, m_halted (cfg_model c) <> None -> srealizesM b c t_nil.
Proof. intros c Hh. exact (srzM_halt b c Hh). Qed.

Lemma srz_spin : forall c,
    to_spin segs (cfg_ms c) (cfg_model c) -> m_halted (cfg_model c) = None -> srealizesM false c t_nil.
Proof. intros c Hs Hh. exact (srzM_spin c Hs Hh). Qed.

Lemma srz_conseq {b : bool} : forall c T T', srealizesM b c T -> t_eq T T' -> srealizesM b c T'.
Proof. intros c T T' H Heq. exact (srzM_conseq b c T T' H Heq). Qed.

(* The flag [false] forgets the dead-arm duty. *)
Lemma srealizesM_E {b : bool} : forall c T, srealizesM b c T -> srealizesM false c T.
Proof.
  intros c T H;
    induction H as [b c I evs nx T i0 bi Hnode Hrob Hcont IH Hdead | b c Hh | c Hspin Hh | b c T T' H IH Heq].
  - apply (srzM_node false c I evs nx T i0 (fun _ => false) Hnode Hrob IH).
    intros i Hf. discriminate Hf.
  - exact (srzM_halt false c Hh).
  - exact (srzM_spin c Hspin Hh).
  - exact (srzM_conseq false c T T' IH Heq).
Qed.

Lemma srealizesM_le {b : bool} : forall b' c T, (b = true -> b' = true) -> srealizesM b' c T -> srealizesM b c T.
Proof.
  intros b' c T Hle H. destruct b.
  - rewrite (Hle eq_refl) in H. exact H.
  - exact (srealizesM_E c T H).
Qed.

Lemma srealizes_of_realizes {b : bool} : forall c T,
  realizes segs c T -> srealizesM b c T.
Proof.
  intros c T H;
    (* (B2): [rz_node] and [srz_node] ask the same [RomBase.sys_rob], so the forgetful
       direction passes [Hrob] straight through. *)
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq].
  - exact (srz_node c I evs nx T i0 Hnode Hrob IH).
  - exact (srz_halt c Hh).
  - exact (srz_conseq c T T' IH Heq).
Qed.

Lemma srz_spinning : forall c, spinning segs c -> srealizesM false c t_nil.
Proof. intros c [Hspin Hh]. exact (srz_spin c Hspin Hh). Qed.

Lemma srealizes_nonempty {b : bool} : forall c T, srealizesM b c T -> T [].
Proof.
  intros c T H;
    induction H as [b c I evs nx T i0 bi Hnode Hrob Hcont IH Hdead | b c Hh | c Hspin Hh | b c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

(* The forced-only exit obligation of the flag [true] (curl's [srealizes_fo]). *)
Lemma srealizesM_fo_gen : forall b c T, srealizesM b c T -> b = true -> HaltsFO.fo_exits segs c T.
Proof.
  intros b c T H;
    induction H as [b c I evs nx T i0 bi Hnode Hrob Hcont IH Hdead | b c Hh | c Hspin Hh | b c T T' H IH Heq];
    intros Hb.
  - apply (HaltsFO.fo_node segs c I evs nx T i0 (fun i => bi i = false) Hnode).
    + intros i Hbi. destruct (Hdead i Hb Hbi) as [j Hj].
      exact (HaltsFO.fo_dead_of_sib segs c I evs nx j i Hnode Hj).
    + intros i Hbi. apply IH.
      destruct (bi i) eqn:E; [reflexivity | exfalso; apply Hbi; reflexivity].
    + intros i _. exact (srealizes_nonempty _ _ (Hcont i)).
  - apply HaltsFO.fo_halted. exact Hh.
  - discriminate Hb.
  - eapply HaltsFO.fo_conseq; [exact (IH Hb) | exact Heq].
Qed.

Lemma srealizes_fo : forall c T, srealizesM true c T -> HaltsFO.fo_exits segs c T.
Proof. intros c T H. exact (srealizesM_fo_gen true c T H eq_refl). Qed.

Lemma srealizes_pclosed {b : bool} : forall c T, srealizesM b c T ->
  forall tr tr', T tr -> is_prefix tr' tr -> T tr'.
Proof.
  intros c T H;
    induction H as [b c I evs nx T i0 bi Hnode Hrob Hcont IH Hdead | b c Hh | c Hspin Hh | b c T T' H IH Heq];
    intros tr tr' HT Hp.
  - destruct HT as [i [Hpre | (tr0 & -> & HT0)]]; exists i.
    + left. eapply is_prefix_trans; eauto.
    + apply is_prefix_app_split in Hp as [Hp | (tr0' & -> & Hp)].
      * left. exact Hp.
      * right. exists tr0'. split; [reflexivity | eapply IH; eauto].
  - unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
  - unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
  - apply Heq. eapply IH; [apply Heq; exact HT | exact Hp].
Qed.

Lemma srealizes_star_only {b : bool} : forall c T, srealizesM b c T ->
  forall tr c', star segs c tr c' -> T tr.
Proof.
  intros c T H;
    induction H as [b c I evs nx T i0 bi Hnode Hrob Hcont IH Hdead | b c Hh | c Hspin Hh | b c T T' H IH Heq];
    intros tr c' Hstar.
  - inversion Hstar as [|c1 e c2 tr2 c3 Hss Hstar2]; subst.
    + exists i0. left. apply is_prefix_nil.
    + destruct Hnode as [_ Hsound].
      destruct (Hsound e (SNext c2) Hss) as (i & -> & Heq2).
      inversion Heq2; subst c2.
      exists i. right. exists tr2.
      split; [reflexivity | eapply IH; exact Hstar2].
  - destruct (star_halted_nil segs c tr c' Hh Hstar) as [-> _]. reflexivity.
  - destruct c as [ms model]; cbn in Hspin, Hh.
    exact (spin_star_nil segs ms model tr c' Hspin Hh Hstar).
  - apply Heq. eapply IH; exact Hstar.
Qed.

Lemma srealizes_admits {b : bool} : forall c T, srealizesM b c T ->
  forall tr, T tr -> obs_trace segs c tr.
Proof.
  intros c T H;
    induction H as [b c I evs nx T i0 bi Hnode Hrob Hcont IH Hdead | b c Hh | c Hspin Hh | b c T T' H IH Heq];
    intros tr HT.
  - destruct Hnode as [Hcomp _].
    destruct HT as [i [Hpre | (tr0 & -> & HT0)]].
    + exists (evs i), (nx i). split; [apply star_one; apply Hcomp | exact Hpre].
    + destruct (IH i tr0 HT0) as (tr'' & c'' & Hstar & Hp).
      exists (evs i ++ tr''), c''.
      split; [eapply star_step; [apply Hcomp | exact Hstar]
             | apply is_prefix_app_mono; exact Hp].
  - unfold t_nil in HT; subst tr. apply obs_trace_nil.
  - unfold t_nil in HT; subst tr. apply obs_trace_nil.
  - apply IH. apply Heq. exact HT.
Qed.

Theorem srealizes_obs_iff {b : bool} : forall c T, srealizesM b c T ->
  forall tr, obs_trace segs c tr <-> T tr.
Proof.
  intros c T H tr. split.
  - intros (tr' & c' & Hstar & Hp).
    eapply srealizes_pclosed;
      [exact H | eapply srealizes_star_only; eauto | exact Hp].
  - apply (srealizes_admits c T H).
Qed.

Lemma srealizes_step {b : bool} : forall c T e c',
  srealizesM b c T -> sstep segs c e (SNext c') -> exists T', srealizesM false c' T'.
Proof.
  intros c T e c' H; revert e c';
    induction H as [b c I evs nx T i0 bi Hnode Hrob Hcont IH Hdead | b c Hh | c Hspin Hh | b c T T' H IH Heq];
    intros e c' Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e (SNext c') Hss) as (i & _ & Heq2).
    inversion Heq2; subst c'. exists (T i). exact (srealizesM_E _ _ (Hcont i)).
  - exfalso. apply Hh. eapply sstep_halted_none; exact Hss.
  - destruct (silent_loop_sstep segs (spinning segs) c e (SNext c')
                (spinning_silent_loop segs) (conj Hspin Hh) Hss)
      as (_ & c'' & Heq2 & Hsp').
    injection Heq2 as ->.
    exists t_nil. exact (srz_spinning _ Hsp').
  - eapply IH; exact Hss.
Qed.

Lemma srealizes_no_sserror {b : bool} : forall c T e,
  srealizesM b c T -> ~ sstep segs c e SError.
Proof.
  intros c T e H; revert e;
    induction H as [b c I evs nx T i0 bi Hnode Hrob Hcont IH Hdead | b c Hh | c Hspin Hh | b c T T' H IH Heq];
    intros e Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate.
  - apply Hh. eapply sstep_halted_none; exact Hss.
  - destruct c as [ms model]; cbn in Hspin, Hh.
    exact (spin_no_sstep_error segs ms model Hspin Hh e Hss).
  - eapply IH; exact Hss.
Qed.

Definition srz_path (c : config) : Prop := exists T, srealizesM false c T.

Theorem srealizes_no_error {b : bool} : forall c T,
  srealizesM b c T -> ~ reaches_error segs c.
Proof.
  intros c T H.
  apply (inv_no_reaches_error segs srz_path).
  - intros c1 e c2 (T1 & H1) Hss. eapply srealizes_step; eauto.
  - intros c1 e (T1 & H1) Hss. eapply srealizes_no_sserror; eauto.
  - exists T; exact (srealizesM_E _ _ H).
Qed.

Lemma srz_silent1 {b : bool} : forall c c' T,
  node_ok segs c unit (fun _ => []) (fun _ => c') ->
  RomBase.sys_rob segs c ->
  srealizesM b c' T ->
  srealizesM b c T.
Proof.
  intros c c' T Hnode Hrob Hc.
  apply (srz_conseq c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (srz_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode Hrob).
    intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply srealizes_nonempty; exact Hc ].
Qed.

Lemma srz_emit1 {b : bool} : forall c c' e T,
  node_ok segs c unit (fun _ => e) (fun _ => c') ->
  RomBase.sys_rob segs c ->
  srealizesM b c' T ->
  srealizesM b c (t_emit e T).
Proof.
  intros c c' e T Hnode Hrob Hc.
  apply (srz_conseq c (t_alt (fun _ : unit => t_emit e T))).
  - apply (srz_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode Hrob).
    intros []; exact Hc.
  - apply t_alt_unit.
Qed.

Lemma t_alt2_sum_eq : forall (IA IB : Type) (A B : TSet) (a0 : IA) (b0 : IB), A [] -> B [] ->
  t_eq (t_alt (fun i : IA + IB => t_emit [] (match i with inl _ => A | inr _ => B end))) (t_alt2 A B).
Proof.
  intros IA IB A B a0 b0 HA0 HB0 tr. unfold t_alt2. split.
  + intros [[i|i] Hi];
      [ left; exact (proj1 (t_emit_nil_eq A HA0 tr) Hi)
      | right; exact (proj1 (t_emit_nil_eq B HB0 tr) Hi) ].
  + intros [H | H];
      [ exists (inl a0); exact (proj2 (t_emit_nil_eq A HA0 tr) H)
      | exists (inr b0); exact (proj2 (t_emit_nil_eq B HB0 tr) H) ].
Qed.

Lemma srz_alt2 {b : bool} : forall c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet)
                        (a0 : IA) (b0 : IB),
  node_ok segs c (IA + IB) (fun _ => []) nx ->
  RomBase.sys_rob segs c ->
  (forall i, srealizesM b (nx (inl i)) A) ->
  (forall i, srealizesM b (nx (inr i)) B) ->
  srealizesM b c (t_alt2 A B).
Proof.
  intros c IA IB nx A B a0 b0 Hnode Hrob HA HB.
  assert (HA0 : A []) by (eapply srealizes_nonempty; apply (HA a0)).
  assert (HB0 : B []) by (eapply srealizes_nonempty; apply (HB b0)).
  apply (srz_conseq c
    (t_alt (fun i : IA + IB =>
              t_emit [] (match i with inl _ => A | inr _ => B end)))).
  - apply (srz_node c (IA + IB) (fun _ => []) nx
             (fun i => match i with inl _ => A | inr _ => B end)
             (inl a0) Hnode Hrob).
    intros [i|i]; [apply HA | apply HB].
  - exact (t_alt2_sum_eq IA IB A B a0 b0 HA0 HB0).
Qed.

(* A two-way node whose left arms are refusals of an allocation call and whose right arm [b0] is no refusal:
   the left arms carry the flag [false] at every flag of the node. *)
Lemma srz_alt2_ref {b : bool} : forall c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet)
                        (a0 : IA) (b0 : IB),
  node_ok segs c (IA + IB) (fun _ => []) nx ->
  RomBase.sys_rob segs c ->
  (forall i, srealizesM false (nx (inl i)) A) ->
  (forall i, srealizesM b (nx (inr i)) B) ->
  (b = true -> forall i, HaltsFO.dead_sib c (nx (inr b0)) (nx (inl i))) ->
  srealizesM b c (t_alt2 A B).
Proof.
  intros c IA IB nx A B a0 b0 Hnode Hrob HA HB Hd.
  assert (HA0 : A []) by (eapply srealizes_nonempty; apply (HA a0)).
  assert (HB0 : B []) by (eapply srealizes_nonempty; apply (HB b0)).
  apply (srz_conseq c
    (t_alt (fun i : IA + IB =>
              t_emit [] (match i with inl _ => A | inr _ => B end)))).
  - apply (srzM_node b c (IA + IB) (fun _ => []) nx
             (fun i => match i with inl _ => A | inr _ => B end)
             (inl a0) (fun i => match i with inl _ => false | inr _ => b end) Hnode Hrob).
    + intros [i|i]; [apply HA | apply HB].
    + intros [i|i] Hb Hbi.
      * exists (inr b0). exact (Hd Hb i).
      * cbv beta iota in Hbi. congruence.
  - exact (t_alt2_sum_eq IA IB A B a0 b0 HA0 HB0).
Qed.

Lemma srz_step {b : bool} : forall ms model ms' T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  srealizesM b (mkCfg ms' model) T ->
  srealizesM b (mkCfg ms model) T.
Proof.
  intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
  (* (B2): an instruction configuration has no [ms_rom] read to show: [sys_rob_instr] *)
  eapply srz_silent1;
    [apply node_instr; eassumption
    | apply RomBase.sys_rob_instr; cbn [cfg_ms]; exact Hsvc
    | exact Hc].
Qed.

Lemma srz_msteps {b : bool} : forall ms ms' model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  srealizesM b (mkCfg ms' model) T ->
  srealizesM b (mkCfg ms model) T.
Proof.
  intros ms ms' model T Hh Hlazy Hms;
    induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH];
    intro Hc; [exact Hc|].
  eapply srz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
                   | apply IH; exact Hc].
Qed.

Lemma node_instr_disjoint : forall ms model ms' ranges,
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms
    = MachineOk (@mkAccessReport machine_state ms' ranges) ->
  accesses_outside_lazy ranges (m_vm_lazy model) ->
  node_ok segs (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
  intros ms model ms' ranges Hh Hsvc Hstep Hout.
  pose proof (mi_account_step_disjoint segs ms model ms' ranges Hstep Hout)
    as Hacc.
  split.
  - intros []. apply (sstep_instr segs ms model ms' model); assumption.
  - intros e st Hss.
    inversion Hss; subst; try congruence.
    match goal with
    | H : mi_account_step _ _ _ = MachineOk _ |- _ =>
        rewrite Hacc in H; injection H; intros; subst
    end.
    exists tt. split; reflexivity.
Qed.

Lemma rz_step_disjoint : forall ms model ms' ranges T,
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms
    = MachineOk (@mkAccessReport machine_state ms' ranges) ->
  accesses_outside_lazy ranges (m_vm_lazy model) ->
  realizes segs (mkCfg ms' model) T ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros ms model ms' ranges T Hh Hsvc Hstep Hout Hc.
  (* (B2): an instruction configuration has no [ms_rom] read to show *)
  eapply rz_silent1;
    [ eapply node_instr_disjoint; eassumption
    | apply RomBase.sys_rob_instr; cbn [cfg_ms]; exact Hsvc
    | exact Hc].
Qed.

Lemma srz_write1 {b : bool} : forall ms model x8 buf T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     srealizesM b (mkCfg (advance_past_svc
                         (set_gpr0 ms (len_word (firstn n buf)))) model) T) ->
  srealizesM b (mkCfg ms model) (t_write_ch (Z_to_bv 64 1) buf T).
Proof.
  intros ms model x8 buf T Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hbm Hnb Hc.
  unfold t_write_ch.
  apply (srz_node (mkCfg ms model) (wr_index buf)
           (fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) buf))
           (fun i => mkCfg (advance_past_svc
                              (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                           model)
           (fun _ => T) (wr_full buf Hnb)).
  - apply (node_write1 segs ms model x8 buf); assumption.
  - apply (sys_rob_write1 segs ms model x8 buf); assumption.
  - intros [n [Hn1 Hn2]]. cbn [proj1_sig]. apply Hc; assumption.
Qed.

Lemma srz_exit {b : bool} : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  srealizesM b (mkCfg ms model)
            (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros ms model x8 Hh Hsvc Hx8.
  apply srealizes_of_realizes. apply (rz_exit segs ms model x8); assumption.
Qed.

Lemma srz_silent_all {b : bool} : forall c (I : Type) (nx : I -> config) (T : TSet) (i0 : I),
  node_ok segs c I (fun _ => []) nx ->
  RomBase.sys_rob segs c ->
  (forall i, srealizesM b (nx i) T) ->
  srealizesM b c T.
Proof.
  intros c I nx T i0 Hnode Hrob HT.
  assert (HT0 : T []) by (eapply srealizes_nonempty; apply (HT i0)).
  apply (srz_conseq c (t_alt (fun _ : I => t_emit [] T))).
  - apply (srz_node c I (fun _ => []) nx (fun _ => T) i0 Hnode Hrob).
    intros i; exact (HT i).
  - intro tr. split.
    + intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
    + intro H. exists i0. exact (proj2 (t_emit_nil_eq T HT0 tr) H).
Qed.

Lemma node_munmap : forall ms model x8,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  node_ok segs (mkCfg ms model) ({e : Z | In e munmap_errnos} + unit)
    (fun _ => [])
    (fun i => match i with
       | inl (exist _ e _) =>
           mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
       | inr _ =>
           mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                 (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1))
                               model)
       end).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno Hargs. split.
  - intros [[e He] | []]; cbn.
    + rewrite <- (apply_effect_no_write ms (errno_ret e)).
      apply (sstep_syscall segs ms model x8 (mkEffect (errno_ret e) [] [])
               model model []).
      * exact Hh.
      * exact Hsvc.
      * apply munmap_fail_ok; assumption.
      * exact Hh.
      * apply materialize_model_accesses_no_lazy. exact Hlazy.
    + apply (sstep_syscall segs ms model x8 (munmap_eff ms)
               (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
               (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
      * exact Hh.
      * exact Hsvc.
      * apply munmap_ok; assumption.
      * rewrite munmap_model_halted; exact Hh.
      * apply materialize_model_accesses_no_lazy.
        exact (munmap_model_no_lazy _ _ _ Hlazy).
  - intros e st Hss.
    destruct (sstep_munmap_inv segs ms model x8 e st Hh Hlazy Hsvc Hno Hargs Hss)
      as [-> [(er & Her & ->) | ->]].
    + exists (inl (exist _ er Her)). split; reflexivity.
    + exists (inr tt). split; reflexivity.
Qed.

(* Off the halting path ([Common/NoReserve.v] has its own nodes): at the flag [false]. *)
Lemma srz_munmap : forall ms model x8 T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  (forall e, In e munmap_errnos ->
     srealizesM false (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) T) ->
  srealizesM false (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                   (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) T ->
  srealizesM false (mkCfg ms model) T.
Proof.
  intros ms model x8 T Hh Hlazy Hsvc Hno Hargs Hfail Hc.
  apply (srz_silent_all (mkCfg ms model) ({e : Z | In e munmap_errnos} + unit)
           (fun i => match i with
              | inl (exist _ e _) =>
                  mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
              | inr _ =>
                  mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1))
                                      model)
              end) T (inr tt));
    [apply (node_munmap ms model x8); assumption | |].
  (* (B2): munmap (215) does not read [in_mem] *)
  { eapply RomBase.sys_rob_memfree; [exact Hsvc | rewrite Hno; exact RomBase.memfree_215]. }
  intros [[e He] | []]; cbn; [exact (Hfail e He) | exact Hc].
Qed.

Lemma node_mmap : forall ms model x8,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  node_ok segs (mkCfg ms model)
    ({e : Z | In e mmap_errnos}
     + {a : word | grant_ok (ms_gpr ms 0) model a
                     (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true})
    (fun _ => [])
    (fun i => match i with
       | inl (exist _ e _) =>
           mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
       | inr (exist _ a _) =>
           mkCfg (advance_past_svc
                    (apply_effect ms
                       (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                 (mmap_model a (page_round_up (ms_gpr ms 1)) model)
       end).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno Hargs Hdecl.
  set (n := page_round_up (ms_gpr ms 1)).
  split.
  - intros [[e He] | [a Ha]]; cbn.
    + rewrite <- (apply_effect_no_write ms (errno_ret e)).
      apply (sstep_syscall segs ms model x8 (mkEffect (errno_ret e) [] [])
               model model []).
      * exact Hh.
      * exact Hsvc.
      * apply mmap_fail_ok; assumption.
      * exact Hh.
      * apply materialize_model_accesses_no_lazy. exact Hlazy.
    + apply (sstep_syscall segs ms model x8 (mkEffect a [] [(a, n)])
               (mmap_model a n model) (mmap_model a n model) []).
      * exact Hh.
      * exact Hsvc.
      * apply mmap_succ_ok; assumption.
      * rewrite mmap_model_halted; exact Hh.
      * apply materialize_model_accesses_no_lazy.
        exact (eq_trans (mmap_model_lazy _ _ _) Hlazy).
  - intros e st Hss.
    destruct (sstep_mmap_inv segs ms model x8 e st Hh Hlazy Hsvc Hno Hargs Hdecl Hss)
      as [-> [(er & Her & ->) | (a & Ha & ->)]].
    + exists (inl (exist _ er Her)). split; reflexivity.
    + exists (inr (exist _ a Ha)). split; reflexivity.
Qed.

(* Off the halting path, at the flag [false]. *)
Lemma srz_mmap : forall ms model x8 A B,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  (forall e, In e mmap_errnos ->
     srealizesM false (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) A) ->
  (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
     srealizesM false (mkCfg (advance_past_svc
                        (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                      (mmap_model a (page_round_up (ms_gpr ms 1)) model)) B) ->
  (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
  srealizesM false (mkCfg ms model) (t_alt2 A B).
Proof.
  intros ms model x8 A B Hh Hlazy Hsvc Hno Hargs Hdecl HA HB Hex.
  destruct Hex as [a0 Ha0].
  eapply (srz_alt2 (mkCfg ms model)
            {e : Z | In e mmap_errnos}
            {a : word | grant_ok (ms_gpr ms 0) model a
                          (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true}
            _ A B
            (exist _ ENOMEM ENOMEM_in_mmap_errnos) (exist _ a0 Ha0)).
  - apply (node_mmap ms model x8); assumption.
  (* (B2): mmap (222) does not read [in_mem] *)
  - eapply RomBase.sys_rob_memfree; [exact Hsvc | rewrite Hno; exact RomBase.memfree_222].
  - intros [e He]; cbn. apply HA; exact He.
  - intros [a Ha]; cbn. apply HB; exact Ha.
Qed.

(* Off the halting path: a refusal that spins, at the flag [false]. *)
Lemma srz_mmap_spin : forall ms model x8 B,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  (forall e, In e mmap_errnos ->
     to_spin segs (advance_past_svc (set_gpr0 ms (errno_ret e))) model) ->
  (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
     srealizesM false (mkCfg (advance_past_svc
                        (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                      (mmap_model a (page_round_up (ms_gpr ms 1)) model)) B) ->
  (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
  srealizesM false (mkCfg ms model) B.
Proof.
  intros ms model x8 B Hh Hlazy Hsvc Hno Hargs Hdecl Hspin HB Hex.
  destruct Hex as [a0 Ha0].
  assert (HB0 : B []) by (eapply srealizes_nonempty; apply (HB a0 Ha0)).
  eapply srz_conseq.
  { apply (srz_node (mkCfg ms model)
             ({e : Z | In e mmap_errnos}
              + {a : word | grant_ok (ms_gpr ms 0) model a
                              (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true})
             (fun _ => [])
             (fun i => match i with
                | inl (exist _ e _) =>
                    mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
                | inr (exist _ a _) =>
                    mkCfg (advance_past_svc
                             (apply_effect ms
                                (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                          (mmap_model a (page_round_up (ms_gpr ms 1)) model)
                end)
             (fun i => match i with inl _ => t_nil | inr _ => B end)
             (inr (exist _ a0 Ha0))).
    - apply (node_mmap ms model x8); assumption.
    (* (B2): mmap (222) does not read [in_mem] *)
    - eapply RomBase.sys_rob_memfree; [exact Hsvc | rewrite Hno; exact RomBase.memfree_222].
    - intros [[e He] | [a Ha]]; cbn.
      + apply srz_spin; cbn; [apply Hspin; exact He | exact Hh].
      + apply HB; exact Ha. }
  intro tr. split.
  - intros [[[e He] | [a Ha]] Hi]; cbn in Hi.
    + apply (t_emit_nil_eq t_nil eq_refl tr) in Hi.
      unfold t_nil in Hi. subst tr. exact HB0.
    + exact (proj1 (t_emit_nil_eq B HB0 tr) Hi).
  - intro HBtr. exists (inr (exist _ a0 Ha0)).
    exact (proj2 (t_emit_nil_eq B HB0 tr) HBtr).
Qed.

End WithSegs.

(* The relation the agreement statements read: the flag [false] (curl's [srealizesE]). *)
Notation srealizesE segs := (srealizesM segs false).

(* Off the halting path: the agreement of two flagged derivations. *)
Theorem spin_shape_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb (rrnd : EntryDraw) (rlim : Z)
         target_segs apc aph asp abrk amb (arnd : EntryDraw) (alim : Z)
         (T : TSet) (inp : ProcInput),
  srealizesE (run_segments source_segs inp rsp rmb)
    (init_config (run_segments source_segs inp rsp rmb) rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  srealizesE (run_segments target_segs inp asp amb)
    (init_config (run_segments target_segs inp asp amb) apc aph asp abrk amb arnd alim inp) T ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    T inp Hsource Htarget.
  split.
  { apply no_error_run_modeled.
    eapply srealizes_no_error; exact Hsource. }
  right. split.
  - intro tr. cbn.
    rewrite (srealizes_obs_iff (run_segments source_segs inp rsp rmb) _ T Hsource tr).
    rewrite (srealizes_obs_iff (run_segments target_segs inp asp amb) _ T Htarget tr).
    reflexivity.
  - cbn. eapply srealizes_no_error; exact Htarget.
Qed.

Ltac chain_mst_sp :=
  first [ (eapply srz_msteps; [ sym_halted | sym_no_lazy | | ])
        | chain_mst ].

Lemma chain_mst_srealizes : forall segs ms ms' model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  srealizesE segs (mkCfg ms' model) T ->
  srealizesE segs (mkCfg ms model) T.
Proof.
  intros segs ms ms' model T Hh Hlazy Hms Hr.
  chain_mst_sp; [exact Hms | exact Hr].
Qed.

Lemma chain_mst_srealizes_mmap : forall segs ms ms' model a n T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  srealizesE segs (mkCfg ms' (MmapSim.mmap_model a n model)) T ->
  srealizesE segs (mkCfg ms (MmapSim.mmap_model a n model)) T.
Proof.
  intros segs ms ms' model a n T Hh Hlazy Hms Hr.
  chain_mst_sp; [exact Hms | exact Hr].
Qed.

Corollary srz_spin_alloc_writes : forall segs ms0 ms model x8 bs cs,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  msteps segs ms0 ms ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  (forall e, In e mmap_errnos ->
     to_spin segs (advance_past_svc (set_gpr0 ms (errno_ret e))) model) ->
  (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
     MmapSim.twm segs
       (advance_past_svc
          (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
       (mmap_model a (page_round_up (ms_gpr ms 1)) model) bs cs) ->
  (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
  bufs_modeled bs ->
  srealizesE segs (mkCfg ms0 model) (t_writes bs (t_exit cs (m_fs model))).
Proof.
  intros segs ms0 ms model x8 bs cs Hh Hlazy Hfd Hms Hsvc Hno Hargs Hdecl
    Hrefuse Hgrant Hex Hbs.
  eapply srz_msteps; [exact Hh | exact Hlazy | exact Hms |].
  eapply srz_mmap_spin; try eassumption.
  intros a Ha. apply srealizes_of_realizes.
  rewrite <- (mmap_model_fs a (page_round_up (ms_gpr ms 1)) model).
  apply twm_realizes;
    [ rewrite mmap_model_halted; exact Hh
    | exact (eq_trans (mmap_model_lazy _ _ _) Hlazy)
    | apply mmap_model_fd1chan; exact Hfd
    | apply Hgrant; exact Ha
    | exact Hbs ].
Qed.

Section SpinBranchReal.
Variable segs : list Segment.
Variables (ms : machine_state) (model : Model) (x8 : word).
Variables (bs : list (list byte)) (cs : word).

Hypothesis Hh : m_halted model = None.
Hypothesis Hlazy : m_vm_lazy model = [].
Hypothesis Hfd : fd1chan model.
Hypothesis Hsvc : ms_svc_pending ms = Some x8.
Hypothesis Hno : bv_unsigned x8 = 222%Z.
Hypothesis Hargs : mmap_args_ok ms.
Hypothesis Hdecl :
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false.
Hypothesis Hrefuse : forall e, In e mmap_errnos ->
  to_spin segs (advance_past_svc (set_gpr0 ms (errno_ret e))) model.
Hypothesis Hgrant : forall a,
  grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
  MmapSim.twm segs
    (advance_past_svc
       (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
    (mmap_model a (page_round_up (ms_gpr ms 1)) model) bs cs.
Hypothesis Hex : exists a,
  grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true.
Hypothesis Hbs : bufs_modeled bs.

Theorem spin_branch_node_srealizes :
  srealizesE segs (mkCfg ms model) (t_writes bs (t_exit cs (m_fs model))).
Proof.
  eapply srz_mmap_spin; try eassumption.
  intros a Ha. apply srealizes_of_realizes.
  rewrite <- (mmap_model_fs a (page_round_up (ms_gpr ms 1)) model).
  apply twm_realizes;
    [ rewrite mmap_model_halted; exact Hh
    | exact (eq_trans (mmap_model_lazy _ _ _) Hlazy)
    | apply mmap_model_fd1chan; exact Hfd
    | apply Hgrant; exact Ha
    | exact Hbs ].
Qed.

Theorem spin_branch_node_obs_iff : forall tr,
  obs_trace segs (mkCfg ms model) tr
  <-> is_prefix tr (wevents bs ++ [ExitEv cs (m_fs model)]).
Proof.
  intro tr.
  rewrite (srealizes_obs_iff segs _ _ spin_branch_node_srealizes tr).
  apply t_writes_exit_iff.
Qed.

Theorem spin_branch_node_no_error : ~ reaches_error segs (mkCfg ms model).
Proof.
  exact (srealizes_no_error segs _ _ spin_branch_node_srealizes).
Qed.

End SpinBranchReal.
