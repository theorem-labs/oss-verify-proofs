(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the srz_spin constructor of srealizes takes a proof of False, so every srealizes derivation is spin-free and gives halting (lib/E2/Top/HaltsAsanKit.v); the lemma srz_spinning is removed and the spin cases of srealizes_star_only, srealizes_step and srealizes_no_sserror are closed by that False. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require MmapSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require ArgvEnv__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.SimInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.ExitSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.DivergeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.LazyFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.SymTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma sstep_cfg_of_sstep_nsp : forall ms model x8 e c',
  ms_svc_pending ms = Some x8 ->
  sstep segs (mkCfg ms model) e (SNext c') ->
  (forall eff m'', c' = mkCfg (advance_past_svc (apply_effect ms eff)) m'' ->
      ~ spurious_refusal_cfg CFG (sys_input segs ms x8) model eff) ->
  sstep_cfg segs CFG (mkCfg ms model) e (SNext c').
Proof.
  intros ms model x8 e c' Hsvc Hss Hnr.
  inversion Hss; subst; try congruence;
    match goal with H : ms_svc_pending ms = Some ?y |- _ => rewrite Hsvc in H; injection H as <- end.
  - eapply sstep_cfg_syscall; eauto.
  - eapply sstep_cfg_exit; eauto.
  - eapply sstep_cfg_killed; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cnode_lift_unit : forall c evs nx,
  node_ok segs c unit evs nx -> cnode_ok segs c unit evs nx.
Proof.
  intros [ms model] evs nx [Hs Hc]. split;
    [| intros e st Hss; apply Hc; eapply sstep_cfg_sub; exact Hss].
  intros []. pose proof (Hs tt) as Hs0.
  pose proof (sstep_halted_none segs _ _ _ Hs0) as Hh. cbn in Hh.
  destruct (ms_svc_pending ms) as [x8|] eqn:Hsvc;
    [| apply sstep_cfg_of_unfiltered; [apply unfiltered_nosvc; exact Hsvc | exact Hs0]].
  apply (sstep_cfg_of_sstep_nsp ms model x8); [exact Hsvc | exact Hs0 |].
  intros eff m'' Enx (Hoff & Href & eff' & m' & evs' & Hspec' & Hnr').
  destruct (m_halted m') as [code|] eqn:Hh'.
  - assert (Hx : exists e', sstep segs (mkCfg ms model) e' (SNext (mkCfg ms m'))).
    { destruct (m_killed m') as [sig|] eqn:Hk.
      + eexists. eapply sstep_killed; eauto.
      + eexists. eapply sstep_exit; eauto. }
    destruct Hx as [e' He']. destruct (Hc _ _ He') as ([] & _ & E). rewrite Enx in E.
    symmetry in E. exact (svc_succ_not_self _ _ _ _ _ Hsvc E).
  - destruct (materialize_model_accesses m' (syscall_effect_accesses eff')) as [m2|] eqn:Hmat.
    + pose proof (sstep_syscall segs ms model x8 eff' m' m2 evs' Hh Hsvc Hspec' Hh' Hmat) as He'.
      destruct (Hc _ _ He') as ([] & _ & E). rewrite Enx in E.
      rewrite (svc_succ_ret _ _ _ _ _ E) in Hnr'. rewrite Hnr' in Href. discriminate Href.
    + pose proof (sstep_syscall_materialization_fault segs ms model x8 eff' m' evs' Hh Hsvc Hspec' Hh' Hmat) as He'.
      destruct (Hc _ _ He') as (u & _ & E). discriminate E.
Qed.

(* [comment removed for export] *)

Inductive srealizes : config -> TSet -> Prop :=
| srz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                    (T : I -> TSet) (i0 : I),
    cnode_ok segs c I evs nx ->
    (forall i, srealizes (nx i) (T i)) ->
    srealizes c (t_alt (fun i => t_emit (evs i) (T i)))
| srz_halt : forall c,
    m_halted (cfg_model c) <> None ->
    srealizes c t_nil
| srz_spin : forall c,
    False /\ to_spin segs (cfg_ms c) (cfg_model c) ->
    m_halted (cfg_model c) = None ->
    srealizes c t_nil
| srz_conseq : forall c T T',
    srealizes c T -> t_eq T T' -> srealizes c T'.

(* [comment removed for export] *)
#[using="Type"] Lemma srealizes_of_realizes : forall c T,
  realizes segs c T -> srealizes c T.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq].
  - exact (srz_node c I evs nx T i0 Hnode IH).
  - exact (srz_halt c Hh).
  - exact (srz_conseq c T T' IH Heq).
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma srealizes_nonempty : forall c T, srealizes c T -> T [].
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
                   | c Hspin Hh | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

#[using="Type"] Lemma srealizes_pclosed : forall c T, srealizes c T ->
  forall tr tr', T tr -> is_prefix tr' tr -> T tr'.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
                   | c Hspin Hh | c T T' H IH Heq];
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

(* [comment removed for export] *)

#[using="Type"] Lemma srealizes_star_only : forall c T, srealizes c T ->
  forall tr c', star_cfg segs CFG c tr c' -> T tr.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
                   | c Hspin Hh | c T T' H IH Heq];
    intros tr c' Hstar.
  - inversion Hstar as [|c1 e c2 tr2 c3 Hss Hstar2]; subst.
    + exists i0. left. apply is_prefix_nil.
    + destruct Hnode as [_ Hsound].
      destruct (Hsound e (SNext c2) Hss) as (i & -> & Heq2).
      inversion Heq2; subst c2.
      exists i. right. exists tr2.
      split; [reflexivity | eapply IH; exact Hstar2].
  - destruct (star_cfg_halted_nil segs c tr c' Hh Hstar) as [-> _]. reflexivity.
  - destruct Hspin as [[] _].
  - apply Heq. eapply IH; exact Hstar.
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma srealizes_admits : forall c T, srealizes c T ->
  forall tr, T tr -> obs_trace_cfg segs CFG c tr.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
                   | c Hspin Hh | c T T' H IH Heq];
    intros tr HT.
  - destruct Hnode as [Hcomp _].
    destruct HT as [i [Hpre | (tr0 & -> & HT0)]].
    + exists (evs i), (nx i). split; [apply star_cfg_one; apply Hcomp | exact Hpre].
    + destruct (IH i tr0 HT0) as (tr'' & c'' & Hstar & Hp).
      exists (evs i ++ tr''), c''.
      split; [eapply star_cfg_step; [apply Hcomp | exact Hstar]
             | apply is_prefix_app_mono; exact Hp].
  - unfold t_nil in HT; subst tr. exists [], c. split; [apply star_cfg_refl | apply is_prefix_nil].
  - unfold t_nil in HT; subst tr. exists [], c. split; [apply star_cfg_refl | apply is_prefix_nil].
  - apply IH. apply Heq. exact HT.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem srealizes_obs_iff : forall c T, srealizes c T ->
  forall tr, obs_trace_cfg segs CFG c tr <-> T tr.
Proof.
  intros c T H tr. split.
  - intros (tr' & c' & Hstar & Hp).
    eapply srealizes_pclosed;
      [exact H | eapply srealizes_star_only; eauto | exact Hp].
  - apply srealizes_admits; exact H.
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma srealizes_step : forall c T e c',
  srealizes c T -> sstep_cfg segs CFG c e (SNext c') -> exists T', srealizes c' T'.
Proof.
  intros c T e c' H; revert e c';
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
                   | c Hspin Hh | c T T' H IH Heq];
    intros e c' Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e (SNext c') Hss) as (i & _ & Heq2).
    inversion Heq2; subst c'. exists (T i). apply Hcont.
  - exfalso. apply Hh. eapply sstep_cfg_halted_none; exact Hss.
  - destruct Hspin as [[] _].
  - eapply IH; exact Hss.
Qed.

#[using="Type"] Lemma srealizes_no_sserror : forall c T e,
  srealizes c T -> ~ sstep_cfg segs CFG c e SError.
Proof.
  intros c T e H; revert e;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
                   | c Hspin Hh | c T T' H IH Heq];
    intros e Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate.
  - apply Hh. eapply sstep_cfg_halted_none; exact Hss.
  - destruct Hspin as [[] _].
  - eapply IH; exact Hss.
Qed.

Definition srz_path (c : config) : Prop := exists T, srealizes c T.

#[using="Type"] Lemma srealizes_star : forall c T tr c',
  srealizes c T -> star_cfg segs CFG c tr c' -> exists T', srealizes c' T'.
Proof.
  intros c T tr c' H Hs. revert T H. induction Hs as [c | c1 e c2 tr2 c3 Hss Hs IH]; intros T H.
  - exists T. exact H.
  - destruct (srealizes_step _ _ _ _ H Hss) as [T2 H2]. exact (IH T2 H2).
Qed.

#[using="Type"] Theorem srealizes_no_error : forall c T,
  srealizes c T -> ~ reaches_error_cfg segs CFG c.
Proof.
  intros c T H (tr & c' & evs & Hstar & Herr).
  destruct (srealizes_star _ _ _ _ H Hstar) as [T' H']. exact (srealizes_no_sserror _ _ _ H' Herr).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma srz_silent1 : forall c c' T,
  cnode_ok segs c unit (fun _ => []) (fun _ => c') ->
  srealizes c' T ->
  srealizes c T.
Proof.
  intros c c' T Hnode Hc.
  apply (srz_conseq c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (srz_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode).
    intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply srealizes_nonempty; exact Hc ].
Qed.

#[using="Type"] Lemma srz_silent1u : forall c c' T,
  unfiltered c ->
  node_ok segs c unit (fun _ => []) (fun _ => c') ->
  srealizes c' T ->
  srealizes c T.
Proof. intros c c' T Hu Hn Hc. eapply srz_silent1; [apply cnode_lift; [exact Hu | exact Hn] | exact Hc]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srz_silent : forall c (I : Type) (nx : I -> config) (i0 : I) T,
  cnode_ok segs c I (fun _ => []) nx ->
  (forall i, srealizes (nx i) T) ->
  srealizes c T.
Proof.
  intros c I nx i0 T Hnode Hc.
  apply (srz_conseq c (t_alt (fun _ : I => t_emit [] T))).
  - apply (srz_node c I (fun _ => []) nx (fun _ => T) i0 Hnode). exact Hc.
  - eapply t_eq_trans; [apply (t_alt_const I i0)|]. apply t_emit_nil_eq. eapply srealizes_nonempty; exact (Hc i0).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srz_emit1 : forall c c' e T,
  cnode_ok segs c unit (fun _ => e) (fun _ => c') ->
  srealizes c' T ->
  srealizes c (t_emit e T).
Proof.
  intros c c' e T Hnode Hc.
  apply (srz_conseq c (t_alt (fun _ : unit => t_emit e T))).
  - apply (srz_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode).
    intros []; exact Hc.
  - apply t_alt_unit.
Qed.

#[using="Type"] Lemma srz_emit1u : forall c c' e T,
  unfiltered c ->
  node_ok segs c unit (fun _ => e) (fun _ => c') ->
  srealizes c' T ->
  srealizes c (t_emit e T).
Proof. intros c c' e T Hu Hn Hc. eapply srz_emit1; [apply cnode_lift; [exact Hu | exact Hn] | exact Hc]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srz_alt2 : forall c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet)
                        (a0 : IA) (b0 : IB),
  cnode_ok segs c (IA + IB) (fun _ => []) nx ->
  (forall i, srealizes (nx (inl i)) A) ->
  (forall i, srealizes (nx (inr i)) B) ->
  srealizes c (t_alt2 A B).
Proof.
  intros c IA IB nx A B a0 b0 Hnode HA HB.
  assert (HA0 : A []) by (eapply srealizes_nonempty; apply (HA a0)).
  assert (HB0 : B []) by (eapply srealizes_nonempty; apply (HB b0)).
  apply (srz_conseq c
    (t_alt (fun i : IA + IB =>
              t_emit [] (match i with inl _ => A | inr _ => B end)))).
  - apply (srz_node c (IA + IB) (fun _ => []) nx
             (fun i => match i with inl _ => A | inr _ => B end)
             (inl a0) Hnode).
    intros [i|i]; [apply HA | apply HB].
  - intro tr. unfold t_alt2. split.
    + intros [[i|i] Hi];
        [ left; exact (proj1 (t_emit_nil_eq A HA0 tr) Hi)
        | right; exact (proj1 (t_emit_nil_eq B HB0 tr) Hi) ].
    + intros [H | H];
        [ exists (inl a0); exact (proj2 (t_emit_nil_eq A HA0 tr) H)
        | exists (inr b0); exact (proj2 (t_emit_nil_eq B HB0 tr) H) ].
Qed.

#[using="Type"] Lemma srz_alt2u : forall c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet)
                        (a0 : IA) (b0 : IB),
  unfiltered c ->
  node_ok segs c (IA + IB) (fun _ => []) nx ->
  (forall i, srealizes (nx (inl i)) A) ->
  (forall i, srealizes (nx (inr i)) B) ->
  srealizes c (t_alt2 A B).
Proof. intros c IA IB nx A B a0 b0 Hu Hn HA HB. exact (srz_alt2 c IA IB nx A B a0 b0 (cnode_lift _ _ _ _ _ Hu Hn) HA HB). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srz_step : forall ms model ms' T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  srealizes (mkCfg ms' model) T ->
  srealizes (mkCfg ms model) T.
Proof.
  intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
  eapply srz_silent1; [apply node_instr; eassumption | exact Hc].
Qed.

#[using="Type"] Lemma srz_msteps : forall ms ms' model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  srealizes (mkCfg ms' model) T ->
  srealizes (mkCfg ms model) T.
Proof.
  intros ms ms' model T Hh Hlazy Hms;
    induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH];
    intro Hc; [exact Hc|].
  eapply srz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
                   | apply IH; exact Hc].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma node_instr_disjoint0 : forall ms model ms' ranges,
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

(* [comment removed for export] *)
#[using="Type"] Lemma node_instr_disjoint : forall ms model ms' ranges,
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms
    = MachineOk (@mkAccessReport machine_state ms' ranges) ->
  accesses_outside_lazy ranges (m_vm_lazy model) ->
  cnode_ok segs (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
  intros ms model ms' ranges Hh Hsvc Hstep Hout.
  apply cnode_lift; [apply unfiltered_nosvc; exact Hsvc | eapply node_instr_disjoint0; eassumption].
Qed.

#[using="Type"] Lemma rz_step_disjoint : forall ms model ms' ranges T,
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms
    = MachineOk (@mkAccessReport machine_state ms' ranges) ->
  accesses_outside_lazy ranges (m_vm_lazy model) ->
  realizes segs (mkCfg ms' model) T ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros ms model ms' ranges T Hh Hsvc Hstep Hout Hc.
  eapply rz_silent1; [eapply node_instr_disjoint; eassumption | exact Hc].
Qed.

#[using="Type"] Lemma srz_step_disjoint : forall ms model ms' ranges T,
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms
    = MachineOk (@mkAccessReport machine_state ms' ranges) ->
  accesses_outside_lazy ranges (m_vm_lazy model) ->
  srealizes (mkCfg ms' model) T ->
  srealizes (mkCfg ms model) T.
Proof.
  intros ms model ms' ranges T Hh Hsvc Hstep Hout Hc.
  eapply srz_silent1; [eapply node_instr_disjoint; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srz_write1 : forall ms model x8 buf T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     srealizes (mkCfg (advance_past_svc
                         (set_gpr0 ms (len_word (firstn n buf)))) model) T) ->
  srealizes (mkCfg ms model) (t_write_ch (Z_to_bv 64 1) buf T).
Proof.
  intros ms model x8 buf T Hh Hlazy Hfd Hsvc Hno Hg Hr Hbm Hnb Hc.
  unfold t_write_ch.
  apply (srz_node (mkCfg ms model) (wr_index buf)
           (fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) buf))
           (fun i => mkCfg (advance_past_svc
                              (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                           model)
           (fun _ => T) (wr_full buf Hnb)).
  - apply (node_write1 segs ms model x8 buf); assumption.
  - intros [n [Hn1 Hn2]]. cbn [proj1_sig]. apply Hc; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srz_exit : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  srealizes (mkCfg ms model)
            (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros ms model x8 Hh Hsvc Hx8.
  apply srealizes_of_realizes. apply (rz_exit segs ms model x8); assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma node_munmap0 : forall ms model x8,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  node_ok segs (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                    (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1))
                                  model)).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno Hargs. split.
  - intros []. apply (sstep_syscall segs ms model x8 (munmap_eff ms)
                        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
                        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
    + exact Hh.
    + exact Hsvc.
    + apply munmap_ok; assumption.
    + rewrite munmap_model_halted; exact Hh.
    + apply materialize_model_accesses_no_lazy.
      exact (munmap_model_no_lazy _ _ _ Hlazy).
  - intros e st Hss.
    destruct (sstep_munmap_inv segs ms model x8 e st Hh Hlazy Hsvc Hno Hargs Hss)
      as [-> ->].
    exists tt. split; reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma node_munmap : forall ms model x8,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  cnode_ok segs (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                    (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1))
                                  model)).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno Hargs.
  apply cnode_lift; [eapply unfiltered_sysno; [exact Hsvc | rewrite Hno; reflexivity]|].
  apply (node_munmap0 ms model x8); assumption.
Qed.

#[using="Type"] Lemma srz_munmap : forall ms model x8 T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  srealizes (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                   (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) T ->
  srealizes (mkCfg ms model) T.
Proof.
  intros ms model x8 T Hh Hlazy Hsvc Hno Hargs Hc.
  eapply srz_silent1; [apply (node_munmap ms model x8); assumption | exact Hc].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma rz_prune : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (keep : I -> bool) (i0 : I) K,
  ms_svc_pending ms = Some x8 ->
  alloc_no (bv_unsigned x8) = true ->
  node_ok segs (mkCfg ms model) I (fun _ => [])
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) ->
  (forall i, keep i = true -> refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = false) ->
  (forall i, keep i = false -> refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = true) ->
  keep i0 = true ->
  (forall i, keep i = true ->
     realizes segs (mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) K) ->
  realizes segs (mkCfg ms model) K.
Proof.
  intros ms model x8 I effs ms' keep i0 K Hsvc Ha Hnode Hk Hd Hi0 Hc.
  pose proof (cnode_prune segs ms model x8 I (fun _ => []) effs ms' keep i0 Hsvc Ha Hnode Hk Hd Hi0) as Hp.
  cbn beta in Hp.
  apply (rz_silent segs _ {i : I | keep i = true} _ (exist _ i0 Hi0) K Hp).
  intros [i Hki]. cbn [proj1_sig]. apply Hc. exact Hki.
Qed.

#[using="Type"] Lemma srz_prune : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (keep : I -> bool) (i0 : I) K,
  ms_svc_pending ms = Some x8 ->
  alloc_no (bv_unsigned x8) = true ->
  node_ok segs (mkCfg ms model) I (fun _ => [])
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) ->
  (forall i, keep i = true -> refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = false) ->
  (forall i, keep i = false -> refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = true) ->
  keep i0 = true ->
  (forall i, keep i = true ->
     srealizes (mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) K) ->
  srealizes (mkCfg ms model) K.
Proof.
  intros ms model x8 I effs ms' keep i0 K Hsvc Ha Hnode Hk Hd Hi0 Hc.
  pose proof (cnode_prune segs ms model x8 I (fun _ => []) effs ms' keep i0 Hsvc Ha Hnode Hk Hd Hi0) as Hp.
  cbn beta in Hp.
  apply (srz_silent _ {i : I | keep i = true} _ (exist _ i0 Hi0) K Hp).
  intros [i Hki]. cbn [proj1_sig]. apply Hc. exact Hki.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma node_mmap : forall ms model x8,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
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
  intros ms model x8 Hh Hlazy Hsvc Hno Hargs.
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
    destruct (sstep_mmap_inv segs ms model x8 e st Hh Hlazy Hsvc Hno Hargs Hss)
      as [-> [(er & Her & ->) | (a & Ha & ->)]].
    + exists (inl (exist _ er Her)). split; reflexivity.
    + exists (inr (exist _ a Ha)). split; reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cnode_mmap : forall ms model x8 a0,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  grant_ok (ms_gpr ms 0) model a0 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
  cnode_ok segs (mkCfg ms model)
    {a : word | grant_ok (ms_gpr ms 0) model a
                  (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true}
    (fun _ => [])
    (fun i => match i with exist _ a _ =>
       mkCfg (advance_past_svc
                (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
             (mmap_model a (page_round_up (ms_gpr ms 1)) model) end).
Proof.
  intros ms model x8 a0 Hh Hlazy Hsvc Hno Hargs Ha0.
  set (n := page_round_up (ms_gpr ms 1)).
  set (nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1))) in *.
  pose (IA := {e : Z | In e mmap_errnos}).
  pose (IB := {a : word | grant_ok (ms_gpr ms 0) model a nZ = true}).
  pose (effs := fun (i : IA + IB) =>
    match i with
    | inl (exist _ e _) => mkEffect (errno_ret e) [] []
    | inr (exist _ a _) => mkEffect a [] [(a, n)]
    end).
  pose (ms' := fun (i : IA + IB) =>
    match i with
    | inl _ => model
    | inr (exist _ a _) => mmap_model a n model
    end).
  pose (keep := fun (i : IA + IB) => match i with inl _ => false | inr _ => true end).
  assert (Hnode : node_ok segs (mkCfg ms model) (IA + IB) (fun _ => [])
                    (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i))).
  { pose proof (node_mmap ms model x8 Hh Hlazy Hsvc Hno Hargs) as [Hs Hc]. split.
    + intros i. pose proof (Hs i) as Hsi. destruct i as [[e He] | [a Ha]]; cbn in Hsi |- *;
        [rewrite apply_effect_no_write; exact Hsi | exact Hsi].
    + intros e st Hss. destruct (Hc e st Hss) as (i & -> & ->). exists i.
      destruct i as [[er Her] | [a Ha]]; cbn; [rewrite apply_effect_no_write|]; split; reflexivity. }
  pose proof (cnode_prune segs ms model x8 (IA + IB) (fun _ => []) effs ms' keep (inr (exist _ a0 Ha0))
                Hsvc ltac:(rewrite Hno; reflexivity) Hnode) as Hp.
  assert (Hk1 : forall i, keep i = true -> refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = false).
  { intros [[e He] | [a Ha]] Hk; [discriminate Hk|]. cbn.
    apply (grant_not_refusal segs ms x8 model a nZ (ms_gpr ms 0) Hno); [| exact Ha].
    unfold nZ. apply pruZ_nonneg. pose proof (bv_unsigned_in_range 64 (ms_gpr ms 1)). lia. }
  assert (Hk2 : forall i, keep i = false -> refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = true).
  { intros [[e He] | [a Ha]] Hk; [|discriminate Hk]. cbn. apply errno_refusal; assumption. }
  destruct (Hp Hk1 Hk2 eq_refl) as [HS HC]. split.
  - intros [a Ha]. exact (HS (exist _ (inr (exist _ a Ha)) eq_refl)).
  - intros e st Hss. destruct (HC e st Hss) as ([[[er Her] | [a Ha]] Hk] & -> & ->); [discriminate Hk|].
    exists (exist _ a Ha). split; reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srz_mmap : forall ms model x8 B,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
     srealizes (mkCfg (advance_past_svc
                        (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                      (mmap_model a (page_round_up (ms_gpr ms 1)) model)) B) ->
  (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
  srealizes (mkCfg ms model) B.
Proof.
  intros ms model x8 B Hh Hlazy Hsvc Hno Hargs HB [a0 Ha0].
  eapply (srz_silent _
            {a : word | grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true}
            _ (exist _ a0 Ha0)).
  - eapply cnode_mmap; eassumption.
  - intros [a Ha]. cbn. apply HB. exact Ha.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srz_mmap_spin : forall ms model x8 B,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
     srealizes (mkCfg (advance_past_svc
                        (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                      (mmap_model a (page_round_up (ms_gpr ms 1)) model)) B) ->
  (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
  srealizes (mkCfg ms model) B.
Proof. exact srz_mmap. Qed.

End WithSegs.

(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem spin_shape_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb (rrnd : EntryDraw) (rlim : Z)
         target_segs apc aph asp abrk amb (arnd : EntryDraw) (alim : Z)
         (T : TSet) (inp : ProcInput),
  srealizes source_segs
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  srealizes target_segs
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T ->
  error_free (run_scfg CFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free (run_scfg CFG (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg CFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg CFG (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    T inp Hsource Htarget.
  split; [| split].
  - cbn. eapply srealizes_no_error; exact Hsource.
  - cbn. eapply srealizes_no_error; exact Htarget.
  - intro tr. cbn.
    rewrite (srealizes_obs_iff source_segs _ T Hsource tr).
    rewrite (srealizes_obs_iff target_segs _ T Htarget tr).
    reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac chain_mst_sp :=
  first [ (eapply srz_msteps; [ sym_halted | sym_no_lazy | | ])
        | chain_mst ].

(* [comment removed for export] *)
Lemma chain_mst_srealizes : forall segs ms ms' model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  srealizes segs (mkCfg ms' model) T ->
  srealizes segs (mkCfg ms model) T.
Proof.
  intros segs ms ms' model T Hh Hlazy Hms Hr.
  chain_mst_sp; [exact Hms | exact Hr].
Qed.

Lemma chain_mst_srealizes_mmap : forall segs ms ms' model a n T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  srealizes segs (mkCfg ms' (MmapSim.mmap_model a n model)) T ->
  srealizes segs (mkCfg ms (MmapSim.mmap_model a n model)) T.
Proof.
  intros segs ms ms' model a n T Hh Hlazy Hms Hr.
  chain_mst_sp; [exact Hms | exact Hr].
Qed.
