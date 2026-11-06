(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg Nodes StoreOk AgentLib AgentNodes SpecConsts ModelAmb RefNodes ExistsRun
  Hoare WalkTac LibWritev RefNodesC RefNodesEx RefNodesG SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX PhaseG.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cfg Require ShapeAlgBase ShapeCfg NodesCfg NodesCfgChk LedgerCfg AllocCfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Definition CFG : SpuriousCfg := mkSpuriousCfg false true true true true true.

Lemma CFG_fam_off : forall no : Z, no <> 214%Z -> no <> 216%Z -> no <> 222%Z -> no <> 226%Z ->
  NodesCfg.sysno_family_off CFG no = false.
Proof. exact NodesCfg.sysno_family_off_alloc_only_false. Qed.

Section C.
  Variable segs : list Segment.

  (* [comment removed for export] *)
  Definition realizes (c : config) (T : TSet) : Prop := ShapeCfg.realizes_cfg CFG segs c T.
  Definition node_ok (c : config) (I : Type) (evs : I -> list event) (nx : I -> config) : Prop :=
    ShapeCfg.node_ok_cfg CFG segs c I evs nx.
  Definition reach (c c' : config) : Prop := star_cfg segs CFG c [] c'.

  (* [comment removed for export] *)
  Lemma node_lift_instr : forall ms model (I : Type) evs nx,
    ms_svc_pending ms = None -> ShapeAlg.node_ok segs (mkCfg ms model) I evs nx -> node_ok (mkCfg ms model) I evs nx.
  Proof. intros. apply NodesCfg.node_ok_cfg_of_plain_instr; assumption. Qed.

  Lemma node_lift_det : forall ms model evs nx,
    ShapeAlg.node_ok segs (mkCfg ms model) unit evs nx -> node_ok (mkCfg ms model) unit evs nx.
  Proof. intros. apply NodesCfg.node_ok_cfg_of_plain_det; assumption. Qed.

  Lemma node_lift_sysno : forall ms model x8 (I : Type) evs nx,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 <> 214%Z -> bv_unsigned x8 <> 216%Z -> bv_unsigned x8 <> 222%Z -> bv_unsigned x8 <> 226%Z ->
    ShapeAlg.node_ok segs (mkCfg ms model) I evs nx -> node_ok (mkCfg ms model) I evs nx.
  Proof.
    intros ms model x8 I evs nx Hsvc H1 H2 H3 H4 Hn.
    apply (NodesCfg.node_ok_cfg_of_plain_sysno CFG segs ms model x8); [exact Hsvc | apply CFG_fam_off; assumption | exact Hn].
  Qed.

  (* [comment removed for export] *)
  Lemma reach_refl : forall c, reach c c.
  Proof. intros c. apply star_cfg_refl. Qed.

  Lemma reach_trans : forall c1 c2 c3, reach c1 c2 -> reach c2 c3 -> reach c1 c3.
  Proof. intros c1 c2 c3 H1 H2. unfold reach. rewrite <- (app_nil_r []). eapply ShapeCfg.star_cfg_trans; eassumption. Qed.

  Lemma reach_step : forall c c', sstep_cfg segs CFG c [] (SNext c') -> reach c c'.
  Proof. intros c c' H. apply ShapeCfg.star_cfg_one. exact H. Qed.

  Lemma reach_node : forall c (I : Type) (nx : I -> config) (i : I), node_ok c I (fun _ => []) nx -> reach c (nx i).
  Proof. intros c I nx i Hn. apply reach_step. exact (proj1 Hn i). Qed.

  Lemma reach_instr : forall ms model ms',
    m_halted model = None -> m_vm_lazy model = [] -> ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' -> reach (mkCfg ms model) (mkCfg ms' model).
  Proof.
    intros ms model ms' Hh Hlazy Hsvc Hstep.
    exact (reach_node _ unit (fun _ => mkCfg ms' model) tt (NodesCfg.node_instr_cfg_no_lazy CFG segs ms model ms' Hh Hlazy Hsvc Hstep)).
  Qed.

  Lemma reach_msteps : forall ms ms' model,
    m_halted model = None -> m_vm_lazy model = [] -> msteps segs ms ms' -> reach (mkCfg ms model) (mkCfg ms' model).
  Proof.
    intros ms ms' model Hh Hlazy Hms. induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH].
    - apply reach_refl.
    - eapply reach_trans; [eapply reach_instr; eassumption | exact IH].
  Qed.

  (* [comment removed for export] *)
  Lemma rz_conseq : forall c T T', realizes c T -> t_eq T T' -> realizes c T'.
  Proof. intros c T T' H E. exact (ShapeCfg.rzc_eq CFG segs c T T' E H). Qed.

  Lemma rz_silent1 : forall c c' T, node_ok c unit (fun _ => []) (fun _ => c') -> realizes c' T -> realizes c T.
  Proof. intros. eapply ShapeCfg.rzc_silent1; eassumption. Qed.

  Lemma rz_emit1 : forall c c' e T, node_ok c unit (fun _ => e) (fun _ => c') -> realizes c' T -> realizes c (t_emit e T).
  Proof. intros. eapply ShapeCfg.rzc_emit1; eassumption. Qed.

  Lemma rz_cases : forall c (I : Type) (nx : I -> config) (T : I -> TSet) (i0 : I),
    node_ok c I (fun _ => []) nx -> (forall i, realizes (nx i) (T i)) -> realizes c (t_alt T).
  Proof. intros c I nx T i0 Hn HT. exact (ShapeCfg.rzc_cases CFG segs c I nx T i0 Hn HT). Qed.

  Lemma rz_alt2 : forall c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet) (a0 : IA) (b0 : IB),
    node_ok c (IA + IB) (fun _ => []) nx ->
    (forall i, realizes (nx (inl i)) A) -> (forall i, realizes (nx (inr i)) B) -> realizes c (t_alt2 A B).
  Proof. intros c IA IB nx A B a0 b0 Hn HA HB. exact (ShapeCfg.rzc_alt2 CFG segs c IA IB nx A B a0 b0 Hn HA HB). Qed.

  Lemma rz_step : forall ms model ms' T,
    m_halted model = None -> m_vm_lazy model = [] -> ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' -> realizes (mkCfg ms' model) T -> realizes (mkCfg ms model) T.
  Proof. intros ms model ms' T Hh Hl Hs Hst H. exact (NodesCfg.rzc_step_no_lazy CFG segs ms model ms' T Hh Hl Hs Hst H). Qed.

  Lemma rz_msteps : forall ms ms' model T,
    m_halted model = None -> m_vm_lazy model = [] -> msteps segs ms ms' ->
    realizes (mkCfg ms' model) T -> realizes (mkCfg ms model) T.
  Proof.
    intros ms ms' model T Hh Hlazy Hms; induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH]; intro Hc; [exact Hc|].
    eapply rz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep | apply IH; exact Hc].
  Qed.

  (* [comment removed for export] *)
  Definition GG (mode : bool) (Q : config -> Prop) (T : TSet) (c : config) : Prop :=
    if mode then realizes c T else exists c', reach c c' /\ Q c'.

  Lemma gg_true : forall Q T c, GG true Q T c <-> realizes c T.
  Proof. intros. unfold GG. tauto. Qed.
  Lemma gg_false : forall Q T c, GG false Q T c <-> exists c', reach c c' /\ Q c'.
  Proof. intros. unfold GG. tauto. Qed.
  Lemma gg_of_rz : forall Q T c, realizes c T -> GG true Q T c.
  Proof. intros Q T c H. exact H. Qed.
  Lemma rz_of_gg : forall Q T c, GG true Q T c -> realizes c T.
  Proof. intros Q T c H. exact H. Qed.
  Lemma gg_here : forall Q T c, Q c -> GG false Q T c.
  Proof. intros Q T c H. exists c. split; [apply reach_refl | exact H]. Qed.
  Lemma gg_here_mode : forall mode Q T c, mode = false -> Q c -> GG mode Q T c.
  Proof. intros mode Q T c -> H. apply gg_here. exact H. Qed.
  Lemma gg_shape_any : forall Q T T' c, GG false Q T c -> GG false Q T' c.
  Proof. intros Q T T' c H. exact H. Qed.
  Lemma gg_reach : forall Q T c c', reach c c' -> GG false Q T c' -> GG false Q T c.
  Proof. intros Q T c c' Hr (c'' & Hr' & HQ). exists c''. split; [eapply reach_trans; eassumption | exact HQ]. Qed.
  Lemma gg_mono : forall mode (Q Q' : config -> Prop) T c,
    (forall c', Q c' -> Q' c') -> GG mode Q T c -> GG mode Q' T c.
  Proof. intros [|] Q Q' T c HQ H; [exact H|]. destruct H as (c' & Hr & Hq). exists c'. split; [exact Hr | apply HQ; exact Hq]. Qed.
  Lemma gg_conseq : forall mode Q T T' c, GG mode Q T c -> t_eq T T' -> GG mode Q T' c.
  Proof. intros [|] Q T T' c H E; [eapply rz_conseq; eassumption | exact H]. Qed.

  Lemma gg_silent1 : forall mode Q T c c',
    node_ok c unit (fun _ => []) (fun _ => c') -> GG mode Q T c' -> GG mode Q T c.
  Proof.
    intros [|] Q T c c' Hnode H.
    - exact (rz_silent1 c c' T Hnode H).
    - eapply gg_reach; [| exact H]. exact (reach_node c unit (fun _ => c') tt Hnode).
  Qed.

  Lemma gg_alt2 : forall mode Q c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet) (a0 : IA) (b0 : IB),
    node_ok c (IA + IB) (fun _ => []) nx ->
    (mode = true -> forall i, realizes (nx (inl i)) A) ->
    (forall i, GG mode Q B (nx (inr i))) ->
    GG mode Q (t_alt2 A B) c.
  Proof.
    intros [|] Q c IA IB nx A B a0 b0 Hnode HA HB.
    - exact (rz_alt2 c IA IB nx A B a0 b0 Hnode (HA eq_refl) HB).
    - eapply gg_reach; [| exact (HB b0)]. exact (reach_node c _ nx (inr b0) Hnode).
  Qed.

  Lemma gg_cases : forall mode Q c (I : Type) (nx : I -> config) (T : I -> TSet) (i0 : I),
    node_ok c I (fun _ => []) nx ->
    (mode = true -> forall i, realizes (nx i) (T i)) ->
    GG mode Q (T i0) (nx i0) ->
    GG mode Q (t_alt T) c.
  Proof.
    intros [|] Q c I nx T i0 Hnode HA HB.
    - exact (rz_cases c I nx T i0 Hnode (HA eq_refl)).
    - eapply gg_reach; [| exact HB]. exact (reach_node c I nx i0 Hnode).
  Qed.

  (* [comment removed for export] *)
  Lemma gg_all : forall mode Q c (I : Type) (nx : I -> config) (T : TSet) (i0 : I),
    node_ok c I (fun _ => []) nx -> (forall i, GG mode Q T (nx i)) -> GG mode Q T c.
  Proof.
    intros [|] Q c I nx T i0 Hnode HB.
    - exact (ShapeCfg.rzc_cases_same CFG segs c I nx T i0 Hnode HB).
    - eapply gg_reach; [| exact (HB i0)]. exact (reach_node c I nx i0 Hnode).
  Qed.

  Lemma gg_step : forall mode Q ms model ms' T,
    m_halted model = None -> m_vm_lazy model = [] -> ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    GG mode Q T (mkCfg ms' model) -> GG mode Q T (mkCfg ms model).
  Proof.
    intros mode Q ms model ms' T Hh Hlazy Hsvc Hstep H.
    eapply gg_silent1; [exact (NodesCfg.node_instr_cfg_no_lazy CFG segs ms model ms' Hh Hlazy Hsvc Hstep) | exact H].
  Qed.

  Lemma gg_msteps : forall mode Q ms ms' model T,
    m_halted model = None -> m_vm_lazy model = [] -> msteps segs ms ms' ->
    GG mode Q T (mkCfg ms' model) -> GG mode Q T (mkCfg ms model).
  Proof.
    intros mode Q ms ms' model T Hh Hlazy Hms;
      induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH]; intro Hc; [exact Hc|].
    eapply gg_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep | apply IH; exact Hc].
  Qed.

  Lemma gg_sys : forall mode Q regs pc mem rom model w T,
    m_halted model = None -> m_vm_lazy model = [] ->
    fetch_word segs pc = Some w -> is_ecall w = true ->
    GG mode Q T (mkCfg (epend regs pc mem rom (getr regs 17)) model) ->
    GG mode Q T (mkCfg (mkst regs pc mem rom) model).
  Proof.
    intros mode Q regs pc mem rom model w T Hh Hlazy HF HE Hc.
    eapply gg_step; [exact Hh | exact Hlazy | reflexivity | eapply step_ecall_epend; eassumption | exact Hc].
  Qed.

  Lemma rz_sys : forall regs pc mem rom model w T,
    m_halted model = None -> m_vm_lazy model = [] ->
    fetch_word segs pc = Some w -> is_ecall w = true ->
    realizes (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
    realizes (mkCfg (mkst regs pc mem rom) model) T.
  Proof. intros regs pc mem rom model w T Hh Hlazy HF HE Hc. exact (gg_sys true (fun _ => True) regs pc mem rom model w T Hh Hlazy HF HE Hc). Qed.

  (* [comment removed for export] *)
  Lemma gg_det : forall mode Q ms model x8 eff0 m0 T,
    m_halted model = None -> ms_svc_pending ms = Some x8 ->
    (forall eff m' evs, check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <-> (eff = eff0 /\ m' = m0 /\ evs = [])) ->
    (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
    m_halted m0 = None -> m_vm_lazy m0 = [] ->
    GG mode Q T (mkCfg (advance_past_svc (apply_effect ms eff0)) m0) ->
    GG mode Q T (mkCfg ms model).
  Proof.
    intros mode Q ms model x8 eff0 m0 T Hh Hsvc Hchk Hnu Hh0 Hlazy0 Hc.
    eapply gg_silent1; [apply node_lift_det; eapply Nodes.node_det; eassumption | exact Hc].
  Qed.

  Lemma gg_ret_only_silent : forall mode Q ms model x8 r m' T,
    m_halted model = None -> ms_svc_pending ms = Some x8 ->
    (forall eff, check_syscall (sys_input segs ms x8) eff model = check_ret_only eff r m' []) ->
    m_halted m' = None -> m_vm_lazy m' = [] ->
    GG mode Q T (mkCfg (advance_past_svc (set_gpr0 ms r)) m') -> GG mode Q T (mkCfg ms model).
  Proof.
    intros mode Q ms model x8 r m' T Hh Hsvc Hchk Hh' Hlazy Hc.
    eapply gg_silent1; [apply node_lift_det; eapply Nodes.node_ret_only; eassumption | exact Hc].
  Qed.

  Lemma gg_ret_only_copyins_silent : forall mode Q ms model x8 reads r m' T,
    m_halted model = None -> ms_svc_pending ms = Some x8 ->
    (forall eff, check_syscall (sys_input segs ms x8) eff model = check_ret_only_copyins reads eff r m' []) ->
    m_halted m' = None -> m_vm_lazy m' = [] ->
    GG mode Q T (mkCfg (advance_past_svc (set_gpr0 ms r)) m') -> GG mode Q T (mkCfg ms model).
  Proof.
    intros mode Q ms model x8 reads r m' T Hh Hsvc Hchk Hh' Hlazy Hc.
    eapply gg_silent1; [apply node_lift_det; eapply Nodes.node_ret_only_copyins; eassumption | exact Hc].
  Qed.
End C.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rz_wall : forall segs c (ch : word) (bs : list byte) (K : TSet),
  (1 <= length bs)%nat -> K [] ->
  realizes segs c (t_alt (fun i : wr_index bs =>
     t_emit (map (WriteEv ch) (firstn (proj1_sig i) bs))
            (t_emit (map (WriteEv ch) (skipn (proj1_sig i) bs)) K))) ->
  realizes segs c (t_emit (map (WriteEv ch) bs) K).
Proof.
  intros segs c ch bs K Hnb HK H. eapply rz_conseq; [exact H | apply t_alt_wall; assumption].
Qed.


(* [comment removed for export] *)
Section G_Nodes.
  Variable segs : list Segment.

Lemma node_ret_only : forall ms model x8 r m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = check_ret_only eff r m' evs) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  node_ok segs (mkCfg ms model) unit (fun _ => evs)
          (fun _ => mkCfg (advance_past_svc (set_gpr0 ms r)) m').
Proof.
  intros ms model x8 r m' evs Hh Hsvc Hchk Hh' Hlazy. apply node_lift_det. exact (Nodes.node_ret_only segs ms model x8 r m' evs Hh Hsvc Hchk Hh' Hlazy).
Qed.


Lemma node_ret_only_copyins : forall ms model x8 reads r m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_ret_only_copyins reads eff r m' evs) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  node_ok segs (mkCfg ms model) unit (fun _ => evs)
          (fun _ => mkCfg (advance_past_svc (set_gpr0 ms r)) m').
Proof.
  intros ms model x8 reads r m' evs Hh Hsvc Hchk Hh' Hlazy. apply node_lift_det. exact (Nodes.node_ret_only_copyins segs ms model x8 reads r m' evs Hh Hsvc Hchk Hh' Hlazy).
Qed.


Lemma node_det : forall ms model x8 eff0 m0 evs0,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = eff0 /\ m' = m0 /\ evs = evs0)) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  m_halted m0 = None ->
  m_vm_lazy m0 = [] ->
  node_ok segs (mkCfg ms model) unit (fun _ => evs0)
          (fun _ => mkCfg (advance_past_svc (apply_effect ms eff0)) m0).
Proof.
  intros ms model x8 eff0 m0 evs0 Hh Hsvc Hchk Hnu Hh0 Hlazy0. apply node_lift_det. exact (Nodes.node_det segs ms model x8 eff0 m0 evs0 Hh Hsvc Hchk Hnu Hh0 Hlazy0).
Qed.


Lemma node_open : forall ms model x8 reads (mk : word -> Model),
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 56%Z ->   (* [comment removed for export] *)
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_open_result_copyins reads eff model mk) ->
  (forall fd, m_halted (mk fd) = None) ->
  (forall fd, m_vm_lazy (mk fd) = []) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  node_ok segs (mkCfg ms model) (open_I model) (fun _ => []) (open_nx ms model mk).
Proof.
  intros ms model x8 reads mk Hh Hlazy Hsvc Hno Hchk Hmk Hmkl Hfree.
  apply (node_lift_sysno segs ms model x8); [exact Hsvc | rewrite Hno; lia | rewrite Hno; lia | rewrite Hno; lia | rewrite Hno; lia |].
  exact (Nodes.node_open segs ms model x8 reads mk Hh Hlazy Hsvc Hchk Hmk Hmkl Hfree).
Qed.


Lemma rz_ret_only : forall ms model x8 r m' evs T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = check_ret_only eff r m' evs) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  realizes segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  realizes segs (mkCfg ms model) (t_emit evs T).
Proof.
  intros ms model x8 r m' evs T Hh Hsvc Hchk Hh' Hlazy Hc.
  eapply rz_emit1; [eapply node_ret_only; eassumption | exact Hc].
Qed.

Lemma rz_ret_only_copyins : forall ms model x8 reads r m' evs T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_ret_only_copyins reads eff r m' evs) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  realizes segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  realizes segs (mkCfg ms model) (t_emit evs T).
Proof.
  intros ms model x8 reads r m' evs T Hh Hsvc Hchk Hh' Hlazy Hc.
  eapply rz_emit1; [eapply node_ret_only_copyins; eassumption | exact Hc].
Qed.

Lemma rz_ret_only_silent : forall ms model x8 r m' T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = check_ret_only eff r m' []) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  realizes segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 r m' T Hh Hsvc Hchk Hh' Hlazy Hc.
  eapply rz_silent1; [eapply node_ret_only; eassumption | exact Hc].
Qed.

Lemma rz_ret_only_copyins_silent : forall ms model x8 reads r m' T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_ret_only_copyins reads eff r m' []) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  realizes segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 reads r m' T Hh Hsvc Hchk Hh' Hlazy Hc.
  eapply rz_silent1; [eapply node_ret_only_copyins; eassumption | exact Hc].
Qed.

Lemma rz_det : forall ms model x8 eff0 m0 T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = eff0 /\ m' = m0 /\ evs = [])) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  m_halted m0 = None ->
  m_vm_lazy m0 = [] ->
  realizes segs (mkCfg (advance_past_svc (apply_effect ms eff0)) m0) T ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 eff0 m0 T Hh Hsvc Hchk Hnu Hh0 Hlazy0 Hc.
  eapply rz_silent1; [eapply node_det; eassumption | exact Hc].
Qed.

Lemma rz_open : forall ms model x8 reads (mk : word -> Model) A B,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 56%Z ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_open_result_copyins reads eff model mk) ->
  (forall fd, m_halted (mk fd) = None) ->
  (forall fd, m_vm_lazy (mk fd) = []) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  (forall e, In e openat_errnos ->
     realizes segs (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) A) ->
  realizes segs (mkCfg (advance_past_svc (set_gpr0 ms (alloc_fd (m_fds model))))
                       (mk (alloc_fd (m_fds model)))) B ->
  realizes segs (mkCfg ms model) (t_alt2 A B).
Proof.
  intros ms model x8 reads mk A B Hh Hlazy Hsvc Hno Hchk Hmk Hmklazy Hfree HA HB.
  apply (rz_alt2 segs (mkCfg ms model) {e : Z | In e openat_errnos} unit
           (open_nx ms model mk) A B (exist _ ENOMEM ENOMEM_in_openat_errnos) tt).
  - eapply node_open; eassumption.
  - intros [e He]. cbn [open_nx]. apply HA. exact He.
  - intros []. cbn [open_nx]. exact HB.
Qed.

Lemma realizes_nonempty : forall c T, realizes segs c T -> T [].
Proof. intros c T H. exact (ShapeCfg.realizes_cfg_nonempty CFG segs c T H). Qed.

Lemma rz_exit : forall ms model x8,
  m_halted model = None -> ms_svc_pending ms = Some x8 -> is_exit_no x8 ->
  realizes segs (mkCfg ms model) (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof. intros ms model x8 Hh Hsvc Hx. exact (NodesCfg.rzc_exit CFG segs ms model x8 Hh Hsvc Hx). Qed.


End G_Nodes.

(* [comment removed for export] *)
Section G_RefNodesC.
  Variable segs : list Segment.

Lemma rz_exit_at : forall regs (pc : word) mem rom model w code,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = code ->
  realizes segs (mkCfg (mkst regs pc mem rom) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs pc mem rom model w code HF HE Hh Hlazy H17 H10.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  rewrite <- H10, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
  eapply rz_exit; [exact Hh | reflexivity |].
  destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.

Lemma rz_exit_at_lit : forall regs (pc : word) mem rom model w (code : Z),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = Z_to_bv 64 code -> (0 <= code < 256)%Z ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) (t_exit (Z_to_bv 64 code) (m_fs model)).
Proof.
  intros regs pc mem rom model w code HF HE Hh Hlazy H17 H10 Hc.
  rewrite <- (bv_and_255_small code Hc). eapply rz_exit_at; eassumption.
Qed.

End G_RefNodesC.

(* [comment removed for export] *)
Section G_RefNodes.
  Variable segs : list Segment.

Lemma node_set_tid : forall ms model x8,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 96%Z ->
  m_tid model = None ->
  node_ok segs (mkCfg ms model) tid_I (fun _ => [])
    (fun i => mkCfg (advance_past_svc (set_gpr0 ms (proj1_sig i))) (with_tid (proj1_sig i) model)).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno Htid.
  apply (node_lift_sysno segs ms model x8); [exact Hsvc | rewrite Hno; lia | rewrite Hno; lia | rewrite Hno; lia | rewrite Hno; lia |].
  exact (RefNodes.node_set_tid segs ms model x8 Hh Hlazy Hsvc Hno Htid).
Qed.


Lemma rz_set_tid : forall regs (pc : word) mem rom model K w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 96 ->
  m_tid model = None ->
  (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     realizes segs (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model)) K) ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model K w HF HE Hh Hlazy H17 Htid Hk.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  apply (rz_conseq segs _ (t_alt (fun _ : tid_I => K)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ (Z_to_bv 64 1) one_tid_ok); exact Ht]].
  eapply rz_cases; [exact (exist _ (Z_to_bv 64 1) one_tid_ok)
                   | eapply node_set_tid; [exact Hh | exact Hlazy | reflexivity | rewrite H17; apply u64_lit; lia | exact Htid] |].
  intros [t Ht]. cbn [proj1_sig]. rewrite adv_set_epend. apply Hk. exact Ht.
Qed.

Lemma rz_close : forall regs (pc : word) mem model w fd e K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 57 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some e ->
  realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem (seg_rom segs))
                       (with_fds (fd_remove (m_fds model) fd) model)) K ->
  realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd e K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hc.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  eapply rz_ret_only_silent; [exact Hh | reflexivity | | | | rewrite adv_set_epend; exact Hc].
  - intros eff. rewrite (check_syscall_57 segs) by (rewrite H17; apply u64_lit; lia).
    unfold check_close. rewrite ms_gpr_epend0, Hfd, (fd32_id fd Hfd32), Hlk. reflexivity.
  - rewrite with_fds_halted'. exact Hh.
  - rewrite with_fds_lazy. exact Hlazy.
Qed.

Lemma rz_read_file : forall regs (pc : word) mem model w fd p off data (cnt : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some (FdFile p off) ->
  fs_lookup (m_fs model) p = Some data ->
  getr regs 12 = Z_to_bv 64 cnt ->
  (1 <= cnt)%Z -> (cnt <= rw_bytes_max)%Z -> (cnt < 2 ^ 64)%Z ->
  store_ok segs mem (getr regs 11) (Z.to_nat cnt) = true ->
  access_okb (getr regs 11) cnt = true ->
  let bs := file_read data off (getr regs 12) in
  realizes segs (mkCfg (mkst (regupd regs 10 (len_word bs)) (v_addi pc 4)
                              (wbytes mem (getr regs 11) bs) (seg_rom segs))
                       (with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model)) K ->
  realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd p off data cnt K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hfs H12 Hc1 Hmax H64 Hok Haok bs Hc.
  assert (Hno : bv_unsigned (getr regs 17) = 63%Z) by (rewrite H17; apply u64_lit; lia).
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  destruct (read_bytes_map_of_store_ok segs mem (getr regs 11) (Z.to_nat cnt) Hok ltac:(lia)) as [wv Hw].
  rewrite Z2Nat.id in Hw by lia.
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hu2 : bv_unsigned (ms_gpr ms 2) = cnt).
  { unfold ms. rewrite ms_gpr_epend2, H12. apply u64_lit. lia. }
  destruct (read_file_check segs ms (getr regs 17) model fd p off data wv Hno
              ltac:(unfold ms; rewrite ms_gpr_epend0; exact Hfd) Hfd32 Hlk Hfs
              ltac:(unfold ms; rewrite ms_writable_byte_epend, ms_gpr_epend1, ms_gpr_epend2, H12; exact Hw)
              ltac:(rewrite Hu2; lia) ltac:(rewrite Hu2; exact Hmax)
              ltac:(fold ms; rewrite Hu2; unfold ms; rewrite ms_gpr_epend1; exact Haok)) as [Hchk Hnu].
  unfold ms in Hchk, Hnu. rewrite ms_gpr_epend1, ms_gpr_epend2 in Hchk.
  subst bs. revert Hc Hchk.
  generalize (file_read data off (getr regs 12)) as bs. intros bs Hc Hchk.
  eapply (rz_det segs _ model _ (mkEffect (len_word bs) (delivered_writes (getr regs 11) bs) [])
            (with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model));
    [exact Hh | reflexivity | exact Hchk | exact Hnu
    | rewrite with_fds_halted'; exact Hh | rewrite with_fds_lazy; exact Hlazy | ].
  destruct bs as [|b bsr]; cbn [delivered_writes].
  - unfold ms. rewrite adv_ret_epend. cbn [wbytes] in Hc. exact Hc.
  - unfold ms. rewrite adv_write1_epend. exact Hc.
Qed.

Lemma rz_read_dir : forall regs (pc : word) mem model w fd K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some FdDir ->
  access_okb (getr regs 11) (bv_unsigned (getr regs 12)) = true ->
  realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem (seg_rom segs)) model) K ->
  realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hdir Hc.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  eapply rz_ret_only_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
  intros eff. rewrite (check_syscall_63 segs _ _ eff model) by (rewrite H17; apply u64_lit; lia).
  unfold check_read. rewrite ms_gpr_epend0, ms_gpr_epend1, ms_gpr_epend2, Hfd, (fd32_id fd Hfd32), Hlk.
  rewrite Hdir. reflexivity.
Qed.

Section Openat.
  Variables (regs : bvmap 5 word) (pc : word) (mem : word -> option byte) (model : Model).
  Variable w : bv 32.
  Hypothesis HF : fetch_word segs pc = Some w.
  Hypothesis HE : is_ecall w = true.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis H17 : getr regs 17 = Z_to_bv 64 56.
  Hypothesis H10 : getr regs 10 = AT_FDCWD.
  (* [comment removed for export] *)
  Hypothesis Hfl : Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z.

  Let ms := epend regs pc mem (seg_rom segs) (getr regs 17).
  Let post (r : word) := mkst (regupd regs 10 r) (v_addi pc 4) mem (seg_rom segs).
  Let fds := m_fds model.

  Lemma Hno56 : bv_unsigned (getr regs 17) = 56%Z.
  Proof. rewrite H17. apply u64_lit. lia. Qed.

  (* [comment removed for export] *)
  Lemma openat_check_head : forall eff,
    check_syscall (sys_input segs ms (getr regs 17)) eff model
    = Prelude.check_copyins_after (open_copyins ms) eff
      match read_cstr (mrb segs mem) (getr regs 11) with
      | CstrTooLong => check_ret_only (clear_copyins eff) (errno_ret ENAMETOOLONG) model []
      | CstrFault => check_ret_only (clear_copyins eff) (errno_ret EFAULT) model []
      | CstrOk p =>
          if path_eqb p [] then check_ret_only (clear_copyins eff) (errno_ret ENOENT) model []
          else if path_has_slash p then Open.check_openat_sep p (getr regs 12) (clear_copyins eff) model
          else if path_is_dirref p then
                 check_open_result (clear_copyins eff) model (fun fd => with_fds (fd_insert (m_fds model) fd FdDir) model)
               else match fs_lookup (m_fs model) p with
                    | None => check_ret_only (clear_copyins eff) (errno_ret ENOENT) model []
                    | Some _ => check_open_result (clear_copyins eff) model
                                  (fun fd => with_fds (fd_insert (m_fds model) fd (FdFile p (Z_to_bv 64 0))) model)
                    end
      end.
  Proof.
    intros eff. cbv delta [ms].
    rewrite (check_syscall_56 segs _ _ eff model Hno56). unfold check_openat.
    rewrite ms_gpr_epend0, ms_gpr_epend1, ms_gpr_epend2.
    rewrite (modeled_open_flags_rd _ Hfl). cbn [negb]. cbv beta iota zeta.
    unfold Open.check_openat_body. rewrite in_mem_si, ms_read_byte_epend.
    unfold open_copyins. rewrite ms_read_byte_epend, ms_gpr_epend1.
    destruct (read_cstr (mrb segs mem) (getr regs 11)) as [p| |]; [|reflexivity|reflexivity].
    destruct (path_eqb p []); [reflexivity|].
    rewrite H10. norm_fd32. rewrite bv_eqb_refl. cbn [negb]. cbv beta iota.
    unfold Open.check_openat_resolved.
    destruct (path_has_slash p); [reflexivity|].
    rewrite Hfl. cbn [Z.eqb]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma rz_openat_toolong : forall bs K,
    rdn segs mem (getr regs 11) 4096 = Some bs -> ~ In (Z_to_bv 8 0) bs ->
    realizes segs (mkCfg (post (errno_ret ENAMETOOLONG)) model) K ->
    realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
  Proof.
    intros bs K Hrd Hnz Hc. cbv delta [post] in *.
    pose proof (read_cstr_toolong_of_rdn segs mem (getr regs 11) bs (rdn_length _ _ _ _ _ Hrd) Hnz Hrd) as Hp.
    eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply rz_ret_only_copyins_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
    intros eff. fold ms. rewrite openat_check_head, Hp. apply check_copyins_after_ret_only.
  Qed.

  (* [comment removed for export] *)
  Definition path_at (p : list byte) : Prop :=
    (length p <= 4095)%nat /\ ~ In (Z_to_bv 8 0) p
    /\ rdn segs mem (getr regs 11) (length p + 1) = Some (p ++ [Z_to_bv 8 0]).

  Lemma path_at_cstr : forall p, path_at p -> read_cstr (mrb segs mem) (getr regs 11) = CstrOk p.
  Proof. intros p (H1 & H2 & H3). apply read_cstr_of_rdn; assumption. Qed.

  (* [comment removed for export] *)
  Lemma rz_openat_empty : forall K,
    path_at [] ->
    realizes segs (mkCfg (post (errno_ret ENOENT)) model) K ->
    realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
  Proof.
    intros K Hp Hc. cbv delta [post] in *.
    eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply rz_ret_only_copyins_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
    intros eff. fold ms. rewrite openat_check_head, (path_at_cstr [] Hp). apply check_copyins_after_ret_only.
  Qed.

  (* [comment removed for export] *)
  Lemma rz_openat_absent : forall p K,
    path_at p -> p <> [] -> path_has_slash p = false -> path_is_dirref p = false ->
    fs_lookup (m_fs model) p = None ->
    realizes segs (mkCfg (post (errno_ret ENOENT)) model) K ->
    realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
  Proof.
    intros p K Hp Hne Hns Hnd Hfs Hc. cbv delta [post] in *.
    eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply rz_ret_only_copyins_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
    intros eff. fold ms. rewrite openat_check_head, (path_at_cstr p Hp).
    rewrite (path_eqb_neq _ _ Hne), Hns, Hnd, Hfs. apply check_copyins_after_ret_only.
  Qed.

  Hypothesis Hfree : fd_lookup fds (alloc_fd fds) = None.

  (* [comment removed for export] *)
  Lemma rz_openat_dirref : forall p KA KB,
    path_at p -> path_is_dirref p = true ->
    (forall e, In e openat_errnos -> realizes segs (mkCfg (post (errno_ret e)) model) KA) ->
    realizes segs (mkCfg (post (alloc_fd fds)) (with_fds (fd_insert fds (alloc_fd fds) FdDir) model)) KB ->
    realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt2 KA KB).
  Proof.
    intros p KA KB Hp Hd HA HB. cbv delta [post] in *.
    assert (Hne : path_eqb p [] = false).
    { destruct p; [|reflexivity]. cbv in Hd. discriminate Hd. }
    eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply rz_open; [exact Hh | exact Hlazy | reflexivity | exact Hno56 | | | | exact Hfree | |].
    - intros eff. fold ms. rewrite openat_check_head, (path_at_cstr _ Hp).
      rewrite Hne, (path_is_dirref_no_slash _ Hd), Hd. apply check_copyins_after_open_result.
    - intros fd. cbv beta delta [fds]. rewrite with_fds_halted'. exact Hh.
    - intros fd. cbv beta delta [fds]. rewrite with_fds_lazy. exact Hlazy.
    - intros e He. rewrite adv_set_epend. apply HA. exact He.
    - rewrite adv_set_epend. exact HB.
  Qed.

  (* [comment removed for export] *)
  Lemma rz_openat_dot : forall KA KB,
    path_at dot_path ->
    (forall e, In e openat_errnos -> realizes segs (mkCfg (post (errno_ret e)) model) KA) ->
    realizes segs (mkCfg (post (alloc_fd fds)) (with_fds (fd_insert fds (alloc_fd fds) FdDir) model)) KB ->
    realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt2 KA KB).
  Proof. intros KA KB Hp HA HB. exact (rz_openat_dirref dot_path KA KB Hp eq_refl HA HB). Qed.

  (* [comment removed for export] *)
  Lemma rz_openat_file : forall p d KA KB,
    path_at p -> p <> [] -> path_has_slash p = false -> path_is_dirref p = false ->
    fs_lookup (m_fs model) p = Some d ->
    (forall e, In e openat_errnos -> realizes segs (mkCfg (post (errno_ret e)) model) KA) ->
    realizes segs (mkCfg (post (alloc_fd fds))
                         (with_fds (fd_insert fds (alloc_fd fds) (FdFile p (Z_to_bv 64 0))) model)) KB ->
    realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt2 KA KB).
  Proof.
    intros p d KA KB Hp Hne Hns Hnd Hfs HA HB. cbv delta [post] in *.
    eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply rz_open; [exact Hh | exact Hlazy | reflexivity | exact Hno56 | | | | exact Hfree | |].
    - intros eff. fold ms. rewrite openat_check_head, (path_at_cstr p Hp).
      rewrite (path_eqb_neq _ _ Hne), Hns, Hnd, Hfs. apply check_copyins_after_open_result.
    - intros fd. cbv beta delta [fds]. rewrite with_fds_halted'. exact Hh.
    - intros fd. cbv beta delta [fds]. rewrite with_fds_lazy. exact Hlazy.
    - intros e He. rewrite adv_set_epend. apply HA. exact He.
    - rewrite adv_set_epend. exact HB.
  Qed.
End Openat.

End G_RefNodes.

(* [comment removed for export] *)
Section G_RefNodesEx.
  Variable segs : list Segment.

Lemma reach_ecall : forall regs pc mem rom model w,
  m_halted model = None -> m_vm_lazy model = [] ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  reach segs (mkCfg (mkst regs pc mem rom) model) (mkCfg (epend regs pc mem rom (getr regs 17)) model).
Proof.
  intros regs pc mem rom model w Hh Hlazy HF HE.
  eapply reach_instr; [exact Hh | exact Hlazy | reflexivity | eapply step_ecall_epend; eassumption].
Qed.

Lemma reach_of_node : forall c (I : Type) (nx : I -> config) (i : I), node_ok segs c I (fun _ => []) nx -> reach segs c (nx i).
Proof. intros c I nx i Hn. exact (reach_node segs c I nx i Hn). Qed.


Lemma reach_ecall_node : forall regs pc mem rom model w (I : Type) (nx : I -> config) (i : I),
  m_halted model = None -> m_vm_lazy model = [] ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  node_ok segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) I (fun _ => []) nx ->
  reach segs (mkCfg (mkst regs pc mem rom) model) (nx i).
Proof.
  intros regs pc mem rom model w I nx i Hh Hlazy HF HE Hn.
  eapply reach_trans; [eapply reach_ecall; eassumption | eapply reach_of_node; exact Hn].
Qed.

Lemma ex_set_tid : forall regs (pc : word) mem rom model w tid,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 96 ->
  m_tid model = None ->
  (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
  reach segs (mkCfg (mkst regs pc mem rom) model)
             (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model)).
Proof.
  intros regs pc mem rom model w tid HF HE Hh Hlazy H17 Htid Hr.
  rewrite <- (adv_set_epend regs pc mem rom (getr regs 17) tid).
  apply (reach_ecall_node regs pc mem rom model w tid_I
           (fun i => mkCfg (advance_past_svc (set_gpr0 (epend regs pc mem rom (getr regs 17)) (proj1_sig i)))
                           (with_tid (proj1_sig i) model))
           (exist _ tid Hr) Hh Hlazy HF HE).
  eapply node_set_tid; [exact Hh | exact Hlazy | reflexivity | rewrite H17; apply u64_lit; lia | exact Htid].
Qed.

Lemma ex_set_tid_1 : forall regs (pc : word) mem rom model w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 96 ->
  m_tid model = None ->
  reach segs (mkCfg (mkst regs pc mem rom) model)
             (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 1)) (v_addi pc 4) mem rom) (with_tid (Z_to_bv 64 1) model)).
Proof. intros. eapply ex_set_tid; try eassumption. apply one_tid_ok. Qed.

Lemma ex_read_dir : forall regs (pc : word) mem model w fd,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some FdDir ->
  access_okb (getr regs 11) (bv_unsigned (getr regs 12)) = true ->
  reach segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
             (mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem (seg_rom segs)) model).
Proof.
  intros regs pc mem model w fd HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hdir.
  rewrite <- (adv_set_epend regs pc mem (seg_rom segs) (getr regs 17)).
  apply (reach_ecall_node regs pc mem (seg_rom segs) model w unit
           (fun _ => mkCfg (advance_past_svc (set_gpr0 (epend regs pc mem (seg_rom segs) (getr regs 17)) (errno_ret EISDIR))) model)
           tt Hh Hlazy HF HE).
  eapply node_ret_only; [exact Hh | reflexivity | | exact Hh | exact Hlazy].
  intros eff. rewrite (check_syscall_63 segs _ _ eff model) by (rewrite H17; apply u64_lit; lia).
  unfold check_read. rewrite ms_gpr_epend0, ms_gpr_epend1, ms_gpr_epend2, Hfd, (fd32_id fd Hfd32), Hlk.
  rewrite Hdir. reflexivity.
Qed.

End G_RefNodesEx.

(* [comment removed for export] *)
Section G_LibWritev.
  Variable segs : list Segment.

Lemma rz_writev_pending : forall ms x8 model (fd : Z) (iov : word) iovs bss (T : nat -> TSet),
  ms_rom ms = seg_rom segs ->
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  bv_unsigned x8 = 66%Z ->
  ms_gpr ms 0 = Z_to_bv 64 fd ->
  ms_gpr ms 1 = iov ->
  ms_gpr ms 2 = Z_to_bv 64 (Z.of_nat (length iovs)) ->
  (1 <= length iovs <= 1024)%nat ->
  (bv_unsigned iov + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
  iov_array segs (ms_mem ms) iov iovs ->
  iov_bufs_ok iovs ->
  iov_bufs segs (ms_mem ms) iovs bss ->
  let bs := concat bss in
  (1 <= iovs_total iovs)%Z -> (iovs_total iovs <= 2 ^ 30)%Z ->
  (forall k, (1 <= k)%nat -> (k <= length bs)%nat ->
     realizes segs (mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat k)))) model) (T k)) ->
  realizes segs (mkCfg ms model)
    (t_alt (fun i : wr_index bs => t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs)) (T (proj1_sig i)))).
Proof.
  intros ms x8 model fd iov iovs bss T Hrom Hh Hlazy Hsvc Hfd Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs bs
         Ht1 Ht30 Hk.
  destruct (writev_check segs ms x8 model fd iov iovs bss Hrom Hfd Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs
              Ht1 Ht30)
    as [Hlen Hchk]. fold bs in Hlen, Hchk.
  set (tot := iovs_total iovs) in *.
  set (CA := import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs)))) in *.
  assert (Hnb : (1 <= length bs)%nat) by lia.
  pose (effs := fun i : wr_index bs =>
          mkEffectU (Z_to_bv 64 (Z.of_nat (proj1_sig i))) [] [] [] []
                    (CA ++ iov_prefix_accesses iovs (proj1_sig i))).
  assert (Enx : forall i : wr_index bs,
    mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat (proj1_sig i))))) model
    = mkCfg (advance_past_svc (apply_effect ms (effs i))) model).
  { intros [k Hk']. cbn [proj1_sig]. unfold effs. cbn [proj1_sig].
    rewrite <- (apply_effect_copyins_no_write ms (Z_to_bv 64 (Z.of_nat k)) (CA ++ iov_prefix_accesses iovs k)).
    reflexivity. }
  apply (ShapeCfg.rzc_node CFG segs (mkCfg ms model) (wr_index bs)
           (fun i => map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs))
           (fun i => mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat (proj1_sig i))))) model)
           (fun i => T (proj1_sig i)) (wr_full bs Hnb)).
  2:{ intros [k [Hk1 Hk2]]. cbn [proj1_sig]. apply Hk; assumption. }
  assert (Hku : forall k, (k <= length bs)%nat -> bv_unsigned (Z_to_bv 64 (Z.of_nat k)) = Z.of_nat k).
  { intros k Hk2. apply u64_lit. lia. }
  apply (node_lift_sysno segs ms model x8); [exact Hsvc | rewrite Hno; lia | rewrite Hno; lia | rewrite Hno; lia | rewrite Hno; lia |].
  split.
  - intros i. rewrite Enx. apply (sstep_of_check segs ms model x8); [exact Hh | exact Hsvc | | exact Hh | exact Hlazy].
    destruct i as [k [Hk1 Hk2]]. unfold effs. cbn [proj1_sig]. rewrite Hchk.
    rewrite (Hku k Hk2), Nat2Z.id.
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia.
    replace (addr_is_error_b (Z_to_bv 64 (Z.of_nat k))) with false
      by (symmetry; unfold addr_is_error_b, two_pow_64; apply Z.ltb_ge; rewrite (Hku k Hk2); lia).
    rewrite (proj2 (access_ranges_eqb_eq _ _) eq_refl). reflexivity.
  - assert (Hinv : forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
              exists i : wr_index bs, eff = effs i /\ m' = model /\ ev = map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs)).
    { intros [ret ws zs us cs ci] m' ev Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate].
      destruct ((1 <=? bv_unsigned ret)%Z && (bv_unsigned ret <=? tot)%Z && negb (addr_is_error_b ret))%bool eqn:Eb;
        [|discriminate].
      destruct (access_ranges_eqb ci (CA ++ iov_prefix_accesses iovs (Z.to_nat (bv_unsigned ret)))) eqn:Eci;
        [|discriminate].
      injection Hc as <- <-.
      apply andb_true_iff in Eb as [Eb _]. apply andb_true_iff in Eb as [E1 E2].
      apply Z.leb_le in E1. apply Z.leb_le in E2. apply access_ranges_eqb_eq in Eci.
      assert (Hkr : (1 <= Z.to_nat (bv_unsigned ret))%nat /\ (Z.to_nat (bv_unsigned ret) <= length bs)%nat) by lia.
      exists (exist _ (Z.to_nat (bv_unsigned ret)) Hkr). cbn [proj1_sig]. unfold effs. cbn [proj1_sig].
      rewrite Z2Nat.id by lia. rewrite u64_roundtrip'. subst ci. repeat split; reflexivity. }
    intros e st Hss.
    destruct (sstep_svc_inv segs ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hmat & ->) | [(Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat. injection Hmat as <-.
      exists i. rewrite Enx. split; reflexivity.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat. discriminate.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). congruence.
    + exfalso. rewrite Hchk in Hc. destruct eff as [ret ws zs us cs ci].
      destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct (_ && _)%bool; [destruct (access_ranges_eqb _ _)|]; discriminate.
Qed.

Lemma rz_writev2 : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (T : nat -> TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 2 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 16)) 8%nat = Some (word_to_le_bytes 8 b2) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 24)) 8%nat = Some (word_to_le_bytes 8 n2) ->
  rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
  rdn segs mem b2 (word_to_nat n2) = Some bs2 ->
  (bv_unsigned iov + 32 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
  (1 <= bv_unsigned n1 + bv_unsigned n2)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  (forall k, (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat ->
     realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
              (T k)) ->
  realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
    (t_alt (fun i : wr_index (bs1 ++ bs2) =>
       t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) (bs1 ++ bs2))) (T (proj1_sig i)))).
Proof.
  intros regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 T HF HE Hh Hlazy Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiok Hb1 Hb2 Ht1 Ht30 Hk.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  pose proof (u64_range n1). pose proof (u64_range n2).
  replace (bs1 ++ bs2) with (concat [bs1; bs2]) in * by (cbn; rewrite app_nil_r; reflexivity).
  eapply (rz_writev_pending (epend regs pc mem (seg_rom segs) (getr regs 17)) (getr regs 17) model fd iov
            [(b1, n1); (b2, n2)] [bs1; bs2] T);
    [reflexivity | exact Hh | exact Hlazy | reflexivity | exact Hfd | exact Hfdr
    | rewrite H17; apply u64_lit; lia
    | rewrite ms_gpr_epend0; exact H10 | rewrite ms_gpr_epend1; exact H11 | rewrite ms_gpr_epend2; exact H12
    | cbn; lia | change (Z.of_nat (length [(b1, n1); (b2, n2)])) with 2%Z; lia
    | | cbn [iov_bufs_ok]; repeat split; assumption | | cbn [iovs_total]; lia | cbn [iovs_total]; lia | ].
  - cbn [iov_array ms_mem epend].
    replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (Z_to_bv 64 (bv_unsigned iov + 24)).
    2:{ change (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (at_ (at_ iov 16) 8).
        rewrite at_at. reflexivity. }
    repeat split; try assumption; lia.
  - cbn [iov_bufs ms_mem epend]. repeat split; assumption.
  - intros k Hk1 Hk2. rewrite adv_set_epend. apply Hk; assumption.
Qed.

Lemma rz_writev1 : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 : word) bs1 (T : nat -> TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 1 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (1 <= bv_unsigned n1)%Z ->
  (bv_unsigned n1 <= 2 ^ 30)%Z ->
  (forall k, (1 <= k)%nat -> (k <= length bs1)%nat ->
     realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
              (T k)) ->
  realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
    (t_alt (fun i : wr_index bs1 =>
       t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs1)) (T (proj1_sig i)))).
Proof.
  intros regs pc mem model w fd iov b1 n1 bs1 T HF HE Hh Hlazy Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rs1 Hiok Hb1 Ht1 Ht30 Hk.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  pose proof (u64_range n1).
  replace bs1 with (concat [bs1]) in Hk by (cbn; rewrite app_nil_r; reflexivity).
  replace bs1 with (concat [bs1]) by (cbn; rewrite app_nil_r; reflexivity).
  eapply (rz_writev_pending (epend regs pc mem (seg_rom segs) (getr regs 17)) (getr regs 17) model fd iov
            [(b1, n1)] [bs1] T);
    [reflexivity | exact Hh | exact Hlazy | reflexivity | exact Hfd | exact Hfdr
    | rewrite H17; apply u64_lit; lia
    | rewrite ms_gpr_epend0; exact H10 | rewrite ms_gpr_epend1; exact H11 | rewrite ms_gpr_epend2; exact H12
    | cbn; lia | change (Z.of_nat (length [(b1, n1)])) with 1%Z; lia
    | | cbn [iov_bufs_ok]; split; [assumption | exact I] | | cbn [iovs_total]; lia | cbn [iovs_total]; lia | ].
  - cbn [iov_array ms_mem epend]. repeat split; try assumption; lia.
  - cbn [iov_bufs ms_mem epend]. split; [assumption | exact I].
  - intros k Hk1 Hk2. rewrite adv_set_epend. apply Hk; assumption.
Qed.

Lemma rz_writev1_wall : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 : word) bs1 (K : TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 1 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (1 <= bv_unsigned n1)%Z ->
  (bv_unsigned n1 <= 2 ^ 30)%Z ->
  K [] ->
  (forall k, (1 <= k)%nat -> (k <= length bs1)%nat ->
     realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
              (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)) ->
  realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 fd)) bs1) K).
Proof.
  intros regs pc mem model w fd iov b1 n1 bs1 K HF HE Hh Hlazy Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rs1 Hiok Hb1 Ht1 Ht30 HK Hk.
  pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (u64_range n1).
  apply rz_wall; [unfold word_to_nat in L1; lia | exact HK |].
  eapply (rz_writev1 regs pc mem model w fd iov b1 n1 bs1
            (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)); eassumption.
Qed.

Lemma rz_writev2_wall : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (K : TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 2 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 16)) 8%nat = Some (word_to_le_bytes 8 b2) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 24)) 8%nat = Some (word_to_le_bytes 8 n2) ->
  rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
  rdn segs mem b2 (word_to_nat n2) = Some bs2 ->
  (bv_unsigned iov + 32 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
  (1 <= bv_unsigned n1 + bv_unsigned n2)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  K [] ->
  (forall k, (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat ->
     realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
              (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)) ->
  realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 fd)) (bs1 ++ bs2)) K).
Proof.
  intros regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 K HF HE Hh Hlazy Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiok Hb1 Hb2 Ht1 Ht30 HK Hk.
  pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (rdn_length segs mem _ _ _ Rs2) as L2.
  pose proof (u64_range n1). pose proof (u64_range n2).
  apply rz_wall; [rewrite length_app; unfold word_to_nat in L1, L2; lia | exact HK |].
  eapply (rz_writev2 regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2
            (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)); eassumption.
Qed.

Lemma rz_writev1_zero : forall regs (pc : word) mem model w (fd : Z) (iov b1 : word) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 1 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 <= TASK_SIZE)%Z ->
  realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem (seg_rom segs)) model) K ->
  realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd iov b1 K HF HE Hh Hlazy Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Hiok Hb1 Hc.

  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 66%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Harr : iov_array segs (ms_mem ms) iov [(b1, Z_to_bv 64 0)]).
  { cbn [iov_array ms_mem ms epend]. refine (conj Rb1 (conj Rn1 (conj _ I))). rewrite u64_lit by lia. lia. }
  assert (Himp : import_iovecs (ms_read_byte ms) iov (Z_to_bv 64 1) = ImpOk [(b1, Z_to_bv 64 0)]).
  { unfold import_iovecs. rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
    rewrite (access_okb_of_le iov 16) by lia.
    rewrite (read_iovec_entry_of_array segs ms b1 (Z_to_bv 64 0) [] iov eq_refl Harr).
    rewrite u64_lit by lia. change (Z.min 0 MAX_RW_COUNT) with 0%Z.
    rewrite (access_okb_of_le b1 0) by lia. reflexivity. }
  assert (Hacc : import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 1) = [(iov, 16%nat)]).
  { unfold import_iovecs_accesses. rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
    rewrite (access_okb_of_le iov 16) by lia. reflexivity. }
  eapply (rz_ret_only_copyins_silent segs ms model (getr regs 17) [(iov, 16%nat)] (Z_to_bv 64 0) model);
    [exact Hh | reflexivity | | exact Hh | exact Hlazy | unfold ms; rewrite adv_set_epend; exact Hc].
  intros eff.
  rewrite (check_syscall_writev (sys_input segs ms (getr regs 17)) eff model) by (rewrite in_sysno_si; exact Hno).
  rewrite in_arg0_si, in_arg1_si, in_arg2_si.
  assert (G0 : ms_gpr ms 0 = Z_to_bv 64 fd) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (G1 : ms_gpr ms 1 = iov) by (unfold ms; rewrite ms_gpr_epend1; exact H11).
  assert (G2 : ms_gpr ms 2 = Z_to_bv 64 1) by (unfold ms; rewrite ms_gpr_epend2; exact H12).
  rewrite G0, G1, G2.
  rewrite fd32_id by (rewrite u64_lit; lia).
  unfold check_writev. rewrite Hfd.
  replace (w_is0 (Z_to_bv 64 fd)) with false by (symmetry; apply w_is0_pos; rewrite u64_lit; lia).
  change (iovcnt32 (Z_to_bv 64 1)) with (Z_to_bv 64 1).
  rewrite in_mem_si, Himp, Hacc.
  (* [comment removed for export] *)
  unfold cap_iovecs. cbn [cap_iovecs_aux iovs_total].
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.min_r by (unfold MAX_RW_COUNT; lia).
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. cbv beta iota zeta.
  change ((0 + 0 =? 0)%Z) with true. cbv beta iota. reflexivity.
Qed.

End G_LibWritev.

(* [comment removed for export] *)
Section G_SymDrive.
  Variable segs : list Segment.

Theorem rz_run : forall fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2
                         E M rom R model T,
  sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
  carry (s_log ss') kn [] = (kn', scs2, hs2) ->
  regs_ok E sr R -> know_ok segs E M kn ->
  scs_denot segs M E scs -> scs_denot segs M E scs2 ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  (forall R' M', regs_ok E (s_regs ss') R' -> know_ok segs E M' kn' ->
     M' = mem_denot E M (s_log ss') ->
     realizes segs (mkCfg (mkst R' (Z_to_bv 64 (s_pc ss')) M' rom) model) T) ->
  realizes segs (mkCfg (mkst R (Z_to_bv 64 pc) M rom) model) T.
Proof.
  intros fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R model T
         Hex Hc HR HK Hsc Hsc2 Hh Hlazy Hcont.
  destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E M rom R Hex HR HK Hsc)
    as (R' & HR' & Hlf & Hms).
  eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |].
  apply (Hcont R' _ HR'); [|reflexivity].
  eapply carry_after; eassumption.
Qed.

End G_SymDrive.

(* [comment removed for export] *)
Section G_PhaseG.
  Variable segs : list Segment.

  Local Notation GG := (GG segs).
  Local Notation gg_sys := (gg_sys segs).
  Local Notation gg_ret_only_silent := (gg_ret_only_silent segs).
  Local Notation gg_ret_only_copyins_silent := (gg_ret_only_copyins_silent segs).
  Local Notation gg_det := (gg_det segs).
  Local Notation gg_msteps := (gg_msteps segs).
  Local Notation gg_silent1 := (gg_silent1 segs).
  Local Notation gg_alt2 := (gg_alt2 segs).
  Local Notation gg_cases := (gg_cases segs).
  Local Notation gg_all := (gg_all segs).
  Local Notation gg_step := (gg_step segs).
  Local Notation gg_reach := (gg_reach segs).
  Local Notation gg_here := (gg_here segs).
  Local Notation gg_conseq := (gg_conseq segs).
  Local Notation gg_mono := (gg_mono segs).


  Lemma gg_close : forall mode Q regs (pc : word) mem model w fd e K,
    fetch_word segs pc = Some w -> is_ecall w = true ->
    m_halted model = None -> m_vm_lazy model = [] ->
    getr regs 17 = Z_to_bv 64 57 ->
    getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
    fd_lookup (m_fds model) fd = Some e ->
    GG mode Q K (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem (seg_rom segs))
                       (with_fds (fd_remove (m_fds model) fd) model)) ->
    GG mode Q K (mkCfg (mkst regs pc mem (seg_rom segs)) model).
  Proof.
    intros mode Q regs pc mem model w fd e K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hc.
    eapply gg_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply gg_ret_only_silent; [exact Hh | reflexivity | | | | rewrite adv_set_epend; exact Hc].
    - intros eff. rewrite (check_syscall_57 segs) by (rewrite H17; apply u64_lit; lia).
      unfold check_close. rewrite ms_gpr_epend0, Hfd, (fd32_id fd Hfd32), Hlk. reflexivity.
    - rewrite with_fds_halted'. exact Hh.
    - rewrite with_fds_lazy. exact Hlazy.
  Qed.

  Lemma gg_read_file : forall mode Q regs (pc : word) mem model w fd p off data (cnt : Z) K,
    fetch_word segs pc = Some w -> is_ecall w = true ->
    m_halted model = None -> m_vm_lazy model = [] ->
    getr regs 17 = Z_to_bv 64 63 ->
    getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
    fd_lookup (m_fds model) fd = Some (FdFile p off) ->
    fs_lookup (m_fs model) p = Some data ->
    getr regs 12 = Z_to_bv 64 cnt ->
    (1 <= cnt)%Z -> (cnt <= rw_bytes_max)%Z -> (cnt < 2 ^ 64)%Z ->
    store_ok segs mem (getr regs 11) (Z.to_nat cnt) = true ->
    access_okb (getr regs 11) cnt = true ->
    let bs := file_read data off (getr regs 12) in
    GG mode Q K (mkCfg (mkst (regupd regs 10 (len_word bs)) (v_addi pc 4)
                             (wbytes mem (getr regs 11) bs) (seg_rom segs))
                       (with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model)) ->
    GG mode Q K (mkCfg (mkst regs pc mem (seg_rom segs)) model).
  Proof.
    intros mode Q regs pc mem model w fd p off data cnt K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hfs H12 Hc1 Hmax H64 Hok Hacc bs Hc.
    assert (Hno : bv_unsigned (getr regs 17) = 63%Z) by (rewrite H17; apply u64_lit; lia).
    eapply gg_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    destruct (read_bytes_map_of_store_ok segs mem (getr regs 11) (Z.to_nat cnt) Hok ltac:(lia)) as [wv Hw].
    rewrite Z2Nat.id in Hw by lia.
    set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
    assert (Hu2 : bv_unsigned (ms_gpr ms 2) = cnt).
    { unfold ms. rewrite ms_gpr_epend2, H12. apply u64_lit. lia. }
    destruct (read_file_check segs ms (getr regs 17) model fd p off data wv Hno
                ltac:(unfold ms; rewrite ms_gpr_epend0; exact Hfd) Hfd32 Hlk Hfs
                ltac:(unfold ms; rewrite ms_writable_byte_epend, ms_gpr_epend1, ms_gpr_epend2, H12; exact Hw)
                ltac:(rewrite Hu2; lia) ltac:(rewrite Hu2; exact Hmax)
                ltac:(fold ms; rewrite Hu2; unfold ms; rewrite ms_gpr_epend1; exact Hacc)) as [Hchk Hnu].
    unfold ms in Hchk, Hnu. rewrite ms_gpr_epend1, ms_gpr_epend2 in Hchk.
    subst bs. revert Hc Hchk.
    generalize (file_read data off (getr regs 12)) as bs. intros bs Hc Hchk.
    eapply (gg_det mode Q _ model _ (mkEffect (len_word bs) (delivered_writes (getr regs 11) bs) [])
              (with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model));
      [exact Hh | reflexivity | exact Hchk | exact Hnu
      | rewrite with_fds_halted'; exact Hh | rewrite with_fds_lazy; exact Hlazy | ].
    destruct bs as [|b bsr]; cbn [delivered_writes].
    - unfold ms. rewrite adv_ret_epend. cbn [wbytes] in Hc. exact Hc.
    - unfold ms. rewrite adv_write1_epend. exact Hc.
  Qed.

  Theorem gg_run : forall mode Q fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2
                           E M rom R model T,
    sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
    carry (s_log ss') kn [] = (kn', scs2, hs2) ->
    regs_ok E sr R -> know_ok segs E M kn ->
    scs_denot segs M E scs -> scs_denot segs M E scs2 ->
    m_halted model = None ->
    m_vm_lazy model = [] ->
    (forall R' M', regs_ok E (s_regs ss') R' -> know_ok segs E M' kn' ->
       M' = mem_denot E M (s_log ss') ->
       GG mode Q T (mkCfg (mkst R' (Z_to_bv 64 (s_pc ss')) M' rom) model)) ->
    GG mode Q T (mkCfg (mkst R (Z_to_bv 64 pc) M rom) model).
  Proof.
    intros mode Q fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R model T
           Hex Hc HR HK Hsc Hsc2 Hh Hlazy Hcont.
    destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E M rom R Hex HR HK Hsc)
      as (R' & HR' & Hlf & Hms).
    eapply gg_msteps; [exact Hh | exact Hlazy | exact Hms |].
    apply (Hcont R' _ HR'); [|reflexivity].
    eapply carry_after; eassumption.
  Qed.

End G_PhaseG.

(* [comment removed for export] *)
Section G_RefNodesG.
  Variable segs : list Segment.

Lemma gg_of_rz_ex : forall mode Q K c c',
  (realizes segs c' K -> realizes segs c K) ->
  reach segs c c' ->
  GG segs mode Q K c' -> GG segs mode Q K c.
Proof.
  intros [|] Q K c c' Hrz Hex Hc.
  - apply gg_of_rz. apply Hrz. exact Hc.
  - eapply gg_reach; [exact Hex | exact Hc].
Qed.

Lemma gg_set_tid : forall mode Q regs (pc : word) mem rom model K w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 96 ->
  m_tid model = None ->
  (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     GG segs mode Q K (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model))) ->
  GG segs mode Q K (mkCfg (mkst regs pc mem rom) model).
Proof.
  intros [|] Q regs pc mem rom model K w HF HE Hh Hlazy H17 Htid Hk.
  - apply gg_of_rz. apply (rz_set_tid segs regs pc mem rom model K w HF HE Hh Hlazy H17 Htid).
    intros tid Ht. exact (Hk tid Ht).
  - eapply gg_reach; [eapply ex_set_tid_1; eassumption | apply Hk; apply one_tid_ok].
Qed.

Lemma gg_read_dir : forall mode Q regs (pc : word) mem model w fd K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some FdDir ->
  access_okb (getr regs 11) (bv_unsigned (getr regs 12)) = true ->
  GG segs mode Q K (mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem (seg_rom segs)) model) ->
  GG segs mode Q K (mkCfg (mkst regs pc mem (seg_rom segs)) model).
Proof.
  intros mode Q regs pc mem model w fd K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hdir.
  apply gg_of_rz_ex.
  - intros Hc. eapply rz_read_dir; eassumption.
  - eapply ex_read_dir; eassumption.
Qed.

Section Openat.
  Variables (regs : bvmap 5 word) (pc : word) (mem : word -> option byte) (model : Model).
  Variable w : bv 32.
  Hypothesis HF : fetch_word segs pc = Some w.
  Hypothesis HE : is_ecall w = true.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis H17 : getr regs 17 = Z_to_bv 64 56.
  Hypothesis H10 : getr regs 10 = AT_FDCWD.
  Hypothesis Hfl : Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z.

  Let post (r : word) := mkst (regupd regs 10 r) (v_addi pc 4) mem (seg_rom segs).
  Let fds := m_fds model.

  Lemma gg_openat_toolong : forall mode Q bs K,
    rdn segs mem (getr regs 11) 4096 = Some bs -> ~ In (Z_to_bv 8 0) bs ->
    GG segs mode Q K (mkCfg (post (errno_ret ENAMETOOLONG)) model) ->
    GG segs mode Q K (mkCfg (mkst regs pc mem (seg_rom segs)) model).
  Proof.
    intros mode Q bs K Hrd Hnz Hc. cbv beta delta [post] in *.
    pose proof (read_cstr_toolong_of_rdn segs mem (getr regs 11) bs (rdn_length _ _ _ _ _ Hrd) Hnz Hrd) as Hp.
    eapply gg_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply gg_ret_only_copyins_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
    intros eff. rewrite (openat_check_head segs regs pc mem model H17 H10 Hfl), Hp. apply check_copyins_after_ret_only.
  Qed.

  Lemma gg_openat_empty : forall mode Q K,
    path_at segs regs mem [] ->
    GG segs mode Q K (mkCfg (post (errno_ret ENOENT)) model) ->
    GG segs mode Q K (mkCfg (mkst regs pc mem (seg_rom segs)) model).
  Proof.
    intros mode Q K Hp Hc. cbv beta delta [post] in *.
    eapply gg_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply gg_ret_only_copyins_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
    intros eff. rewrite (openat_check_head segs regs pc mem model H17 H10 Hfl), (path_at_cstr segs regs mem [] Hp).
    apply check_copyins_after_ret_only.
  Qed.

  Lemma gg_openat_absent : forall mode Q p K,
    path_at segs regs mem p -> p <> [] -> path_has_slash p = false -> path_is_dirref p = false ->
    fs_lookup (m_fs model) p = None ->
    GG segs mode Q K (mkCfg (post (errno_ret ENOENT)) model) ->
    GG segs mode Q K (mkCfg (mkst regs pc mem (seg_rom segs)) model).
  Proof.
    intros mode Q p K Hp Hne Hns Hnd Hfs Hc. cbv beta delta [post] in *.
    eapply gg_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply gg_ret_only_copyins_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
    intros eff. rewrite (openat_check_head segs regs pc mem model H17 H10 Hfl), (path_at_cstr segs regs mem p Hp).
    rewrite (path_eqb_neq _ _ Hne), Hns, Hnd, Hfs. apply check_copyins_after_ret_only.
  Qed.

  Hypothesis Hfree : fd_lookup fds (alloc_fd fds) = None.

  (* [comment removed for export] *)
  Lemma gg_openat_dirref : forall mode Q p KA KB,
    path_at segs regs mem p -> path_is_dirref p = true ->
    (mode = true -> forall e, In e openat_errnos -> realizes segs (mkCfg (post (errno_ret e)) model) KA) ->
    GG segs mode Q KB (mkCfg (post (alloc_fd fds)) (with_fds (fd_insert fds (alloc_fd fds) FdDir) model)) ->
    GG segs mode Q (t_alt2 KA KB) (mkCfg (mkst regs pc mem (seg_rom segs)) model).
  Proof.
    intros mode Q p KA KB Hp Hd HA HB. cbv beta delta [post fds] in *.
    assert (Hne : path_eqb p [] = false).
    { destruct p; [|reflexivity]. cbv in Hd. discriminate Hd. }
    eapply gg_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    apply (gg_alt2 segs mode Q _ {e : Z | In e openat_errnos} unit
             (open_nx (epend regs pc mem (seg_rom segs) (getr regs 17)) model
                (fun fd => with_fds (fd_insert (m_fds model) fd FdDir) model)) KA KB
             (exist _ ENOMEM ENOMEM_in_openat_errnos) tt).
    - eapply node_open; [exact Hh | exact Hlazy | reflexivity | rewrite H17; apply u64_lit; lia | | | | exact Hfree].
      + intros eff. rewrite (openat_check_head segs regs pc mem model H17 H10 Hfl), (path_at_cstr segs regs mem _ Hp).
        rewrite Hne, (path_is_dirref_no_slash _ Hd), Hd. apply check_copyins_after_open_result.
      + intros fd. rewrite with_fds_halted'. exact Hh.
      + intros fd. rewrite with_fds_lazy. exact Hlazy.
    - intros Hm [e He]. cbn [open_nx]. rewrite adv_set_epend. apply (HA Hm). exact He.
    - intros []. cbn [open_nx]. rewrite adv_set_epend. exact HB.
  Qed.

  Lemma gg_openat_dot : forall mode Q KA KB,
    path_at segs regs mem dot_path ->
    (mode = true -> forall e, In e openat_errnos -> realizes segs (mkCfg (post (errno_ret e)) model) KA) ->
    GG segs mode Q KB (mkCfg (post (alloc_fd fds)) (with_fds (fd_insert fds (alloc_fd fds) FdDir) model)) ->
    GG segs mode Q (t_alt2 KA KB) (mkCfg (mkst regs pc mem (seg_rom segs)) model).
  Proof. intros mode Q KA KB Hp HA HB. exact (gg_openat_dirref mode Q dot_path KA KB Hp eq_refl HA HB). Qed.

  (* [comment removed for export] *)
  Lemma gg_openat_file : forall mode Q p d KA KB,
    path_at segs regs mem p -> p <> [] -> path_has_slash p = false -> path_is_dirref p = false ->
    fs_lookup (m_fs model) p = Some d ->
    (mode = true -> forall e, In e openat_errnos -> realizes segs (mkCfg (post (errno_ret e)) model) KA) ->
    GG segs mode Q KB (mkCfg (post (alloc_fd fds))
                             (with_fds (fd_insert fds (alloc_fd fds) (FdFile p (Z_to_bv 64 0))) model)) ->
    GG segs mode Q (t_alt2 KA KB) (mkCfg (mkst regs pc mem (seg_rom segs)) model).
  Proof.
    intros mode Q p d KA KB Hp Hne Hns Hnd Hfs HA HB. cbv beta delta [post fds] in *.
    eapply gg_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    apply (gg_alt2 segs mode Q _ {e : Z | In e openat_errnos} unit
             (open_nx (epend regs pc mem (seg_rom segs) (getr regs 17)) model
                (fun fd => with_fds (fd_insert (m_fds model) fd (FdFile p (Z_to_bv 64 0))) model)) KA KB
             (exist _ ENOMEM ENOMEM_in_openat_errnos) tt).
    - eapply node_open; [exact Hh | exact Hlazy | reflexivity | rewrite H17; apply u64_lit; lia | | | | exact Hfree].
      + intros eff. rewrite (openat_check_head segs regs pc mem model H17 H10 Hfl), (path_at_cstr segs regs mem p Hp).
        rewrite (path_eqb_neq _ _ Hne), Hns, Hnd, Hfs. apply check_copyins_after_open_result.
      + intros fd. rewrite with_fds_halted'. exact Hh.
      + intros fd. rewrite with_fds_lazy. exact Hlazy.
    - intros Hm [e He]. cbn [open_nx]. rewrite adv_set_epend. apply (HA Hm). exact He.
    - intros []. cbn [open_nx]. rewrite adv_set_epend. exact HB.
  Qed.
End Openat.

End G_RefNodesG.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section G_Alloc.
  Variable segs : list Segment.

  Lemma CFG_inj_off : forall ms x8, (bv_unsigned x8 = 214 \/ bv_unsigned x8 = 222 \/ bv_unsigned x8 = 226)%Z ->
    injected_family_off CFG (sys_input segs ms x8) = true.
  Proof. intros ms x8 H. rewrite NodesCfg.injected_family_off_sysno. destruct H as [-> | [-> | ->]]; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma node_sum_r : forall ms model x8 (IA IB : Type) (nx : IA + IB -> config) (b0 : IB),
    ms_svc_pending ms = Some x8 ->
    (bv_unsigned x8 = 214 \/ bv_unsigned x8 = 222 \/ bv_unsigned x8 = 226)%Z ->
    ShapeAlg.node_ok segs (mkCfg ms model) (IA + IB) (fun _ => []) nx ->
    (forall i, m_halted (cfg_model (nx i)) = None) ->
    (forall a, refusal_b (sys_input segs ms x8) model (ms_gpr (cfg_ms (nx (inl a))) 0) = true) ->
    (forall b, refusal_b (sys_input segs ms x8) model (ms_gpr (cfg_ms (nx (inr b))) 0) = false) ->
    node_ok segs (mkCfg ms model) IB (fun _ => []) (fun b => nx (inr b)).
  Proof.
    intros ms model x8 IA IB nx b0 Hsvc Hno Hnode Hrun HA HB.
    exact (NodesCfg.node_ok_cfg_of_plain_sum_r CFG segs ms model x8 IA IB (fun _ => []) nx b0 Hsvc (CFG_inj_off ms x8 Hno) Hnode Hrun HA HB).
  Qed.

  Lemma gg_sum_r : forall mode Q ms model x8 (IA IB : Type) (nx : IA + IB -> config) (B : TSet) (b0 : IB),
    ms_svc_pending ms = Some x8 ->
    (bv_unsigned x8 = 214 \/ bv_unsigned x8 = 222 \/ bv_unsigned x8 = 226)%Z ->
    ShapeAlg.node_ok segs (mkCfg ms model) (IA + IB) (fun _ => []) nx ->
    (forall i, m_halted (cfg_model (nx i)) = None) ->
    (forall a, refusal_b (sys_input segs ms x8) model (ms_gpr (cfg_ms (nx (inl a))) 0) = true) ->
    (forall b, refusal_b (sys_input segs ms x8) model (ms_gpr (cfg_ms (nx (inr b))) 0) = false) ->
    (forall i, GG segs mode Q B (nx (inr i))) ->
    GG segs mode Q B (mkCfg ms model).
  Proof.
    intros mode Q ms model x8 IA IB nx B b0 Hsvc Hno Hnode Hrun HA HB HK.
    exact (gg_all segs mode Q (mkCfg ms model) IB (fun b => nx (inr b)) B b0
             (node_sum_r ms model x8 IA IB nx b0 Hsvc Hno Hnode Hrun HA HB) HK).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma gg_mmap_raw : forall mode Q ms model x8 (A B : TSet),
    m_halted model = None -> m_vm_lazy model = [] ->
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 222%Z ->
    mmap_args_ok ms ->
    (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
       GG segs mode Q B (mkCfg (advance_past_svc
                             (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                          (mmap_model a (page_round_up (ms_gpr ms 1)) model))) ->
    (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
    GG segs mode Q B (mkCfg ms model).
  Proof.
    intros mode Q ms model x8 A B Hh Hlazy Hsvc Hno Hargs HB Hex.
    set (n := page_round_up (ms_gpr ms 1)).
    set (nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1))).
    destruct Hex as [b0 Hb0].
    pose (IA := {e : Z | In e mmap_errnos}).
    pose (IB := {a : word | grant_ok (ms_gpr ms 0) model a nZ = true}).
    pose (nx := fun (i : IA + IB) =>
      match i with
      | inl (exist _ e _) => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
      | inr (exist _ a _) =>
          mkCfg (advance_past_svc (apply_effect ms (mkEffect a [] [(a, n)]))) (mmap_model a n model)
      end).
    apply (gg_sum_r mode Q ms model x8 IA IB nx B (exist _ b0 Hb0) Hsvc (or_intror (or_introl Hno))).
    - split.
      + intros [[e He] | [a Ha]]; cbn.
        * rewrite <- (apply_effect_no_write ms (errno_ret e)).
          apply (sstep_syscall segs ms model x8 (mkEffect (errno_ret e) [] []) model model []).
          -- exact Hh.
          -- exact Hsvc.
          -- apply mmap_fail_ok; assumption.
          -- exact Hh.
          -- apply materialize_model_accesses_no_lazy. exact Hlazy.
        * apply (sstep_syscall segs ms model x8 (mkEffect a [] [(a, n)])
                   (mmap_model a n model) (mmap_model a n model) []).
          -- exact Hh.
          -- exact Hsvc.
          -- apply mmap_succ_ok; assumption.
          -- rewrite mmap_model_halted; exact Hh.
          -- apply materialize_model_accesses_no_lazy.
             exact (eq_trans (mmap_model_lazy _ _ _) Hlazy).
      + intros e st Hss.
        destruct (sstep_mmap_inv segs ms model x8 e st Hh Hlazy Hsvc Hno Hargs Hss)
          as [-> [(er & Her & ->) | (a & Ha & ->)]].
        * exists (inl (exist _ er Her)). split; reflexivity.
        * exists (inr (exist _ a Ha)). split; reflexivity.
    - intros [[e He] | [a Ha]]; cbn [nx cfg_model]; [exact Hh | rewrite mmap_model_halted; exact Hh].
    - intros [e He]. cbn [nx cfg_ms]. rewrite NodesCfg.ms_gpr0_set_gpr0.
      destruct He as [<- | []]. exact (AllocCfg.mmap_refusal_enomem segs ms x8 model Hno).
    - intros [a Ha]. cbn [nx cfg_ms]. rewrite NodesCfg.ms_gpr0_apply_effect. cbn [eff_ret].
      apply (AllocCfg.mmap_refusal_grant segs ms x8 model a Hno).
      exact (proj1 (grant_ok_unpack _ _ _ _ Ha)).
    - intros [a Ha]; cbn. apply HB; exact Ha.
  Qed.

  Lemma rz_mmap : forall ms model x8 (A B : TSet),
    m_halted model = None -> m_vm_lazy model = [] ->
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 222%Z ->
    mmap_args_ok ms ->
    (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
       realizes segs (mkCfg (advance_past_svc
                         (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                       (mmap_model a (page_round_up (ms_gpr ms 1)) model)) B) ->
    (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
    realizes segs (mkCfg ms model) B.
  Proof.
    intros ms model x8 A B Hh Hlazy Hsvc Hno Hargs HB Hex.
    exact (gg_mmap_raw true (fun _ => True) ms model x8 A B Hh Hlazy Hsvc Hno Hargs HB Hex).
  Qed.
  (* [comment removed for export] *)
  Lemma gg_munmap_raw : forall mode Q ms model x8 T,
    m_halted model = None -> m_vm_lazy model = [] ->
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 215%Z ->
    munmap_args_ok ms model ->
    GG segs mode Q T (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                       (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) ->
    GG segs mode Q T (mkCfg ms model).
  Proof.
    intros mode Q ms model x8 T Hh Hlazy Hsvc Hno Hargs Hc.
    eapply gg_silent1; [| exact Hc]. apply node_lift_det. split.
    - intros []. apply (sstep_syscall segs ms model x8 (munmap_eff ms)
                          (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
                          (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
      + exact Hh.
      + exact Hsvc.
      + apply munmap_ok; assumption.
      + rewrite munmap_model_halted; exact Hh.
      + apply materialize_model_accesses_no_lazy. exact (munmap_model_no_lazy _ _ _ Hlazy).
    - intros e st Hss.
      destruct (sstep_munmap_inv segs ms model x8 e st Hh Hlazy Hsvc Hno Hargs Hss) as [-> ->].
      exists tt. split; reflexivity.
  Qed.

  Lemma rz_munmap_raw : forall ms model x8 T,
    m_halted model = None -> m_vm_lazy model = [] ->
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 215%Z ->
    munmap_args_ok ms model ->
    realizes segs (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                    (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) T ->
    realizes segs (mkCfg ms model) T.
  Proof. intros ms model x8 T. exact (gg_munmap_raw true (fun _ => True) ms model x8 T). Qed.

  (* [comment removed for export] *)
  Lemma brk_next_halted : forall ms model (x8 : word) r,
    m_halted model = None -> m_vm_lazy model = [] -> bv_unsigned x8 = 214%Z ->
    brk_resolution_ok model (ms_gpr ms 0) r ->
    m_halted (brk_model (ms_gpr ms 0) r model) = None.
  Proof.
    intros ms model x8 r Hh Hlazy Hno Hr.
    pose proof (brk_ok_intro segs ms x8 model r Hno Hr) as Hspec.
    exact (proj1 (proj2 (brk_step_shape segs ms x8 model _ _ _ Hh Hlazy Hno Hspec))).
  Qed.

  (* [comment removed for export] *)
  Lemma gg_brk_query : forall mode Q regs (pc : word) mem model w K,
    fetch_word segs pc = Some w -> is_ecall w = true ->
    m_halted model = None -> m_vm_lazy model = [] ->
    getr regs 17 = Z_to_bv 64 214 ->
    getr regs 10 = Z_to_bv 64 0 ->
    GG segs mode Q K (mkCfg (mkst (regupd regs 10 (vm_brk (m_vmmaps model))) (v_addi pc 4) mem (seg_rom segs)) model) ->
    GG segs mode Q K (mkCfg (mkst regs pc mem (seg_rom segs)) model).
  Proof.
    intros mode Q regs pc mem model w K HF HE Hh Hlazy H17 H10 Hc.
    eapply gg_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
    assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
    assert (H0 : ms_gpr ms 0 = Z_to_bv 64 0) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
    assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> r = vm_brk (m_vmmaps model)).
    { intros r. rewrite H0. unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta.
      unfold w_is0. rewrite bv_eqb_refl. cbn [orb]. apply bv_eqb_eq. }
    assert (Hq : brk_resolution_ok model (ms_gpr ms 0) (vm_brk (m_vmmaps model))) by (apply Hcases; reflexivity).
    eapply (gg_all segs mode Q (mkCfg ms model) _ _ K (exist _ _ Hq)).
    - apply (NodesCfg.node_ok_cfg_of_plain_nonrefusal CFG segs ms model (getr regs 17)); [reflexivity | |
        exact (node_brk segs ms model (getr regs 17) Hh Hlazy eq_refl Hno)].
      intros [r Hr] _. cbn [cfg_ms proj1_sig]. rewrite NodesCfg.ms_gpr0_apply_effect. cbn [eff_ret].
      rewrite NodesCfg.refusal_b_brk by (rewrite NodesCfg.in_sysno_sys_input; exact Hno).
      rewrite NodesCfg.in_arg0_sys_input, H0. unfold brk_refusal_b. cbv zeta.
      unfold w_is0. rewrite bv_eqb_refl. reflexivity.
    - intros [r Hr]. cbn [proj1_sig].
      pose proof (proj1 (Hcases r) Hr) as Er. subst r.
      rewrite H0, brk_zeros_query, brk_unmaps_keep.
      rewrite (brk_model_query _ model eq_refl), vmmaps_eta, with_vmmaps_eta.
      unfold ms. rewrite adv_ret_epend. exact Hc.
  Qed.

  (* [comment removed for export] *)
  Lemma gg_brk_grow : forall mode Q regs (pc : word) mem model w (d : Z) (KB : TSet),
    fetch_word segs pc = Some w -> is_ecall w = true ->
    m_halted model = None -> m_vm_lazy model = [] ->
    getr regs 17 = Z_to_bv 64 214 ->
    let h := m_vmmaps model in
    let b := vm_brk h in
    (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
    (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
    (bv_unsigned (vm_start_brk h) <= bv_unsigned b + d)%Z ->
    getr regs 10 = Z_to_bv 64 (bv_unsigned b + d) ->
    Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true ->
    GG segs mode Q KB
       (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (bv_unsigned b + d))) (v_addi pc 4)
                    (zfill b (Z_to_bv 64 d) mem) (seg_rom segs))
              (with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                             (vm_noaccess h) (vm_start_brk h)
                             (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) model)) ->
    GG segs mode Q KB (mkCfg (mkst regs pc mem (seg_rom segs)) model).
  Proof.
    intros mode Q regs pc mem model w d KB HF HE Hh Hlazy H17 h b Hbal Hdal Hd Hb0 Hnw Hs H10 Hadm HB.
    pose proof (u64_range b) as Hbr.
    set (req := Z_to_bv 64 (bv_unsigned b + d)) in *.
    assert (Hureq : bv_unsigned req = (bv_unsigned b + d)%Z) by (unfold req; apply u64_lit; lia).
    eapply gg_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
    assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
    assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
    assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> (r = b \/ (r = req /\ Mmap.brk_grow_ok model req req = true))).
    { intros r. rewrite H0. apply brk_r_ok_grow_cases; fold h; fold b; rewrite ?Hureq; lia. }
    assert (Hgrow : brk_resolution_ok model (ms_gpr ms 0) req) by (apply Hcases; right; split; [reflexivity | exact Hadm]).
    assert (Hneq : req <> b).
    { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E. unfold b in E. lia. }
    assert (Hrefb : forall ret, refusal_b (sys_input segs ms (getr regs 17)) model ret = bv_eqb ret b).
    { intros ret. rewrite NodesCfg.refusal_b_brk by (rewrite NodesCfg.in_sysno_sys_input; exact Hno).
      rewrite NodesCfg.in_arg0_sys_input, H0. unfold brk_refusal_b. cbv zeta. fold h. fold b.
      assert (E0 : w_is0 req = false).
      { unfold w_is0, bv_eqb. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. apply Z.eqb_neq. lia. }
      rewrite E0. unfold min_brk. rewrite (proj2 (Z.ltb_ge _ _)) by (fold h; lia).
      rewrite (bv_eqb_neq _ _ Hneq). reflexivity. }
    pose (I := {r : word | brk_resolution_ok model (ms_gpr ms 0) r}).
    pose (J := {i : I | proj1_sig i = req}).
    pose (nx := fun i : I => mkCfg (advance_past_svc (apply_effect ms
                         (mkEffectU (proj1_sig i) []
                            (brk_zeros (ms_gpr ms 0) (proj1_sig i) (vm_brk (m_vmmaps model)))
                            (brk_unmaps (proj1_sig i) (vm_brk (m_vmmaps model))) [] [])))
                      (brk_model (ms_gpr ms 0) (proj1_sig i) model)).
    assert (j0 : J) by (exists (exist _ req Hgrow); reflexivity).
    eapply (gg_all segs mode Q (mkCfg ms model) J (fun j => nx (proj1_sig j)) KB j0).
    - apply (NodesCfg.node_ok_cfg_of_plain_filter CFG segs ms model (getr regs 17) I J (fun _ => []) nx (@proj1_sig I _) j0 eq_refl
               (CFG_inj_off ms (getr regs 17) (or_introl Hno))
               (node_brk segs ms model (getr regs 17) Hh Hlazy eq_refl Hno)).
      + intros [r Hr]. cbn [nx cfg_model proj1_sig]. exact (brk_next_halted ms model (getr regs 17) r Hh Hlazy Hno Hr).
      + intros [[r Hr] E]. cbn [proj1_sig] in E. subst r. cbn [nx cfg_ms proj1_sig].
        rewrite NodesCfg.ms_gpr0_apply_effect. cbn [eff_ret]. rewrite Hrefb. apply bv_eqb_neq. exact Hneq.
      + intros [r Hr]. destruct (proj1 (Hcases r) Hr) as [-> | [-> Hg]].
        * right. cbn [nx cfg_ms proj1_sig]. rewrite NodesCfg.ms_gpr0_apply_effect. cbn [eff_ret]. rewrite Hrefb. apply bv_eqb_refl.
        * left. exists (exist (fun i : I => proj1_sig i = req) (exist _ req Hr) eq_refl). reflexivity.
    - intros [[r Hr] E]. cbn [proj1_sig] in E. subst r. unfold nx. cbn [proj1_sig]. fold h.
      assert (Hlt : (bv_unsigned b < bv_unsigned req)%Z) by (rewrite Hureq; lia).
      assert (Hreq0 : req <> Z_to_bv 64 0).
      { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
        change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
      rewrite H0. fold b. rewrite (brk_zeros_grow req req b Hreq0 Hb0 Hlt), (brk_unmaps_grow req b) by lia.
      unfold brk_page_range.
      rewrite (page_round_up_Z_aligned (bv_unsigned b)) by (first [lia | exact Hbal]).
      rewrite (page_round_up_Z_aligned (bv_unsigned req))
        by (rewrite Hureq; first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
      rewrite (proj2 (Z.ltb_lt _ _) Hlt).
      replace (Z_to_bv 64 (bv_unsigned b)) with b by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
      rewrite Hureq. replace (bv_unsigned b + d - bv_unsigned b)%Z with d by lia.
      unfold req, b, h. rewrite (brk_model_grow_eq model d) by assumption.
      unfold ms. rewrite adv_zeros1_epend. exact HB.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma gg_mmap_fixed_noaccess : forall mode Q regs (pc : word) mem model w (addr : word) (len : Z) (KB : TSet),
    fetch_word segs pc = Some w -> is_ecall w = true ->
    m_halted model = None -> m_vm_lazy model = [] ->
    getr regs 17 = Z_to_bv 64 222 ->
    getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
    getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
    (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
    getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 50 ->
    getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
    let n := Z_to_bv 64 (page_round_up_Z len) in
    region_free (vm_reserved (m_vmmaps model)) addr n = true ->
    map_contains (vm_maps (m_vmmaps model)) addr n = true ->
    GG segs mode Q KB (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (unfill addr n mem) (seg_rom segs))
                             (fixed_noaccess_model addr n model)) ->
    GG segs mode Q KB (mkCfg (mkst regs pc mem (seg_rom segs)) model).
  Proof.
    intros mode Q regs pc mem model w addr len KB HF HE Hh Hlazy H17 H10 Hal Hpos H11 Hlen Hce H12 H13 H14 H15 n Hrf Hmc HB.
    pose proof (alloc_top_room (m_vmmaps model)) as Hcv. pose proof stack_max_size_val as Hsms.
    unfold two_pow_64 in Hcv. pose proof (u64_range addr) as Har.
    eapply gg_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
    assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
    assert (Hlen' : (len < 2 ^ 64)%Z) by (pose proof (page_round_up_Z_bounds len ltac:(lia)); lia).
    assert (Hargs : mmap_fixed_args_ok ms).
    { unfold mmap_fixed_args_ok, ms.
      rewrite ms_gpr_epend1, ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend4, ms_gpr_epend5.
      rewrite H11, H12, H13, H14, H15. repeat split; try reflexivity.
      intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia. }
    pose proof (fun eff => mmap_fixed_check segs ms (getr regs 17) model eff addr len Hno Hargs
                             ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
                             ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Hce Hrf Hmc) as Hchk.
    cbv zeta in Hchk. fold n in Hchk.
    assert (Haddr_ne : errno_ret_in mmap_errnos addr = false).
    { apply errno_ret_in_below; [reflexivity|]. unfold two_pow_64.
      pose proof (page_round_up_Z_bounds len ltac:(lia)). lia. }
    pose (effs := fun i : three => match i with
                             | T1 => mkEffectU (errno_ret ENOMEM) [] [] [] [] []
                             | T2 => mkEffectU addr [] [] [(addr, n)] [] []
                             | T3 => mkEffectU (errno_ret ENOMEM) [] [] [(addr, n)] [] [] end).
    pose (ms' := fun i : three => match i with
                            | T1 => model
                            | T2 => fixed_noaccess_model addr n model
                            | T3 => fixed_destroyed_model addr n model end).
    assert (Herr : forall e, In e mmap_errnos -> e = ENOMEM).
    { intros e [<-|[]]. reflexivity. }
    pose (nx := fun i : three => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
    assert (Hplain : ShapeAlg.node_ok segs (mkCfg ms model) three (fun _ => []) nx).
    { apply (node_chk segs ms model (getr regs 17) three effs ms' Hh eq_refl).
      + intros [| |]; cbn [effs ms']; rewrite Hchk.
        * rewrite (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos). reflexivity.
        * rewrite Haddr_ne, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
        * rewrite (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos), (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
      + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
        destruct ws; [|discriminate]. destruct zs; [|discriminate].
        destruct cs; [|discriminate]. destruct ci; [|discriminate].
        destruct (errno_ret_in mmap_errnos r) eqn:Er.
        * destruct (proj1 (errno_ret_in_true _ _) Er) as (e & He & ->). rewrite (Herr e He).
          destruct us.
          -- injection Hc as <- <-. exists T1. repeat split; reflexivity.
          -- destruct (listNN_eqb (p :: us) [(addr, n)]) eqn:Hl; [|discriminate].
             apply listNN_eqb_eq in Hl. rewrite Hl. injection Hc as <- <-. exists T3. repeat split; reflexivity.
        * destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
          destruct (listNN_eqb us [(addr, n)]) eqn:Hl; [|discriminate].
          apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst. injection Hc as <- <-.
          exists T2. repeat split; reflexivity.
      + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
        destruct ws; [|discriminate]. destruct zs; [|discriminate].
        destruct cs; [|discriminate]. destruct ci; [|discriminate].
        destruct (errno_ret_in mmap_errnos r); [destruct us; [discriminate|]; destruct (listNN_eqb _ _); discriminate|].
        destruct (bv_eqb r addr && listNN_eqb us [(addr, n)])%bool; discriminate.
      + intros [| |]; cbn [ms']; [exact Hh | unfold fixed_noaccess_model | unfold fixed_destroyed_model];
          rewrite vm_forget_range_halted, with_vmmaps_halted; exact Hh.
      + intros [| |]; cbn [ms']; [exact Hlazy | unfold fixed_noaccess_model | unfold fixed_destroyed_model];
          apply vm_forget_range_lazy_nil; rewrite with_vmmaps_lazy'; exact Hlazy. }
    eapply (gg_all segs mode Q (mkCfg ms model) unit (fun _ => nx T2) KB tt).
    - apply (NodesCfg.node_ok_cfg_of_plain_filter CFG segs ms model (getr regs 17) three unit (fun _ => []) nx (fun _ => T2) tt eq_refl
               (CFG_inj_off ms (getr regs 17) (or_intror (or_introl Hno))) Hplain).
      + intros [| |]; unfold nx; cbn [cfg_model ms']; [exact Hh | unfold fixed_noaccess_model | unfold fixed_destroyed_model];
          rewrite vm_forget_range_halted, with_vmmaps_halted; exact Hh.
      + intros _. unfold nx. cbn [cfg_ms effs]. rewrite NodesCfg.ms_gpr0_apply_effect. cbn [eff_ret].
        apply (AllocCfg.mmap_refusal_grant segs ms (getr regs 17) model addr Hno Hal).
      + intros [| |]; [right | left; exists tt; reflexivity | right]; unfold nx; cbn [cfg_ms effs];
          rewrite NodesCfg.ms_gpr0_apply_effect; cbn [eff_ret]; exact (AllocCfg.mmap_refusal_enomem segs ms (getr regs 17) model Hno).
    - intros _. unfold nx. cbn [effs ms']. unfold ms. rewrite adv_unmaps1_epend. exact HB.
  Qed.
End G_Alloc.


Section G_AllocReplay.
  Variable segs : list Segment.
  Local Notation GG := (GG segs).
  Local Notation gg_sys := (gg_sys segs).
  Local Notation gg_ret_only_silent := (gg_ret_only_silent segs).
  Local Notation gg_ret_only_copyins_silent := (gg_ret_only_copyins_silent segs).
  Local Notation gg_det := (gg_det segs).
  Local Notation gg_msteps := (gg_msteps segs).
  Local Notation gg_silent1 := (gg_silent1 segs).
  Local Notation gg_alt2 := (gg_alt2 segs).
  Local Notation gg_cases := (gg_cases segs).
  Local Notation gg_all := (gg_all segs).
  Local Notation gg_step := (gg_step segs).
  Local Notation gg_reach := (gg_reach segs).
  Local Notation gg_here := (gg_here segs).
  Local Notation gg_conseq := (gg_conseq segs).
  Local Notation gg_mono := (gg_mono segs).
  Local Notation gg_mmap_raw := (gg_mmap_raw segs).
  Local Notation gg_munmap_raw := (gg_munmap_raw segs).

Lemma rz_mmap_anon : forall regs (pc : word) mem model w (len : Z) KA KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = Z_to_bv 64 34 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let n := page_round_up_Z len in
  (exists a, grant_ok (getr regs 10) model a n = true) ->
  (forall e, In e mmap_errnos ->
     realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem (seg_rom segs)) model) KA) ->
  (forall a, grant_ok (getr regs 10) model a n = true ->
     realizes segs (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4)
                                (zfill a (Z_to_bv 64 n) mem) (seg_rom segs))
                         (mmap_model a (Z_to_bv 64 n) model)) KB) ->
  realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) KB.
Proof.
  intros regs pc mem model w len KA KB HF HE Hh Hlazy H17 H11 Hlen H12 H13 H14 H15 n Hex HA HB.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
  { unfold ms. rewrite ms_gpr_epend1, H11. apply u64_lit. lia. }
  assert (Hpr : page_round_up (ms_gpr ms 1) = Z_to_bv 64 n).
  { unfold page_round_up. rewrite Hu1. reflexivity. }
  assert (Hargs : mmap_args_ok ms).
  { unfold mmap_args_ok, ms.
    rewrite ms_gpr_epend1, ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend4, ms_gpr_epend5.
    rewrite H11, H12, H13, H14, H15. repeat split; try reflexivity.
    intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia. }
  assert (H0 : ms_gpr ms 0 = getr regs 10) by (unfold ms; rewrite ms_gpr_epend0; reflexivity).
  eapply (rz_mmap segs ms model (getr regs 17) KA KB Hh Hlazy eq_refl
            ltac:(rewrite H17; apply u64_lit; lia) Hargs).
  - intros a Ha. rewrite Hpr. rewrite H0, Hu1 in Ha. unfold ms, epend. rewrite adv_mmap_grant. apply HB. exact Ha.
  - rewrite H0, Hu1. exact Hex.
Qed.

  Lemma gg_mmap_anon : forall mode Q regs (pc : word) mem model w (len : Z) KA KB,
    fetch_word segs pc = Some w -> is_ecall w = true ->
    m_halted model = None -> m_vm_lazy model = [] ->
    getr regs 17 = Z_to_bv 64 222 ->
    getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
    getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = Z_to_bv 64 34 ->
    getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
    let n := page_round_up_Z len in
    (exists a, grant_ok (getr regs 10) model a n = true) ->
    (mode = true -> forall e, In e mmap_errnos ->
       realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem (seg_rom segs)) model) KA) ->
    (forall a, grant_ok (getr regs 10) model a n = true ->
       GG mode Q KB (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4)
                                  (zfill a (Z_to_bv 64 n) mem) (seg_rom segs))
                          (mmap_model a (Z_to_bv 64 n) model))) ->
    GG mode Q KB (mkCfg (mkst regs pc mem (seg_rom segs)) model).
  Proof.
    intros mode Q regs pc mem model w len KA KB HF HE Hh Hlazy H17 H11 Hlen H12 H13 H14 H15 n Hex HA HB.
    eapply gg_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
    assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
    { unfold ms. rewrite ms_gpr_epend1, H11. apply u64_lit. lia. }
    assert (Hpr : page_round_up (ms_gpr ms 1) = Z_to_bv 64 n).
    { unfold page_round_up. rewrite Hu1. reflexivity. }
    assert (Hargs : mmap_args_ok ms).
    { unfold mmap_args_ok, ms.
      rewrite ms_gpr_epend1, ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend4, ms_gpr_epend5.
      rewrite H11, H12, H13, H14, H15. repeat split; try reflexivity.
      intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia. }
    assert (H0 : ms_gpr ms 0 = getr regs 10) by (unfold ms; rewrite ms_gpr_epend0; reflexivity).
    eapply (gg_mmap_raw mode Q ms model (getr regs 17) KA KB Hh Hlazy eq_refl
              ltac:(rewrite H17; apply u64_lit; lia) Hargs).
    - intros a Ha. rewrite Hpr. rewrite H0, Hu1 in Ha. unfold ms, epend. rewrite adv_mmap_grant. apply HB. exact Ha.
    - rewrite H0, Hu1. exact Hex.
  Qed.

Lemma rz_munmap : forall regs (pc : word) mem model w (a : word) (len : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 215 ->
  getr regs 10 = a -> (bv_unsigned a mod page_size = 0)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned a + page_round_up_Z len <= TASK_SIZE)%Z ->
  map_has (vm_maps (m_vmmaps model)) a (Z_to_bv 64 (page_round_up_Z len)) = true ->
  realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
                             (unfill a (Z_to_bv 64 (page_round_up_Z len)) mem) (seg_rom segs))
                      (munmap_model a (Z_to_bv 64 (page_round_up_Z len)) model)) K ->
  realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w a len K HF HE Hh Hlazy H17 H10 Hal H11 Hlen Hnw Hhas Hc.
  assert (Hlen' : (len < two_pow_64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range a).
    unfold TASK_SIZE in Hnw. unfold two_pow_64. lia. }
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
  { unfold ms. rewrite ms_gpr_epend1, H11. apply u64_lit. unfold two_pow_64 in Hlen'. lia. }
  assert (Hpr : page_round_up (ms_gpr ms 1) = Z_to_bv 64 (page_round_up_Z len)).
  { unfold page_round_up. rewrite Hu1. reflexivity. }
  assert (H0 : ms_gpr ms 0 = a) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hargs : munmap_args_ok ms model).
  { unfold munmap_args_ok. rewrite H0, Hu1, Hpr. repeat split; try assumption.
    intro Hz. apply (f_equal bv_unsigned) in Hz. rewrite Hu1 in Hz.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hz. lia. }
  eapply (rz_munmap_raw segs ms model (getr regs 17));
    [exact Hh | exact Hlazy | reflexivity | rewrite H17; apply u64_lit; lia | exact Hargs |].
  unfold munmap_eff. rewrite H0, Hpr. unfold ms. rewrite adv_unmaps1_epend. exact Hc.
Qed.

  Lemma gg_munmap : forall mode Q regs (pc : word) mem model w (a : word) (len : Z) K,
    fetch_word segs pc = Some w -> is_ecall w = true ->
    m_halted model = None -> m_vm_lazy model = [] ->
    getr regs 17 = Z_to_bv 64 215 ->
    getr regs 10 = a -> (bv_unsigned a mod page_size = 0)%Z ->
    getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
    (bv_unsigned a + page_round_up_Z len <= TASK_SIZE)%Z ->
    map_has (vm_maps (m_vmmaps model)) a (Z_to_bv 64 (page_round_up_Z len)) = true ->
    GG mode Q K (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
                             (unfill a (Z_to_bv 64 (page_round_up_Z len)) mem) (seg_rom segs))
                       (munmap_model a (Z_to_bv 64 (page_round_up_Z len)) model)) ->
    GG mode Q K (mkCfg (mkst regs pc mem (seg_rom segs)) model).
  Proof.
    intros mode Q regs pc mem model w a len K HF HE Hh Hlazy H17 H10 Hal H11 Hlen Hnw Hhas Hc.
    assert (Hlen' : (len < two_pow_64)%Z).
    { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range a).
      unfold TASK_SIZE in Hnw. unfold two_pow_64. lia. }
    eapply gg_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
    assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
    { unfold ms. rewrite ms_gpr_epend1, H11. apply u64_lit. unfold two_pow_64 in Hlen'. lia. }
    assert (Hpr : page_round_up (ms_gpr ms 1) = Z_to_bv 64 (page_round_up_Z len)).
    { unfold page_round_up. rewrite Hu1. reflexivity. }
    assert (H0 : ms_gpr ms 0 = a) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
    assert (Hargs : munmap_args_ok ms model).
    { unfold munmap_args_ok. rewrite H0, Hu1, Hpr. repeat split; try assumption.
      intro Hz. apply (f_equal bv_unsigned) in Hz. rewrite Hu1 in Hz.
      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hz. lia. }
    eapply (gg_munmap_raw mode Q ms model (getr regs 17));
      [exact Hh | exact Hlazy | reflexivity | rewrite H17; apply u64_lit; lia | exact Hargs |].
    unfold munmap_eff. rewrite H0, Hpr. unfold ms. rewrite adv_unmaps1_epend. exact Hc.
  Qed.

End G_AllocReplay.

(* [comment removed for export] *)
Ltac run_block_with HR HK fuel stops scr NX keep :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
    lazymatch type of HK with
    | know_ok ?segs _ ?M ?kn =>
      lazymatch goal with
      | |- realizes _ (mkCfg (mkst R (Z_to_bv 64 ?pc) M ?rom) ?model) ?T =>
        let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn NX) []) in
        lazymatch r with
        | (?ss', ?scs, ?scr') =>
          let c := eval vm_compute in (carry (s_log ss') kn []) in
          lazymatch c with
          | (?kn', ?scs2, ?hs2) =>
            eapply (rz_run segs fuel stops scr pc sr kn NX ss' scs scr' kn' scs2 hs2 E M rom R model T);
            (* [comment removed for export] *)
            [ vm_cast_no_check (@eq_refl _ (ss', scs, scr'))
            | vm_cast_no_check (@eq_refl _ (kn', scs2, hs2))
            | exact HR | exact HK
            | split_foralls
            | split_foralls
            | try reflexivity; try assumption
            | try reflexivity; try assumption
            | clear HR HK;
              let R' := fresh "R" in let M' := fresh "M" in let EQM := fresh "EQM" in
              intros R' M' HR HK EQM; cbn [s_pc s_regs s_log] in HR, EQM |- *;
              lazymatch keep with
              | true => idtac
              | false => clear EQM; try clear R; try clear M;
                         try rename R' into R; try rename M' into M
              end ]
          end
        end
      end
    end
  end.

Tactic Notation "run_block_gen" constr(fuel) constr(stops) constr(scr) constr(NX) constr(keep) :=
  match goal with
  | HR : regs_ok _ _ _, HK : know_ok _ _ _ _ |- _ => run_block_with HR HK fuel stops scr NX keep
  end.

Ltac gg_block_with HR HK fuel stops scr NX keep :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
    lazymatch type of HK with
    | know_ok ?segs _ ?M ?kn =>
      lazymatch goal with
      | |- GG _ ?mode ?Q ?T (mkCfg (mkst R (Z_to_bv 64 ?pc) M ?rom) ?model) =>
        let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn NX) []) in
        lazymatch r with
        | (?ss', ?scs, ?scr') =>
          let c := eval vm_compute in (carry (s_log ss') kn []) in
          lazymatch c with
          | (?kn', ?scs2, ?hs2) =>
            eapply (gg_run segs mode Q fuel stops scr pc sr kn NX ss' scs scr' kn' scs2 hs2 E M rom R model T);
            [ vm_cast_no_check (@eq_refl _ (ss', scs, scr'))
            | vm_cast_no_check (@eq_refl _ (kn', scs2, hs2))
            | exact HR | exact HK
            | split_foralls
            | split_foralls
            | try reflexivity; try assumption
            | try reflexivity; try assumption
            | clear HR HK;
              let R' := fresh "R" in let M' := fresh "M" in let EQM := fresh "EQM" in
              intros R' M' HR HK EQM; cbn [s_pc s_regs s_log] in HR, EQM |- *;
              lazymatch keep with
              | true => idtac
              | false => clear EQM; try clear R; try clear M;
                         try rename R' into R; try rename M' into M
              end ]
          end
        end
      end
    end
  end.

Tactic Notation "gg_block_gen" constr(fuel) constr(stops) constr(scr) constr(NX) constr(keep) :=
  match goal with
  | HR : regs_ok _ _ _, HK : know_ok _ _ _ _ |- _ => gg_block_with HR HK fuel stops scr NX keep
  end.
