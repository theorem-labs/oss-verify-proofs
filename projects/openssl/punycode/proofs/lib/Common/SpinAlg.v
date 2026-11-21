(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (srealizes nodes and srz_silent1, srz_emit1, srz_alt2 and srz_silent_all take a RomBase.sys_rob premise, discharged at the instruction, write, munmap and mmap nodes; srz_write1 takes an access_ok premise; node_munmap removed and srz_munmap goes through node_munmap_cut with an errno continuation; srz_mmap takes a place_declined_b premise). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import
  SimInv ExitSim CatSim MmapSim ShapeAlg DivergeSim LazyFrame SymTac CfgStep.
From OSSVerify.Proofs.openssl.punycode.lib.Common.Cfg Require RomBase RomWrite.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)

Inductive srealizes : config -> TSet -> Prop :=
| srz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                    (T : I -> TSet) (i0 : I),
    node_ok segs c I evs nx ->
    RomBase.sys_rob segs c ->   (* LPS 08b1429: the node's syscall reads the same over a larger backing *)
    (forall i, srealizes (nx i) (T i)) ->
    srealizes c (t_alt (fun i => t_emit (evs i) (T i)))
| srz_halt : forall c,
    m_halted (cfg_model c) <> None ->
    srealizes c t_nil
    (* [comment removed for export] *)
| srz_conseq : forall c T T',
    srealizes c T -> t_eq T T' -> srealizes c T'.

(* [comment removed for export] *)
Lemma srealizes_of_realizes : forall c T,
  realizes segs c T -> srealizes c T.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq].
  - exact (srz_node c I evs nx T i0 Hnode Hrob IH).
  - exact (srz_halt c Hh).
  - exact (srz_conseq c T T' IH Heq).
Qed.

(* [comment removed for export] *)
Lemma realizes_of_srealizes : forall c T,
  srealizes c T -> realizes segs c T.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq].
  - exact (rz_node segs c I evs nx T i0 Hnode Hrob IH).
  - exact (rz_halt segs c Hh).
  - exact (rz_conseq segs c T T' IH Heq).
Qed.

(* [comment removed for export] *)

Lemma srealizes_nonempty : forall c T, srealizes c T -> T [].
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh
                   | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

Lemma srealizes_pclosed : forall c T, srealizes c T ->
  forall tr tr', T tr -> is_prefix tr' tr -> T tr'.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh
                   | c T T' H IH Heq];
    intros tr tr' HT Hp.
  - destruct HT as [i [Hpre | (tr0 & -> & HT0)]]; exists i.
    + left. eapply is_prefix_trans; eauto.
    + apply is_prefix_app_split in Hp as [Hp | (tr0' & -> & Hp)].
      * left. exact Hp.
      * right. exists tr0'. split; [reflexivity | eapply IH; eauto].
  - unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
  - apply Heq. eapply IH; [apply Heq; exact HT | exact Hp].
Qed.

(* [comment removed for export] *)

Lemma srealizes_star_only : forall c T, srealizes c T ->
  forall tr c', star_cfg segs kit_cfg c tr c' -> T tr.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh
                   | c T T' H IH Heq];
    intros tr c' Hstar.
  - inversion Hstar as [|c1 e c2 tr2 c3 Hss Hstar2]; subst.
    + exists i0. left. apply is_prefix_nil.
    + destruct Hnode as [_ Hsound].
      destruct (Hsound e (SNext c2) Hss) as (i & -> & Heq2).
      inversion Heq2; subst c2.
      exists i. right. exists tr2.
      split; [reflexivity | eapply IH; exact Hstar2].
  - destruct (star_cfg_halted_nil segs c tr c' Hh Hstar) as [-> _]. reflexivity.
  - apply Heq. eapply IH; exact Hstar.
Qed.

(* [comment removed for export] *)

Lemma srealizes_admits : forall c T, srealizes c T ->
  forall tr, T tr -> obs_trace_cfg segs kit_cfg c tr.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh
                   | c T T' H IH Heq];
    intros tr HT.
  - destruct Hnode as [Hcomp _].
    destruct HT as [i [Hpre | (tr0 & -> & HT0)]].
    + exists (evs i), (nx i). split; [apply star_cfg_one; apply Hcomp | exact Hpre].
    + destruct (IH i tr0 HT0) as (tr'' & c'' & Hstar & Hp).
      exists (evs i ++ tr''), c''.
      split; [eapply star_cfg_step; [apply Hcomp | exact Hstar]
             | apply is_prefix_app_mono; exact Hp].
  - unfold t_nil in HT; subst tr. apply obs_trace_cfg_nil.
  - apply IH. apply Heq. exact HT.
Qed.

(* [comment removed for export] *)
Theorem srealizes_obs_iff : forall c T, srealizes c T ->
  forall tr, obs_trace_cfg segs kit_cfg c tr <-> T tr.
Proof.
  intros c T H tr. split.
  - intros (tr' & c' & Hstar & Hp).
    eapply srealizes_pclosed;
      [exact H | eapply srealizes_star_only; eauto | exact Hp].
  - apply srealizes_admits; exact H.
Qed.

(* [comment removed for export] *)

Lemma srealizes_step : forall c T e c',
  srealizes c T -> sstep_cfg segs kit_cfg c e (SNext c') -> exists T', srealizes c' T'.
Proof.
  intros c T e c' H; revert e c';
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh
                   | c T T' H IH Heq];
    intros e c' Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e (SNext c') Hss) as (i & _ & Heq2).
    inversion Heq2; subst c'. exists (T i). apply Hcont.
  - exfalso. apply Hh. eapply sstep_cfg_halted_none; exact Hss.
  - eapply IH; exact Hss.
Qed.

Lemma srealizes_no_sserror : forall c T e,
  srealizes c T -> ~ sstep_cfg segs kit_cfg c e SError.
Proof.
  intros c T e H; revert e;
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh
                   | c T T' H IH Heq];
    intros e Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate.
  - apply Hh. eapply sstep_cfg_halted_none; exact Hss.
  - eapply IH; exact Hss.
Qed.

Definition srz_path (c : config) : Prop := exists T, srealizes c T.

Theorem srealizes_no_error : forall c T,
  srealizes c T -> ~ reaches_error_cfg segs kit_cfg c.
Proof.
  intros c T H.
  apply (inv_no_reaches_error_cfg segs srz_path).
  - intros c1 e c2 (T1 & H1) Hss. eapply srealizes_step; eauto.
  - intros c1 e (T1 & H1) Hss. eapply srealizes_no_sserror; eauto.
  - exists T; exact H.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma srz_silent1 : forall c c' T,
  node_ok segs c unit (fun _ => []) (fun _ => c') ->
  RomBase.sys_rob segs c ->
  srealizes c' T ->
  srealizes c T.
Proof.
  intros c c' T Hnode Hrob Hc.
  apply (srz_conseq c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (srz_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode Hrob).
    intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply srealizes_nonempty; exact Hc ].
Qed.

(* [comment removed for export] *)
Lemma srz_emit1 : forall c c' e T,
  node_ok segs c unit (fun _ => e) (fun _ => c') ->
  RomBase.sys_rob segs c ->
  srealizes c' T ->
  srealizes c (t_emit e T).
Proof.
  intros c c' e T Hnode Hrob Hc.
  apply (srz_conseq c (t_alt (fun _ : unit => t_emit e T))).
  - apply (srz_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode Hrob).
    intros []; exact Hc.
  - apply t_alt_unit.
Qed.

(* [comment removed for export] *)
Lemma srz_alt2 : forall c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet)
                        (a0 : IA) (b0 : IB),
  node_ok segs c (IA + IB) (fun _ => []) nx ->
  RomBase.sys_rob segs c ->
  (forall i, srealizes (nx (inl i)) A) ->
  (forall i, srealizes (nx (inr i)) B) ->
  srealizes c (t_alt2 A B).
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
  - intro tr. unfold t_alt2. split.
    + intros [[i|i] Hi];
        [ left; exact (proj1 (t_emit_nil_eq A HA0 tr) Hi)
        | right; exact (proj1 (t_emit_nil_eq B HB0 tr) Hi) ].
    + intros [H | H];
        [ exists (inl a0); exact (proj2 (t_emit_nil_eq A HA0 tr) H)
        | exists (inr b0); exact (proj2 (t_emit_nil_eq B HB0 tr) H) ].
Qed.

(* [comment removed for export] *)
Lemma srz_silent_all : forall c (I : Type) (nx : I -> config) (B : TSet) (i0 : I),
  node_ok segs c I (fun _ => []) nx ->
  RomBase.sys_rob segs c ->
  (forall i, srealizes (nx i) B) ->
  srealizes c B.
Proof.
  intros c I nx B i0 Hnode Hrob HB.
  assert (HB0 : B []) by (eapply srealizes_nonempty; apply (HB i0)).
  apply (srz_conseq c (t_alt (fun _ : I => t_emit [] B))).
  - apply (srz_node c I (fun _ => []) nx (fun _ => B) i0 Hnode Hrob HB).
  - intro tr. split.
    + intros [i Hi]. exact (proj1 (t_emit_nil_eq B HB0 tr) Hi).
    + intro H. exists i0. exact (proj2 (t_emit_nil_eq B HB0 tr) H).
Qed.

(* [comment removed for export] *)
Lemma srz_step : forall ms model ms' T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  srealizes (mkCfg ms' model) T ->
  srealizes (mkCfg ms model) T.
Proof.
  intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
  eapply srz_silent1; [apply node_instr; eassumption | apply RomBase.sys_rob_instr; exact Hsvc | exact Hc].
Qed.

Lemma srz_msteps : forall ms ms' model T,
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
  apply node_ok_of_u; [kit_pending_on |].
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
  eapply rz_silent1; [eapply node_instr_disjoint; eassumption | apply RomBase.sys_rob_instr; exact Hsvc | exact Hc].
Qed.

Lemma srz_step_disjoint : forall ms model ms' ranges T,
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms
    = MachineOk (@mkAccessReport machine_state ms' ranges) ->
  accesses_outside_lazy ranges (m_vm_lazy model) ->
  srealizes (mkCfg ms' model) T ->
  srealizes (mkCfg ms model) T.
Proof.
  intros ms model ms' ranges T Hh Hsvc Hstep Hout Hc.
  eapply srz_silent1; [eapply node_instr_disjoint; eassumption | apply RomBase.sys_rob_instr; exact Hsvc | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma srz_write1 : forall ms model x8 buf T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  (* the range [vfs_write]'s [access_ok] accepts; see [CatSim.write1_check_n] *)
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     srealizes (mkCfg (advance_past_svc
                         (set_gpr0 ms (len_word (firstn n buf)))) model) T) ->
  srealizes (mkCfg ms model) (t_write_ch (Z_to_bv 64 1) buf T).
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
  - eapply RomWrite.write1_rob; eassumption.
  - intros [n [Hn1 Hn2]]. cbn [proj1_sig]. apply Hc; assumption.
Qed.

(* [comment removed for export] *)
Lemma srz_exit : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  srealizes (mkCfg ms model)
            (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros ms model x8 Hh Hsvc Hx8.
  apply srealizes_of_realizes. apply (rz_exit segs ms model x8); assumption.
Qed.

(* At the revision munmap (215) may also answer an injected munmap_errnos;
   under [kit_cfg] that is a spurious refusal, so the kit's node has only the
   cut child ([ShapeAlg.node_munmap_cut]).  [srz_munmap] keeps its errno
   premise (a stronger premise; no caller loses anything) and no longer
   needs it. *)
Lemma srz_munmap : forall ms model x8 T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  (forall e, In e munmap_errnos ->
     srealizes (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) T) ->
  srealizes (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                   (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) T ->
  srealizes (mkCfg ms model) T.
Proof.
  intros ms model x8 T Hh Hlazy Hsvc Hno Hargs _ Hc.
  apply (srz_silent_all (mkCfg ms model) unit
           (fun _ => mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                           (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model))
           T tt);
    [exact (node_munmap_cut segs ms model x8 Hh Hlazy Hsvc Hno Hargs)
    | eapply RomBase.sys_rob_memfree; [exact Hsvc | rewrite Hno; exact RomBase.memfree_215] |].
  intros []. exact Hc.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma srz_mmap : forall ms model x8 B,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
     srealizes (mkCfg (advance_past_svc
                        (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                      (mmap_model a (page_round_up (ms_gpr ms 1)) model)) B) ->
  (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
  srealizes (mkCfg ms model) B.
Proof.
  intros ms model x8 B Hh Hlazy Hsvc Hno Hargs Hdecl HB Hex.
  pose proof (node_mmap segs ms model x8 Hh Hlazy Hsvc Hno Hargs Hdecl Hex) as Hnode.
  destruct Hex as [a0 Ha0].
  assert (HB0 : B []) by (eapply srealizes_nonempty; apply (HB a0 Ha0)).
  eapply srz_conseq.
  { eapply (srz_node (mkCfg ms model) _ _ _ (fun _ => B) (exist _ a0 Ha0) Hnode
             (RomBase.sys_rob_memfree segs ms model x8 Hsvc ltac:(rewrite Hno; exact RomBase.memfree_222))).
    intros [a Ha]. apply HB; exact Ha. }
  intro tr. split.
  - intros [i Hi]. exact (proj1 (t_emit_nil_eq B HB0 tr) Hi).
  - intro H. exists (exist _ a0 Ha0). exact (proj2 (t_emit_nil_eq B HB0 tr) H).
Qed.

(* [comment removed for export] *)
Definition srz_mmap_spin := srz_mmap.

End WithSegs.

(* [comment removed for export] *)

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

(* [comment removed for export] *)
