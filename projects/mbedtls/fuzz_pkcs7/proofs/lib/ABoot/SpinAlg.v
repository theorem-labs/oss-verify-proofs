(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Mm.Mmap.   (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import
  SimInv ExitSim CatSim MmapSim ShapeAlg DivergeSim LazyFrame SymTac.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.


Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)

Inductive srealizes0 : config -> TSet -> Prop :=
| srz0_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                    (T : I -> TSet) (i0 : I),
    node_ok segs c I evs nx ->
    (forall i, srealizes0 (nx i) (T i)) ->
    srealizes0 c (t_alt (fun i => t_emit (evs i) (T i)))
| srz0_halt : forall c,
    m_halted (cfg_model c) <> None ->
    srealizes0 c t_nil
| srz0_spin : forall c,
    to_spin segs (cfg_ms c) (cfg_model c) ->
    m_halted (cfg_model c) = None ->
    srealizes0 c t_nil
| srz0_conseq : forall c T T',
    srealizes0 c T -> t_eq T T' -> srealizes0 c T'.

(* [comment removed for export] *)
#[using="Type"] Lemma srealizes0_of_realizes : forall c T,
  realizes segs c T -> srealizes0 c T.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq].
  - exact (srz0_node c I evs nx T i0 Hnode IH).
  - exact (srz0_halt c Hh).
  - exact (srz0_conseq c T T' IH Heq).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srz0_spinning : forall c, spinning segs c -> srealizes0 c t_nil.
Proof. intros c [Hspin Hh]. exact (srz0_spin c Hspin Hh). Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma srealizes0_nonempty : forall c T, srealizes0 c T -> T [].
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
                   | c Hspin Hh | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

#[using="Type"] Lemma srealizes0_pclosed : forall c T, srealizes0 c T ->
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

#[using="Type"] Lemma srealizes0_star_only : forall c T, srealizes0 c T ->
  forall tr c', star segs c tr c' -> T tr.
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
  - destruct (star_halted_nil segs c tr c' Hh Hstar) as [-> _]. reflexivity.
  - destruct c as [ms model]; cbn in Hspin, Hh.
    exact (spin_star_nil segs ms model tr c' Hspin Hh Hstar).
  - apply Heq. eapply IH; exact Hstar.
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma srealizes0_admits : forall c T, srealizes0 c T ->
  forall tr, T tr -> obs_trace segs c tr.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
                   | c Hspin Hh | c T T' H IH Heq];
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

(* [comment removed for export] *)
#[using="Type"] Theorem srealizes0_obs_iff : forall c T, srealizes0 c T ->
  forall tr, obs_trace segs c tr <-> T tr.
Proof.
  intros c T H tr. split.
  - intros (tr' & c' & Hstar & Hp).
    eapply srealizes0_pclosed;
      [exact H | eapply srealizes0_star_only; eauto | exact Hp].
  - apply srealizes0_admits; exact H.
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma srealizes0_step : forall c T e c',
  srealizes0 c T -> sstep segs c e (SNext c') -> exists T', srealizes0 c' T'.
Proof.
  intros c T e c' H; revert e c';
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
                   | c Hspin Hh | c T T' H IH Heq];
    intros e c' Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e (SNext c') Hss) as (i & _ & Heq2).
    inversion Heq2; subst c'. exists (T i). apply Hcont.
  - exfalso. apply Hh. eapply sstep_halted_none; exact Hss.
  - destruct (silent_loop_sstep segs (spinning segs) c e (SNext c')
                (spinning_silent_loop segs) (conj Hspin Hh) Hss)
      as (_ & c'' & Heq2 & Hsp').
    injection Heq2 as ->.
    exists t_nil. exact (srz0_spinning _ Hsp').
  - eapply IH; exact Hss.
Qed.

#[using="Type"] Lemma srealizes0_no_sserror : forall c T e,
  srealizes0 c T -> ~ sstep segs c e SError.
Proof.
  intros c T e H; revert e;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
                   | c Hspin Hh | c T T' H IH Heq];
    intros e Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate.
  - apply Hh. eapply sstep_halted_none; exact Hss.
  - destruct c as [ms model]; cbn in Hspin, Hh.
    exact (spin_no_sstep_error segs ms model Hspin Hh e Hss).
  - eapply IH; exact Hss.
Qed.

Definition srz0_path (c : config) : Prop := exists T, srealizes0 c T.

#[using="Type"] Theorem srealizes0_no_error : forall c T,
  srealizes0 c T -> ~ reaches_error segs c.
Proof.
  intros c T H.
  apply (inv_no_reaches_error segs srz0_path).
  - intros c1 e c2 (T1 & H1) Hss. eapply srealizes0_step; eauto.
  - intros c1 e (T1 & H1) Hss. eapply srealizes0_no_sserror; eauto.
  - exists T; exact H.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma srz0_silent1 : forall c c' T,
  node_ok segs c unit (fun _ => []) (fun _ => c') ->
  srealizes0 c' T ->
  srealizes0 c T.
Proof.
  intros c c' T Hnode Hc.
  apply (srz0_conseq c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (srz0_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode).
    intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply srealizes0_nonempty; exact Hc ].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srz0_emit1 : forall c c' e T,
  node_ok segs c unit (fun _ => e) (fun _ => c') ->
  srealizes0 c' T ->
  srealizes0 c (t_emit e T).
Proof.
  intros c c' e T Hnode Hc.
  apply (srz0_conseq c (t_alt (fun _ : unit => t_emit e T))).
  - apply (srz0_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode).
    intros []; exact Hc.
  - apply t_alt_unit.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srz0_alt2 : forall c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet)
                        (a0 : IA) (b0 : IB),
  node_ok segs c (IA + IB) (fun _ => []) nx ->
  (forall i, srealizes0 (nx (inl i)) A) ->
  (forall i, srealizes0 (nx (inr i)) B) ->
  srealizes0 c (t_alt2 A B).
Proof.
  intros c IA IB nx A B a0 b0 Hnode HA HB.
  assert (HA0 : A []) by (eapply srealizes0_nonempty; apply (HA a0)).
  assert (HB0 : B []) by (eapply srealizes0_nonempty; apply (HB b0)).
  apply (srz0_conseq c
    (t_alt (fun i : IA + IB =>
              t_emit [] (match i with inl _ => A | inr _ => B end)))).
  - apply (srz0_node c (IA + IB) (fun _ => []) nx
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

(* [comment removed for export] *)
#[using="Type"] Lemma srz0_step : forall ms model ms' T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  srealizes0 (mkCfg ms' model) T ->
  srealizes0 (mkCfg ms model) T.
Proof.
  intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
  eapply srz0_silent1; [apply node_instr; eassumption | exact Hc].
Qed.

#[using="Type"] Lemma srz0_msteps : forall ms ms' model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  srealizes0 (mkCfg ms' model) T ->
  srealizes0 (mkCfg ms model) T.
Proof.
  intros ms ms' model T Hh Hlazy Hms;
    induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH];
    intro Hc; [exact Hc|].
  eapply srz0_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
                   | apply IH; exact Hc].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma node_instr_disjoint : forall ms model ms' ranges,
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

#[using="Type"] Lemma srz0_step_disjoint : forall ms model ms' ranges T,
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms
    = MachineOk (@mkAccessReport machine_state ms' ranges) ->
  accesses_outside_lazy ranges (m_vm_lazy model) ->
  srealizes0 (mkCfg ms' model) T ->
  srealizes0 (mkCfg ms model) T.
Proof.
  intros ms model ms' ranges T Hh Hsvc Hstep Hout Hc.
  eapply srz0_silent1; [eapply node_instr_disjoint; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srz0_write1 : forall ms model x8 buf T,
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
     srealizes0 (mkCfg (advance_past_svc
                         (set_gpr0 ms (len_word (firstn n buf)))) model) T) ->
  srealizes0 (mkCfg ms model) (t_write_ch (Z_to_bv 64 1) buf T).
Proof.
  intros ms model x8 buf T Hh Hlazy Hfd Hsvc Hno Hg Hr Hbm Hnb Hc.
  unfold t_write_ch.
  apply (srz0_node (mkCfg ms model) (wr_index buf)
           (fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) buf))
           (fun i => mkCfg (advance_past_svc
                              (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                           model)
           (fun _ => T) (wr_full buf Hnb)).
  - apply (node_write1 segs ms model x8 buf); assumption.
  - intros [n [Hn1 Hn2]]. cbn [proj1_sig]. apply Hc; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srz0_exit : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  srealizes0 (mkCfg ms model)
            (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros ms model x8 Hh Hsvc Hx8.
  apply srealizes0_of_realizes. apply (rz_exit segs ms model x8); assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma node_munmap : forall ms model x8,
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

#[using="Type"] Lemma srz0_munmap : forall ms model x8 T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  srealizes0 (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                   (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) T ->
  srealizes0 (mkCfg ms model) T.
Proof.
  intros ms model x8 T Hh Hlazy Hsvc Hno Hargs Hc.
  eapply srz0_silent1; [apply (node_munmap ms model x8); assumption | exact Hc].
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
#[using="Type"] Lemma srz0_mmap : forall ms model x8 A B,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  (forall e, In e mmap_errnos ->
     srealizes0 (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) A) ->
  (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
     srealizes0 (mkCfg (advance_past_svc
                        (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                      (mmap_model a (page_round_up (ms_gpr ms 1)) model)) B) ->
  (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
  srealizes0 (mkCfg ms model) (t_alt2 A B).
Proof.
  intros ms model x8 A B Hh Hlazy Hsvc Hno Hargs HA HB Hex.
  destruct Hex as [a0 Ha0].
  eapply (srz0_alt2 (mkCfg ms model)
            {e : Z | In e mmap_errnos}
            {a : word | grant_ok (ms_gpr ms 0) model a
                          (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true}
            _ A B
            (exist _ ENOMEM ENOMEM_in_mmap_errnos) (exist _ a0 Ha0)).
  - apply (node_mmap ms model x8); assumption.
  - intros [e He]; cbn. apply HA; exact He.
  - intros [a Ha]; cbn. apply HB; exact Ha.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srz0_mmap_spin : forall ms model x8 B,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  (forall e, In e mmap_errnos ->
     to_spin segs (advance_past_svc (set_gpr0 ms (errno_ret e))) model) ->
  (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
     srealizes0 (mkCfg (advance_past_svc
                        (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                      (mmap_model a (page_round_up (ms_gpr ms 1)) model)) B) ->
  (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
  srealizes0 (mkCfg ms model) B.
Proof.
  intros ms model x8 B Hh Hlazy Hsvc Hno Hargs Hspin HB Hex.
  destruct Hex as [a0 Ha0].
  assert (HB0 : B []) by (eapply srealizes0_nonempty; apply (HB a0 Ha0)).
  eapply srz0_conseq.
  { apply (srz0_node (mkCfg ms model)
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
    - intros [[e He] | [a Ha]]; cbn.
      + apply srz0_spin; cbn; [apply Hspin; exact He | exact Hh].
      + apply HB; exact Ha. }
  (* [comment removed for export] *)
  intro tr. split.
  - intros [[[e He] | [a Ha]] Hi]; cbn in Hi.
    + apply (t_emit_nil_eq t_nil eq_refl tr) in Hi.
      unfold t_nil in Hi. subst tr. exact HB0.
    + exact (proj1 (t_emit_nil_eq B HB0 tr) Hi).
  - intro HBtr. exists (inr (exist _ a0 Ha0)).
    exact (proj2 (t_emit_nil_eq B HB0 tr) HBtr).
Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fo_step (c : config) (e : list event) (c' : config) : Prop :=
  sstep_cfg segs forced_only_cfg c e (SNext c').

Inductive srealizes : config -> TSet -> Prop :=
| srz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                    (T : I -> TSet) (i0 : I),
    node_ok segs c I evs nx ->
    (forall i, srealizes (nx i) (T i)) ->
    srealizes c (t_alt (fun i => t_emit (evs i) (T i)))
| srz_halt : forall c,
    m_halted (cfg_model c) <> None ->
    srealizes c t_nil
| srz_node_sp : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                       (T : I -> TSet) (i0 : I),
    node_ok segs c I evs nx ->
    (forall i, srealizes (nx i) (T i)
               \/ (srealizes0 (nx i) (T i) /\ ~ fo_step c (evs i) (nx i))) ->
    srealizes c (t_alt (fun i => t_emit (evs i) (T i)))
| srz_conseq : forall c T T',
    srealizes c T -> t_eq T T' -> srealizes c T'.

(* [comment removed for export] *)
#[using="Type"] Lemma srealizes_ind2 : forall (P : config -> TSet -> Prop),
  (forall c (I : Type) (evs : I -> list event) (nx : I -> config) (T : I -> TSet) (i0 : I),
      node_ok segs c I evs nx -> (forall i, srealizes (nx i) (T i)) -> (forall i, P (nx i) (T i)) ->
      P c (t_alt (fun i => t_emit (evs i) (T i)))) ->
  (forall c, m_halted (cfg_model c) <> None -> P c t_nil) ->
  (forall c (I : Type) (evs : I -> list event) (nx : I -> config) (T : I -> TSet) (i0 : I),
      node_ok segs c I evs nx ->
      (forall i, (srealizes (nx i) (T i) /\ P (nx i) (T i))
                 \/ (srealizes0 (nx i) (T i) /\ ~ fo_step c (evs i) (nx i))) ->
      P c (t_alt (fun i => t_emit (evs i) (T i)))) ->
  (forall c T T', srealizes c T -> P c T -> t_eq T T' -> P c T') ->
  forall c T, srealizes c T -> P c T.
Proof.
  intros P Hnode Hhalt Hsp Hconseq.
  fix IH 3. intros c T H.
  destruct H as [c I evs nx T i0 Hn Hk | c Hh | c I evs nx T i0 Hn Hk | c T T' H Heq].
  - apply (Hnode c I evs nx T i0 Hn Hk). intros i. exact (IH _ _ (Hk i)).
  - apply Hhalt. exact Hh.
  - apply (Hsp c I evs nx T i0 Hn). intros i. destruct (Hk i) as [Hl | Hr].
    + left. split; [exact Hl | exact (IH _ _ Hl)].
    + right. exact Hr.
  - apply (Hconseq c T T' H (IH _ _ H) Heq).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srealizes_srealizes0 : forall c T, srealizes c T -> srealizes0 c T.
Proof.
  apply srealizes_ind2.
  - intros c I evs nx T i0 Hn _ IH. exact (srz0_node c I evs nx T i0 Hn IH).
  - intros c Hh. exact (srz0_halt c Hh).
  - intros c I evs nx T i0 Hn Hk. apply (srz0_node c I evs nx T i0 Hn).
    intros i. destruct (Hk i) as [[_ IH] | [H0 _]]; [exact IH | exact H0].
  - intros c T T' _ IH Heq. exact (srz0_conseq c T T' IH Heq).
Qed.

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
#[using="Type"] Lemma srz_node_excused : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                        (T : I -> TSet) (i0 : I) (live : I -> Prop),
  node_ok segs c I evs nx ->
  (forall i, live i -> srealizes (nx i) (T i)) ->
  (forall i, ~ live i -> srealizes0 (nx i) (T i) /\ ~ fo_step c (evs i) (nx i)) ->
  (forall i, live i \/ ~ live i) ->
  srealizes c (t_alt (fun i => t_emit (evs i) (T i))).
Proof.
  intros c I evs nx T i0 live Hn HL HE Hdec.
  apply (srz_node_sp c I evs nx T i0 Hn). intros i.
  destruct (Hdec i) as [Hi | Hi]; [left; exact (HL i Hi) | right; exact (HE i Hi)].
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma srealizes_nonempty : forall c T, srealizes c T -> T [].
Proof. intros c T H. exact (srealizes0_nonempty c T (srealizes_srealizes0 c T H)). Qed.

#[using="Type"] Lemma srealizes_pclosed : forall c T, srealizes c T ->
  forall tr tr', T tr -> is_prefix tr' tr -> T tr'.
Proof. intros c T H. exact (srealizes0_pclosed c T (srealizes_srealizes0 c T H)). Qed.

#[using="Type"] Lemma srealizes_star_only : forall c T, srealizes c T ->
  forall tr c', star segs c tr c' -> T tr.
Proof. intros c T H. exact (srealizes0_star_only c T (srealizes_srealizes0 c T H)). Qed.

#[using="Type"] Lemma srealizes_admits : forall c T, srealizes c T ->
  forall tr, T tr -> obs_trace segs c tr.
Proof. intros c T H. exact (srealizes0_admits c T (srealizes_srealizes0 c T H)). Qed.

#[using="Type"] Theorem srealizes_obs_iff : forall c T, srealizes c T ->
  forall tr, obs_trace segs c tr <-> T tr.
Proof. intros c T H. exact (srealizes0_obs_iff c T (srealizes_srealizes0 c T H)). Qed.

#[using="Type"] Theorem srealizes_no_error : forall c T,
  srealizes c T -> ~ reaches_error segs c.
Proof. intros c T H. exact (srealizes0_no_error c T (srealizes_srealizes0 c T H)). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma family_off_alloc : forall i,
  (bv_unsigned (in_sysno i) = 214 \/ bv_unsigned (in_sysno i) = 216 \/ bv_unsigned (in_sysno i) = 222 \/ bv_unsigned (in_sysno i) = 226)%Z ->
  injected_family_off forced_only_cfg i = true.
Proof. intros i [H|[H|[H|H]]]; unfold injected_family_off; rewrite H; reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma refusal_b_mmap : forall i m r,
  bv_unsigned (in_sysno i) = 222%Z -> refusal_b i m r = errno_ret_in mmap_errnos r.
Proof. intros i m r H. unfold refusal_b. rewrite H. reflexivity. Qed.

#[using="Type"] Lemma refusal_b_mprotect : forall i m r,
  bv_unsigned (in_sysno i) = 226%Z -> refusal_b i m r = errno_ret_in mprotect_errnos r.
Proof. intros i m r H. unfold refusal_b. rewrite H. reflexivity. Qed.

#[using="Type"] Lemma ms_gpr0_advance_apply_effect : forall ms eff,
  ms_gpr (advance_past_svc (apply_effect ms eff)) 0 = eff_ret eff.
Proof.
  intros ms eff. unfold ms_gpr, advance_past_svc, apply_effect, set_reg.
  replace (bv_eqb (10 : reg) 0) with false by (vm_compute; reflexivity).
  cbn -[Z.add Z.of_nat bvmap_set bvmap_get].
  replace (Z_to_bv 5 (10 + Z.of_nat 0)) with (10 : reg) by (apply bv_eq; vm_compute; reflexivity).
  unfold reg_get. rewrite bvmap_get_set_same. reflexivity.
Qed.

#[using="Type"] Lemma refusal_not_fo_step : forall ms model x8 eff' model' evs' c',
  ms_svc_pending ms = Some x8 ->
  injected_family_off forced_only_cfg (sys_input segs ms x8) = true ->
  syscall_spec (sys_input segs ms x8) model (Ok eff' model' evs') ->
  refusal_b (sys_input segs ms x8) model (eff_ret eff') = false ->
  refusal_b (sys_input segs ms x8) model (ms_gpr (cfg_ms c') 0) = true ->
  ~ fo_step (mkCfg ms model) [] c'.
Proof.
  intros ms model x8 eff' model' evs' c' Hsvc Hoff Hspec Hnr Hr Hst.
  unfold fo_step in Hst. inversion Hst; subst.
  - (* [comment removed for export] *) congruence.
  - (* [comment removed for export] *)
    match goal with
    | Hx : ms_svc_pending ms = Some ?x0, Hns : ~ spurious_refusal_cfg _ _ _ ?eff |- _ =>
        assert (Ex : x0 = x8) by congruence; subst x0;
        apply Hns; split; [exact Hoff | split; [| exists eff', model', evs'; split; [exact Hspec | exact Hnr]]]
    end.
    cbn [cfg_ms] in Hr. rewrite ms_gpr0_advance_apply_effect in Hr. exact Hr.
  - (* [comment removed for export] *)
    match goal with H : _ ++ _ = [] |- _ => apply app_eq_nil in H; destruct H as [_ H]; discriminate H end.
  - (* [comment removed for export] *)
    match goal with H : _ ++ _ = [] |- _ => apply app_eq_nil in H; destruct H as [_ H]; discriminate H end.
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma srz_silent1 : forall c c' T,
  node_ok segs c unit (fun _ => []) (fun _ => c') ->
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

#[using="Type"] Lemma srz_emit1 : forall c c' e T,
  node_ok segs c unit (fun _ => e) (fun _ => c') ->
  srealizes c' T ->
  srealizes c (t_emit e T).
Proof.
  intros c c' e T Hnode Hc.
  apply (srz_conseq c (t_alt (fun _ : unit => t_emit e T))).
  - apply (srz_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode).
    intros []; exact Hc.
  - apply t_alt_unit.
Qed.

#[using="Type"] Lemma srz_alt2 : forall c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet)
                        (a0 : IA) (b0 : IB),
  node_ok segs c (IA + IB) (fun _ => []) nx ->
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

#[using="Type"] Lemma srz_mmap : forall ms model x8 A B,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  (forall e, In e mmap_errnos ->
     srealizes (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) A) ->
  (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
     srealizes (mkCfg (advance_past_svc
                        (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                      (mmap_model a (page_round_up (ms_gpr ms 1)) model)) B) ->
  (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
  srealizes (mkCfg ms model) (t_alt2 A B).
Proof.
  intros ms model x8 A B Hh Hlazy Hsvc Hno Hargs HA HB Hex.
  destruct Hex as [a0 Ha0].
  eapply (srz_alt2 (mkCfg ms model)
            {e : Z | In e mmap_errnos}
            {a : word | grant_ok (ms_gpr ms 0) model a
                          (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true}
            _ A B
            (exist _ ENOMEM ENOMEM_in_mmap_errnos) (exist _ a0 Ha0)).
  - apply (node_mmap ms model x8); assumption.
  - intros [e He]; cbn. apply HA; exact He.
  - intros [a Ha]; cbn. apply HB; exact Ha.
Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma srz_mmap_spin : forall ms model x8 B,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  (forall e, In e mmap_errnos ->
     to_spin segs (advance_past_svc (set_gpr0 ms (errno_ret e))) model) ->
  (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
     srealizes (mkCfg (advance_past_svc
                        (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                      (mmap_model a (page_round_up (ms_gpr ms 1)) model)) B) ->
  (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
  srealizes (mkCfg ms model) B.
Proof.
  intros ms model x8 B Hh Hlazy Hsvc Hno Hargs Hspin HB Hex.
  destruct Hex as [a0 Ha0].
  assert (HB0 : B []) by (eapply srealizes_nonempty; apply (HB a0 Ha0)).
  set (n := page_round_up (ms_gpr ms 1)).
  (* [comment removed for export] *)
  assert (Hgrant : syscall_spec (sys_input segs ms x8) model
                     (Ok (mkEffect a0 [] [(a0, n)]) (mmap_model a0 n model) [])).
  { apply mmap_succ_ok; assumption. }
  assert (Hoff : injected_family_off forced_only_cfg (sys_input segs ms x8) = true).
  { apply (family_off_alloc (sys_input segs ms x8)). cbn [in_sysno sys_input]. rewrite Hno. right; right; left; reflexivity. }
  assert (Hnr : refusal_b (sys_input segs ms x8) model (eff_ret (mkEffect a0 [] [(a0, n)])) = false).
  { rewrite (refusal_b_mmap (sys_input segs ms x8) model) by (cbn [in_sysno sys_input]; exact Hno). cbn [eff_ret].
    apply (grant_not_errno (ms_gpr ms 0) model a0 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))));
      [apply page_round_up_Z_nonneg; pose proof (bv_unsigned_in_range 64 (ms_gpr ms 1)); lia | exact Ha0]. }
  eapply srz_conseq.
  { apply (srz_node_sp (mkCfg ms model)
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
    - intros [[e He] | [a Ha]]; cbn.
      + right. split.
        * apply srz0_spin; cbn; [apply Hspin; exact He | exact Hh].
        * eapply (refusal_not_fo_step ms model x8); [exact Hsvc | exact Hoff | exact Hgrant | exact Hnr |].
          cbn [cfg_ms]. rewrite <- (apply_effect_no_write ms (errno_ret e)). rewrite ms_gpr0_advance_apply_effect. cbn [eff_ret].
          rewrite (refusal_b_mmap (sys_input segs ms x8) model) by (cbn [in_sysno sys_input]; exact Hno).
          apply errno_ret_in_intro. exact He.
      + left. apply HB; exact Ha. }
  (* [comment removed for export] *)
  intro tr. split.
  - intros [[[e He] | [a Ha]] Hi]; cbn in Hi.
    + apply (t_emit_nil_eq t_nil eq_refl tr) in Hi.
      unfold t_nil in Hi. subst tr. exact HB0.
    + exact (proj1 (t_emit_nil_eq B HB0 tr) Hi).
  - intro HBtr. exists (inr (exist _ a0 Ha0)).
    exact (proj2 (t_emit_nil_eq B HB0 tr) HBtr).
Qed.

End WithSegs.

(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem spin_shape_strong_equiv : forall source_segs rpc rph rsp rbrk rmb (rrnd : EntryDraw) (rlim : Z)
         target_segs apc aph asp abrk amb (arnd : EntryDraw) (alim : Z)
         (T : TSet) (inp : ProcInput),
  srealizes source_segs
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  srealizes target_segs
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T ->
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
    rewrite (srealizes_obs_iff source_segs _ T Hsource tr).
    rewrite (srealizes_obs_iff target_segs _ T Htarget tr).
    reflexivity.
  - cbn. eapply srealizes_no_error; exact Htarget.
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

(* [comment removed for export] *)

(* [comment removed for export] *)
Corollary srz_spin_alloc_writes : forall segs ms0 ms model x8 bs cs,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  msteps segs ms0 ms ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  (forall e, In e mmap_errnos ->
     to_spin segs (advance_past_svc (set_gpr0 ms (errno_ret e))) model) ->
  (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
     MmapSim.twm segs
       (advance_past_svc
          (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
       (mmap_model a (page_round_up (ms_gpr ms 1)) model) bs cs) ->
  (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
  bufs_modeled bs ->
  srealizes segs (mkCfg ms0 model) (t_writes bs (t_exit cs (m_fs model))).
Proof.
  intros segs ms0 ms model x8 bs cs Hh Hlazy Hfd Hms Hsvc Hno Hargs
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

(* [comment removed for export] *)

(* [comment removed for export] *)
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
(* [comment removed for export] *)
Hypothesis Hrefuse : forall e, In e mmap_errnos ->
  to_spin segs (advance_past_svc (set_gpr0 ms (errno_ret e))) model.
(* [comment removed for export] *)
Hypothesis Hgrant : forall a,
  grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
  MmapSim.twm segs
    (advance_past_svc
       (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
    (mmap_model a (page_round_up (ms_gpr ms 1)) model) bs cs.
Hypothesis Hex : exists a,
  grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true.
Hypothesis Hbs : bufs_modeled bs.

(* [comment removed for export] *)
#[using="x8 Hh Hlazy Hfd Hsvc Hno Hargs Hrefuse Hgrant Hex Hbs"] Theorem spin_branch_node_srealizes :
  srealizes segs (mkCfg ms model) (t_writes bs (t_exit cs (m_fs model))).
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

(* [comment removed for export] *)
#[using="x8 Hh Hlazy Hfd Hsvc Hno Hargs Hrefuse Hgrant Hex Hbs"] Theorem spin_branch_node_obs_iff : forall tr,
  obs_trace segs (mkCfg ms model) tr
  <-> is_prefix tr (wevents bs ++ [ExitEv cs (m_fs model)]).
Proof.
  intro tr.
  rewrite (srealizes_obs_iff segs _ _ spin_branch_node_srealizes tr).
  apply t_writes_exit_iff.
Qed.

(* [comment removed for export] *)
#[using="x8 bs cs Hh Hlazy Hfd Hsvc Hno Hargs Hrefuse Hgrant Hex Hbs"] Theorem spin_branch_node_no_error : ~ reaches_error segs (mkCfg ms model).
Proof.
  exact (srealizes_no_error segs _ _ spin_branch_node_srealizes).
Qed.

End SpinBranchReal.
