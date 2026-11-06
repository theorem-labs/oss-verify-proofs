(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c5 X1by X1br X1bo X1bs X1c2 X1c6 X1bq.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Common Require Import CfgStep.
Import ListNotations.
Open Scope bv_scope.

Definition prog_tree (R : Type) : Type := ProcInput -> ExecEntry -> itree node R.

Definition ms0 (segs : list Segment) (pc : N) (ph : PhdrInfo)
(en : ExecEntry) (inp : ProcInput) : machine_state :=
init_ms segs pc ph (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en).

Definition ms0F (segs : list Segment) (pc : N) (ph : PhdrInfo)
(en : ExecEntry) (inp : ProcInput) : machine_state :=
init_msF segs pc ph (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en).

Lemma ms0_eq : forall segs pc ph en inp,
ms0 segs pc ph en inp =
MS (mkR_init (en_sp en)) bvmap_empty (Z_to_bv 64 (Z.of_N pc)) (Z_to_bv 32 0) None
(wrap_mem ph (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)) (seg_rom segs).
Proof. reflexivity. Qed.

Lemma ms0F_eq : forall segs pc ph en inp,
ms0F segs pc ph en inp =
MS (mkR_init (en_sp en)) mkF0 (Z_to_bv 64 (Z.of_N pc)) (Z_to_bv 32 0) None
(wrap_mem ph (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)) (seg_rom segs).
Proof. reflexivity. Qed.

Definition mo0 (segs : list Segment) (lim : Z) (en : ExecEntry) (inp : ProcInput) : Model :=
init_model (segments_reserved segs) (en_brk en) (en_mmap_base en) (en_sp en) lim inp.

Definition ceil_of (en : ExecEntry) : Z := (bv_unsigned (en_sp en) - stack_max_size)%Z.

Lemma alloc_top_mo0 : forall segs lim en inp, alloc_top (m_vmmaps (mo0 segs lim en inp)) = ceil_of en.
Proof. intros segs lim [? ? ? ?] inp. unfold mo0. rewrite m_vmmaps_init_model. reflexivity. Qed.

Lemma mo0_not_halted : forall segs lim en inp, m_halted (mo0 segs lim en inp) = None.
Proof. reflexivity. Qed.

Lemma mo0_minv : forall segs lim en inp, minv (mo0 segs lim en inp).
Proof. intros. apply minv_init. Qed.

Lemma ms0_svc : forall segs pc ph en inp, ms_svc_pending (ms0 segs pc ph en inp) = None.
Proof. reflexivity. Qed.

Lemma ms0F_svc : forall segs pc ph en inp, ms_svc_pending (ms0F segs pc ph en inp) = None.
Proof. reflexivity. Qed.

Remark frm0_init : frm0 (Z_to_bv 32 0).
Proof. reflexivity. Qed.

Definition valid_input_core (inp : ProcInput) : Prop :=
valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
/\ valid_creds inp /\ valid_nofile (in_nofile inp)
/\ valid_sigmask inp /\ valid_hwcap (in_hwcap inp)
/\ in_va_size inp = Sv48.

Lemma valid_input_core_of_valid_input : forall inp, valid_input inp -> valid_input_core inp.
Proof. intros inp (A & B & C & _ & D & E & F & G & _ & I & _). exact (conj A (conj B (conj C (conj D (conj E (conj F (conj G I))))))). Qed.

Lemma valid_input_core_of_valid_input_abort : forall inp, valid_input_abort inp -> valid_input_core inp.
Proof. intros inp (A & B & C & _ & D & E & F & G & _ & I & _). exact (conj A (conj B (conj C (conj D (conj E (conj F (conj G I))))))). Qed.

Lemma valid_input_core_va_size : forall inp, valid_input_core inp -> in_va_size inp = Sv48.
Proof. intros inp (_ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.

Lemma valid_entry_core : forall img en inp,
valid_input_core inp ->
(valid_entry img en inp
<-> match img, en with
| mkImage segs _ _, mkEntry sp brk0 mbase _ =>
valid_sp sp /\ valid_brk segs brk0 /\ valid_mmap_base mbase
/\ entry_stack_fits sp (in_argv inp) (in_envp inp)
end).
Proof. intros img en inp VI. apply valid_entry_sv48. apply valid_input_core_va_size. exact VI. Qed.

Lemma valid_entry_parts : forall segs pc ph sp brk0 mbase dr inp,
valid_input_core inp ->
valid_entry (mkImage segs pc ph) (mkEntry sp brk0 mbase dr) inp ->
valid_sp sp /\ valid_brk segs brk0 /\ valid_mmap_base mbase
/\ entry_stack_fits sp (in_argv inp) (in_envp inp).
Proof. intros segs pc ph sp brk0 mbase dr inp VI VE. exact (proj1 (valid_entry_core _ _ _ VI) VE). Qed.

Definition tree_ok {R : Type} (segs : list Segment) (pc : N) (ph : PhdrInfo) (lim : Z)
(t : prog_tree R) (Q : R -> machine_state -> Prop) : Prop :=
forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input_core inp ->
impl segs (at_node segs) (t inp en) Q (ms0 segs pc ph en inp)
/\ leaves_unreachable_m nstep (t inp en) (mo0 segs lim en inp)
/\ tsafe nstep nsafe (t inp en) (mo0 segs lim en inp).

Definition tree_okF {R : Type} (segs : list Segment) (pc : N) (ph : PhdrInfo) (lim : Z)
(t : prog_tree R) (Q : R -> machine_state -> Prop) : Prop :=
forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input_core inp ->
impl segs (at_node segs) (t inp en) Q (ms0F segs pc ph en inp)
/\ leaves_unreachable_m nstep (t inp en) (mo0 segs lim en inp)
/\ tsafe nstep nsafe (t inp en) (mo0 segs lim en inp).

Definition tree_traces {R : Type} (t : itree node R) (mo : Model) : list event -> Prop :=
fun tr => exists full, ttrace nstep nexit t mo full /\ is_prefix tr full.

Definition trees_equiv {RS RT : Type} (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
(segsT : list Segment) (pcT : N) (phT : PhdrInfo) (tS : prog_tree RS) (tT : prog_tree RT) : Prop :=
forall enS enT inp,
valid_entry (mkImage segsS pcS phS) enS inp ->
valid_entry (mkImage segsT pcT phT) enT inp ->
valid_input_core inp ->
trace_equiv (tree_traces (tS inp enS) (mo0 segsS source_alloc_limit enS inp))
(tree_traces (tT inp enT) (mo0 segsT target_alloc_limit enT inp)).

Lemma trees_equiv_of_ttrace : forall {RS RT : Type} (tS : itree node RS) (tT : itree node RT) moS moT,
(forall tr, ttrace nstep nexit tS moS tr <-> ttrace nstep nexit tT moT tr) ->
trace_equiv (tree_traces tS moS) (tree_traces tT moT).
Proof.
intros RS RT tS tT moS moT H tr. unfold tree_traces.
split; intros (full & Hf & Hp); exists full; split; auto; apply H; exact Hf.
Qed.

Lemma run_eq : forall segs pc ph lim en inp,
run_scfg (alloc_only_cfg false) (mkImage segs pc ph) lim en inp =
let c0 := mkCfg (init_machine_state segs pc ph (en_sp en) (en_draw en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
(mo0 segs lim en inp) in
{| bh_traces := obs_trace_cfg segs kit_cfg c0;
bh_errors := reaches_error_cfg segs kit_cfg c0;
bh_all_errors := all_traces_error_cfg segs kit_cfg c0;
bh_unmodeled := reaches_unmodeled_cfg segs kit_cfg c0 |}.
Proof. intros segs pc ph lim [sp brk mb rnd] inp. reflexivity. Qed.

Lemma run_of_tree_gen : forall {R : Type} segs pc ph lim (t : itree node R) (Q : R -> machine_state -> Prop) en inp
(msX : machine_state),
(let c0 := mkCfg (init_machine_state segs pc ph (en_sp en) (en_draw en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (mo0 segs lim en inp) in
let c0' := mkCfg msX (mo0 segs lim en inp) in
(forall tr, obs_trace_cfg segs kit_cfg c0 tr <-> obs_trace_cfg segs kit_cfg c0' tr) /\
(reaches_error_cfg segs kit_cfg c0 <-> reaches_error_cfg segs kit_cfg c0') /\
(all_traces_error_cfg segs kit_cfg c0 <-> all_traces_error_cfg segs kit_cfg c0') /\
(reaches_unmodeled_cfg segs kit_cfg c0 <-> reaches_unmodeled_cfg segs kit_cfg c0')) ->
ms_svc_pending msX = None ->
impl segs (at_node segs) t Q msX ->
leaves_unreachable_m nstep t (mo0 segs lim en inp) ->
tsafe nstep nsafe t (mo0 segs lim en inp) ->
trace_equiv (bh_traces (run_scfg (alloc_only_cfg false) (mkImage segs pc ph) lim en inp)) (tree_traces t (mo0 segs lim en inp))
/\ ~ bh_errors (run_scfg (alloc_only_cfg false) (mkImage segs pc ph) lim en inp)
/\ ~ bh_unmodeled (run_scfg (alloc_only_cfg false) (mkImage segs pc ph) lim en inp).
Proof.
intros R segs pc ph lim t Q en inp msX Heqv Hsvc Himpl Hleaves Hsafe.
rewrite run_eq. cbn [bh_traces bh_errors bh_unmodeled].
destruct Heqv as (Htr & Herr & _ & Hunm).
pose proof (nodes_sound segs) as NS.
split; [| split].
- intros tr. rewrite (Htr tr). unfold tree_traces.
apply (impl_run_traces2 node segs (at_node segs) nstep nexit minv nsafe NS t _ _ _
Himpl Hleaves (mo0_not_halted _ _ _ _) (mo0_minv _ _ _ _) Hsafe Hsvc).
- rewrite Herr.
apply (impl_run_safe2 node segs (at_node segs) nstep nexit minv nsafe NS t _ _ _
Himpl Hleaves (mo0_not_halted _ _ _ _) (mo0_minv _ _ _ _) Hsafe Hsvc).
- rewrite Hunm.
apply (impl_run_modeled2 node segs (at_node segs) nstep nexit minv nsafe NS t _ _ _
Himpl Hleaves (mo0_not_halted _ _ _ _) (mo0_minv _ _ _ _) Hsafe Hsvc).
Qed.

Lemma run_of_tree : forall {R : Type} segs pc ph lim (t : itree node R) (Q : R -> machine_state -> Prop) en inp,
impl segs (at_node segs) t Q (ms0 segs pc ph en inp) ->
leaves_unreachable_m nstep t (mo0 segs lim en inp) ->
tsafe nstep nsafe t (mo0 segs lim en inp) ->
trace_equiv (bh_traces (run_scfg (alloc_only_cfg false) (mkImage segs pc ph) lim en inp)) (tree_traces t (mo0 segs lim en inp))
/\ ~ bh_errors (run_scfg (alloc_only_cfg false) (mkImage segs pc ph) lim en inp)
/\ ~ bh_unmodeled (run_scfg (alloc_only_cfg false) (mkImage segs pc ph) lim en inp).
Proof.
intros R segs pc ph lim t Q en inp Himpl Hleaves Hsafe.
eapply (run_of_tree_gen segs pc ph lim t Q en inp (ms0 segs pc ph en inp)); try assumption.
- exact (init_behaviour_eqv segs pc ph (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) (mo0 segs lim en inp)).
- apply ms0_svc.
Qed.

Lemma run_of_treeF : forall {R : Type} segs pc ph lim (t : itree node R) (Q : R -> machine_state -> Prop) en inp,
impl segs (at_node segs) t Q (ms0F segs pc ph en inp) ->
leaves_unreachable_m nstep t (mo0 segs lim en inp) ->
tsafe nstep nsafe t (mo0 segs lim en inp) ->
trace_equiv (bh_traces (run_scfg (alloc_only_cfg false) (mkImage segs pc ph) lim en inp)) (tree_traces t (mo0 segs lim en inp))
/\ ~ bh_errors (run_scfg (alloc_only_cfg false) (mkImage segs pc ph) lim en inp)
/\ ~ bh_unmodeled (run_scfg (alloc_only_cfg false) (mkImage segs pc ph) lim en inp).
Proof.
intros R segs pc ph lim t Q en inp Himpl Hleaves Hsafe.
eapply (run_of_tree_gen segs pc ph lim t Q en inp (ms0F segs pc ph en inp)); try assumption.
- exact (init_behaviour_eqvF segs pc ph (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) (mo0 segs lim en inp)).
- apply ms0F_svc.
Qed.

Lemma trace_equiv_sym : forall T1 T2, trace_equiv T1 T2 -> trace_equiv T2 T1.
Proof. intros T1 T2 H tr. symmetry. apply H. Qed.

Lemma trace_equiv_trans : forall T1 T2 T3, trace_equiv T1 T2 -> trace_equiv T2 T3 -> trace_equiv T1 T3.
Proof. intros T1 T2 T3 H1 H2 tr. rewrite (H1 tr). apply H2. Qed.

Definition tree_ok_any {R : Type} (segs : list Segment) (pc : N) (ph : PhdrInfo) (lim : Z)
(t : prog_tree R) (Q : R -> machine_state -> Prop) : Prop :=
tree_ok segs pc ph lim t Q \/ tree_okF segs pc ph lim t Q.

Lemma run_of_tree_any : forall {R : Type} segs pc ph lim (t : prog_tree R) (Q : R -> machine_state -> Prop) en inp,
tree_ok_any segs pc ph lim t Q ->
valid_entry (mkImage segs pc ph) en inp -> valid_input_core inp ->
trace_equiv (bh_traces (run_scfg (alloc_only_cfg false) (mkImage segs pc ph) lim en inp)) (tree_traces (t inp en) (mo0 segs lim en inp))
/\ ~ bh_errors (run_scfg (alloc_only_cfg false) (mkImage segs pc ph) lim en inp)
/\ ~ bh_unmodeled (run_scfg (alloc_only_cfg false) (mkImage segs pc ph) lim en inp).
Proof.
intros R segs pc ph lim t Q en inp [H|H] Hv Hi;
destruct (H en inp Hv Hi) as (Himpl & Hleaves & Hsafe).
- eapply run_of_tree; eauto.
- eapply run_of_treeF; eauto.
Qed.

Lemma short_write_no_kill : forall fd bs eff evs sig fs,
short_write fd bs eff evs -> ~ In (KillEv sig fs) evs.
Proof.
intros fd bs eff evs sig fs (k & _ & _ & ->) Hin.
apply in_map_iff in Hin. destruct Hin as (b & Hb & _). discriminate Hb.
Qed.

Lemma nstep_no_kill : forall n mo eff mo' evs sig fs,
nstep n mo eff mo' evs -> ~ In (KillEv sig fs) evs.
Proof.
intros n mo eff mo' evs sig fs H.
destruct n; cbn [nstep] in H;
try (destruct H as (-> & _); intros [])
; try (destruct H as (_ & Hs); revert Hs).
- intros Hs. eapply short_write_no_kill; exact Hs.
- destruct (length (concat bufs) =? 0)%nat.
+ intros (_ & ->). intros [].
+ intros Hs. eapply short_write_no_kill; exact Hs.
- destruct H.
Qed.

Lemma ttrace_no_kill : forall {R : Type} (t : itree node R) mo tr sig fs,
ttrace nstep nexit t mo tr -> ~ In (KillEv sig fs) tr.
Proof.
intros R t. induction t as [r | n k IH]; intros mo tr sig fs Ht Hin.
- cbn in Ht. subst tr. exact Hin.
- cbn in Ht. destruct Ht as [(code & mo' & Hx & ->) | (rsp & mo' & evs & tr' & Hs & Ht' & ->)].
+ destruct Hin as [Heq | []]. discriminate Heq.
+ apply in_app_or in Hin. destruct Hin as [Hin | Hin].
* exact (nstep_no_kill _ _ _ _ _ _ _ Hs Hin).
* exact (IH rsp mo' tr' sig fs Ht' Hin).
Qed.

Lemma is_prefix_In : forall {A : Type} (l1 l2 : list A) x,
is_prefix l1 l2 -> In x l1 -> In x l2.
Proof.
intros A l1. induction l1 as [|a l1 IH]; intros l2 x Hp Hin.
- destruct Hin.
- destruct l2 as [|b l2]; [destruct Hp|]. destruct Hp as [<- Hp].
destruct Hin as [<- | Hin]; [left; reflexivity | right; exact (IH _ _ Hp Hin)].
Qed.

Lemma tree_traces_no_kill : forall {R : Type} (t : itree node R) mo tr sig fs,
tree_traces t mo tr -> ~ In (KillEv sig fs) tr.
Proof.
intros R t mo tr sig fs (full & Hf & Hp) Hin.
apply (ttrace_no_kill t mo full sig fs Hf). exact (is_prefix_In _ _ _ Hp Hin).
Qed.

Lemma not_dies_of_tree : forall {R : Type} b (t : itree node R) mo,
trace_equiv (bh_traces b) (tree_traces t mo) -> ~ dies_by_signal b.
Proof.
intros R b t mo Heq (tr & sig & fs & Hb & Hin).
apply (tree_traces_no_kill t mo tr sig fs); [apply Heq; exact Hb | exact Hin].
Qed.
