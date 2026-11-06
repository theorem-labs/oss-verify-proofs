(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YK18.v, with its module paths changed; srealizes_of_realizes removed and the exit case of srz_exit re-proved directly (srz_emit1 over sstep_exit), because this unit's realizes (YK15.v) has a cut at a budget refusal (a Theorem Labs lane's adaptation, a working branch 0bed23e5b69). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK16 YK0n YK0i YK0v YK15 YK0j YK0t YK1g.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.R Require Import Cfg.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Section b.
Variable segs : list Segment.
Inductive srealizes : config -> TSet -> Prop :=
| srz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
(T : I -> TSet) (i0 : I),
node_ok segs c I evs nx ->
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
Lemma realizes_of_srealizes : forall c T, srealizes c T -> realizes segs c T.
Proof.
intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c Hspin Hh | c T T' H IH Heq].
- exact (rz_node segs c I evs nx T i0 Hnode IH).
- exact (rz_halt segs c Hh).
- destruct Hspin as [[] _].
- exact (rz_conseq segs c T T' IH Heq).
Qed.
Lemma srealizes_nonempty : forall c T, srealizes c T -> T [].
Proof.
intros c T H;
induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
| c Hspin Hh | c T T' H IH Heq].
- exists i0. left. apply is_prefix_nil.
- reflexivity.
- reflexivity.
- apply Heq. exact IH.
Qed.
Lemma srealizes_pclosed : forall c T, srealizes c T ->
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
Lemma srealizes_star_only : forall c T, srealizes c T ->
forall tr c', star_cfg segs ACFG c tr c' -> T tr.
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
- destruct (star_cfg_halted_nil segs ACFG c tr c' Hh Hstar) as [-> _]. reflexivity.
- destruct Hspin as [[] _].
- apply Heq. eapply IH; exact Hstar.
Qed.
Lemma srealizes_admits : forall c T, srealizes c T ->
forall tr, T tr -> obs_trace_cfg segs ACFG c tr.
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
- unfold t_nil in HT; subst tr. apply obs_trace_cfg_nil.
- unfold t_nil in HT; subst tr. apply obs_trace_cfg_nil.
- apply IH. apply Heq. exact HT.
Qed.
Theorem srealizes_obs_iff : forall c T, srealizes c T ->
forall tr, obs_trace_cfg segs ACFG c tr <-> T tr.
Proof.
intros c T H tr. split.
- intros (tr' & c' & Hstar & Hp).
eapply srealizes_pclosed;
[exact H | eapply srealizes_star_only; eauto | exact Hp].
- apply srealizes_admits; exact H.
Qed.
Lemma srealizes_step : forall c T e c',
srealizes c T -> sstep_cfg segs ACFG c e (SNext c') -> exists T', srealizes c' T'.
Proof.
intros c T e c' H; revert e c';
induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
| c Hspin Hh | c T T' H IH Heq];
intros e c' Hss.
- destruct Hnode as [_ Hsound].
destruct (Hsound e (SNext c') Hss) as (i & _ & Heq2).
inversion Heq2; subst c'. exists (T i). apply Hcont.
- exfalso. apply Hh. eapply sstep_halted_none; exact Hss.
- destruct Hspin as [[] _].
- eapply IH; exact Hss.
Qed.
Lemma srealizes_no_sserror : forall c T e,
srealizes c T -> ~ sstep_cfg segs ACFG c e SError.
Proof.
intros c T e H; revert e;
induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
| c Hspin Hh | c T T' H IH Heq];
intros e Hss.
- destruct Hnode as [_ Hsound].
destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate.
- apply Hh. eapply sstep_halted_none; exact Hss.
- destruct Hspin as [[] _].
- eapply IH; exact Hss.
Qed.
Definition srz_path (c : config) : Prop := exists T, srealizes c T.
Theorem srealizes_no_error : forall c T,
srealizes c T -> ~ reaches_error_cfg segs ACFG c.
Proof.
intros c T H.
apply (inv_no_reaches_error_cfg segs ACFG srz_path).
- intros c1 e c2 (T1 & H1) Hss. eapply srealizes_step; eauto.
- intros c1 e (T1 & H1) Hss. eapply srealizes_no_sserror; eauto.
- exists T; exact H.
Qed.
Lemma srz_silent1 : forall c c' T,
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
Lemma srz_emit1 : forall c c' e T,
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
Lemma srz_alt2 : forall c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet)
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
Lemma srz_step : forall ms model ms' T,
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
apply node_ok_of_pnode; [apply transparent_instr; exact Hsvc|]. split.
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
eapply rz_silent1; [eapply node_instr_disjoint; eassumption | exact Hc].
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
eapply srz_silent1; [eapply node_instr_disjoint; eassumption | exact Hc].
Qed.
Lemma srz_write1 : forall ms model x8 buf T,
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
Lemma srz_exit : forall ms model x8,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
is_exit_no x8 ->
srealizes (mkCfg ms model)
(t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
intros ms model x8 Hh Hsvc Hx8.
set (code := bv_and (ms_gpr ms 0) (Z_to_bv 64 255)).
unfold t_exit.
eapply (srz_emit1 (mkCfg ms model) (mkCfg ms (with_halted code model))).
- apply node_ok_of_pnode; [eapply transparent_exit; eassumption|]. split.
+ intros []. cbn.
replace [ExitEv code (m_fs model)]
with ([] ++ [ExitEv code (m_fs (with_halted code model))]) by reflexivity.
apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
(with_halted code model) [] code);
[exact Hh | exact Hsvc
| apply (exit_dispatch_ok (sys_input segs ms x8) model);
rewrite in_sysno_sys_input; exact Hx8
| reflexivity
| apply m_killed_with_halted ].
+ intros e st Hss.
destruct (sstep_exit_inv segs ms model x8 e st Hh Hsvc Hx8 Hss) as [-> ->].
exists tt. split; reflexivity.
- apply srz_halt. cbn. discriminate.
Qed.
Lemma node_munmap : forall ms model x8,
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
intros ms model x8 Hh Hlazy Hsvc Hno Hargs.
apply node_ok_of_pnode; [eapply transparent_nonalloc_no; [exact Hsvc | exact Hno | reflexivity]|]. split.
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
Lemma srz_munmap : forall ms model x8 T,
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
End b.
Ltac chain_mst_sp :=
first [ (eapply srz_msteps; [ sym_halted | sym_no_lazy | | ])
| chain_mst ].
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
srealizes segs (mkCfg ms' (YK0v.mmap_model a n model)) T ->
srealizes segs (mkCfg ms (YK0v.mmap_model a n model)) T.
Proof.
intros segs ms ms' model a n T Hh Hlazy Hms Hr.
chain_mst_sp; [exact Hms | exact Hr].
Qed.
