(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Trevor Hansen, 2026-11: module names. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import
YK16 YK0o YK0j YK0v YK15 YK0k YK0t YK1g.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Export HaltsFO.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)
Section b.
Variable segs : list Segment.
Inductive srealizesE : config -> TSet -> Prop :=
| srzE_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
(T : I -> TSet) (i0 : I),
node_ok segs c I evs nx ->
(forall i, srealizesE (nx i) (T i)) ->
srealizesE c (t_alt (fun i => t_emit (evs i) (T i)))
| srzE_halt : forall c,
m_halted (cfg_model c) <> None ->
srealizesE c t_nil
| srzE_spin : forall c,
to_spin segs (cfg_ms c) (cfg_model c) ->
m_halted (cfg_model c) = None ->
srealizesE c t_nil
| srzE_conseq : forall c T T',
srealizesE c T -> t_eq T T' -> srealizesE c T'.
Definition srealizesM (b : bool) (c : config) (T : TSet) : Prop :=
srealizesE c T /\ (if b then fo_exits segs c T else True).
Definition srealizes (c : config) (T : TSet) : Prop := srealizesM true c T.

Lemma srealizesM_E : forall b c T, srealizesM b c T -> srealizesE c T.
Proof. intros b c T [H _]; exact H. Qed.
Lemma srealizesM_of_E : forall c T, srealizesE c T -> srealizesM false c T.
Proof. intros c T H. split; [exact H | exact Logic.I]. Qed.
Lemma srealizesM_weaken : forall b c T, srealizes c T -> srealizesM b c T.
Proof. intros b c T [HE HF]. split; [exact HE | destruct b; [exact HF | exact Logic.I]]. Qed.
Lemma srealizesM_mono : forall b b' c T, Bool.le b' b -> srealizesM b c T -> srealizesM b' c T.
Proof. intros b b' c T Hle [HE HF]. split; [exact HE|]. destruct b', b; cbn in Hle; first [exact HF | exact Logic.I | discriminate Hle | destruct Hle]. Qed.
Lemma srealizes_fo : forall c T, srealizes c T -> fo_exits segs c T.
Proof. intros c T [_ H]; exact H. Qed.

Lemma srealizesE_of_realizes : forall c T,
realizes segs c T -> srealizesE c T.
Proof.
intros c T H;
induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq].
- exact (srzE_node c I evs nx T i0 Hnode IH).
- exact (srzE_halt c Hh).
- exact (srzE_conseq c T T' IH Heq).
Qed.
Lemma srealizes_of_realizes : forall c T,
realizes segs c T -> srealizes c T.
Proof. intros c T H. split; [apply srealizesE_of_realizes; exact H | apply fo_of_realizes; exact H]. Qed.

(* [comment removed for export] *)
Lemma srzM_spin : forall c,
to_spin segs (cfg_ms c) (cfg_model c) -> m_halted (cfg_model c) = None -> srealizesM false c t_nil.
Proof. intros c Hs Hh. split; [exact (srzE_spin c Hs Hh) | exact Logic.I]. Qed.
Lemma srz_spin : forall c,
to_spin segs (cfg_ms c) (cfg_model c) -> m_halted (cfg_model c) = None -> srealizesM false c t_nil.
Proof. exact srzM_spin. Qed.
Lemma srz_spinning : forall c, spinning segs c -> srealizesM false c t_nil.
Proof. intros c [Hspin Hh]. exact (srzM_spin c Hspin Hh). Qed.

Lemma srealizesE_nonempty : forall c T, srealizesE c T -> T [].
Proof.
intros c T H;
induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
| c Hspin Hh | c T T' H IH Heq].
- exists i0. left. apply is_prefix_nil.
- reflexivity.
- reflexivity.
- apply Heq. exact IH.
Qed.
Lemma srealizesM_nonempty : forall b c T, srealizesM b c T -> T [].
Proof. intros b c T [H _]. exact (srealizesE_nonempty c T H). Qed.
Lemma srealizes_nonempty : forall c T, srealizes c T -> T [].
Proof. intros c T [H _]. exact (srealizesE_nonempty c T H). Qed.

Lemma srealizesE_pclosed : forall c T, srealizesE c T ->
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
Lemma srealizes_pclosed : forall c T, srealizes c T ->
forall tr tr', T tr -> is_prefix tr' tr -> T tr'.
Proof. intros c T [H _]. exact (srealizesE_pclosed c T H). Qed.

Lemma srealizesE_star_only : forall c T, srealizesE c T ->
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
Lemma srealizes_star_only : forall c T, srealizes c T ->
forall tr c', star segs c tr c' -> T tr.
Proof. intros c T [H _]. exact (srealizesE_star_only c T H). Qed.

Lemma srealizesE_admits : forall c T, srealizesE c T ->
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
Lemma srealizes_admits : forall c T, srealizes c T ->
forall tr, T tr -> obs_trace segs c tr.
Proof. intros c T [H _]. exact (srealizesE_admits c T H). Qed.

Theorem srealizesE_obs_iff : forall c T, srealizesE c T ->
forall tr, obs_trace segs c tr <-> T tr.
Proof.
intros c T H tr. split.
- intros (tr' & c' & Hstar & Hp).
eapply srealizesE_pclosed;
[exact H | eapply srealizesE_star_only; eauto | exact Hp].
- apply srealizesE_admits; exact H.
Qed.
Theorem srealizes_obs_iff : forall c T, srealizes c T ->
forall tr, obs_trace segs c tr <-> T tr.
Proof. intros c T [H _]. exact (srealizesE_obs_iff c T H). Qed.

Lemma srealizesE_step : forall c T e c',
srealizesE c T -> sstep segs c e (SNext c') -> exists T', srealizesE c' T'.
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
exists t_nil. destruct Hsp' as [Hs' Hh']. exact (srzE_spin _ Hs' Hh').
- eapply IH; exact Hss.
Qed.
Lemma srealizesE_no_sserror : forall c T e,
srealizesE c T -> ~ sstep segs c e SError.
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
Definition srzE_path (c : config) : Prop := exists T, srealizesE c T.
Theorem srealizesE_no_error : forall c T,
srealizesE c T -> ~ reaches_error segs c.
Proof.
intros c T H.
apply (inv_no_reaches_error segs srzE_path).
- intros c1 e c2 (T1 & H1) Hss. eapply srealizesE_step; eauto.
- intros c1 e (T1 & H1) Hss. eapply srealizesE_no_sserror; eauto.
- exists T; exact H.
Qed.
Definition srz_path (c : config) : Prop := exists T, srealizes c T.
Theorem srealizes_no_error : forall c T,
srealizes c T -> ~ reaches_error segs c.
Proof. intros c T [H _]. exact (srealizesE_no_error c T H). Qed.
Theorem srealizesM_no_error : forall b c T,
srealizesM b c T -> ~ reaches_error segs c.
Proof. intros b c T [H _]. exact (srealizesE_no_error c T H). Qed.

(* [comment removed for export] *)
Lemma srzM_node : forall b c (I : Type) (evs : I -> list event) (nx : I -> config)
(T : I -> TSet) (i0 : I),
node_ok segs c I evs nx ->
(forall i, srealizesM b (nx i) (T i)) ->
srealizesM b c (t_alt (fun i => t_emit (evs i) (T i))).
Proof.
intros b c I evs nx T i0 Hnode Hc. split.
- apply (srzE_node c I evs nx T i0 Hnode). intros i. exact (proj1 (Hc i)).
- destruct b; [|exact Logic.I]. apply (fo_node_all segs c I evs nx T i0 Hnode).
+ intros i. exact (proj2 (Hc i)).
+ intros i. exact (srealizesE_nonempty _ _ (proj1 (Hc i))).
Qed.
Lemma srzM_halt : forall b c, m_halted (cfg_model c) <> None -> srealizesM b c t_nil.
Proof. intros b c Hh. split; [exact (srzE_halt c Hh) | destruct b; [apply fo_halted; exact Hh | exact Logic.I]]. Qed.
Lemma srzM_conseq : forall b c T T', srealizesM b c T -> t_eq T T' -> srealizesM b c T'.
Proof.
intros b c T T' [HE HF] Heq. split; [exact (srzE_conseq c T T' HE Heq) | destruct b; [exact (fo_conseq segs c T T' HF Heq) | exact Logic.I]].
Qed.
(* [comment removed for export] *)
Lemma srzM_node_dead : forall b c (I : Type) (evs : I -> list event) (nx : I -> config)
(T : I -> TSet) (i0 : I) (dead : I -> Prop),
node_ok segs c I evs nx ->
~ dead i0 ->
(forall i, dead i -> srealizesE (nx i) (T i) /\ (b = true -> fo_dead segs c (nx i))) ->
(forall i, ~ dead i -> srealizesM b (nx i) (T i)) ->
srealizesM b c (t_alt (fun i => t_emit (evs i) (T i))).
Proof.
intros b c I evs nx T i0 dead Hnode Hi0 Hd Hl. split.
- apply (srzE_node c I evs nx T i0 Hnode). intros i.
destruct (Classical_Prop.classic (dead i)) as [Hi | Hi]; [exact (proj1 (Hd i Hi)) | exact (proj1 (Hl i Hi))].
- destruct b; [|exact Logic.I]. apply (fo_node segs c I evs nx T i0 dead Hnode).
+ intros i Hi. exact (proj2 (Hd i Hi) eq_refl).
+ intros i Hi. exact (proj2 (Hl i Hi)).
+ intros i Hi. exact (srealizesE_nonempty _ _ (proj1 (Hl i Hi))).
Qed.

(* [comment removed for export] *)
Lemma srz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
(T : I -> TSet) (i0 : I),
node_ok segs c I evs nx ->
(forall i, srealizes (nx i) (T i)) ->
srealizes c (t_alt (fun i => t_emit (evs i) (T i))).
Proof. exact (srzM_node true). Qed.
Lemma srz_halt : forall c,
m_halted (cfg_model c) <> None ->
srealizes c t_nil.
Proof. exact (srzM_halt true). Qed.
Lemma srz_conseq : forall c T T',
srealizes c T -> t_eq T T' -> srealizes c T'.
Proof. exact (srzM_conseq true). Qed.
Lemma srz_node_dead : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
(T : I -> TSet) (i0 : I) (dead : I -> Prop),
node_ok segs c I evs nx ->
~ dead i0 ->
(forall i, dead i -> srealizesE (nx i) (T i) /\ fo_dead segs c (nx i)) ->
(forall i, ~ dead i -> srealizes (nx i) (T i)) ->
srealizes c (t_alt (fun i => t_emit (evs i) (T i))).
Proof.
intros c I evs nx T i0 dead Hnode Hi0 Hd Hl.
apply (srzM_node_dead true c I evs nx T i0 dead Hnode Hi0); [|exact Hl].
intros i Hi. destruct (Hd i Hi) as [A B]. split; [exact A | intros _; exact B].
Qed.

Lemma srealizes_step : forall c T e c',
srealizes c T -> sstep segs c e (SNext c') -> exists T', srealizesE c' T'.
Proof. intros c T e c' [H _] Hs. exact (srealizesE_step c T e c' H Hs). Qed.
Lemma srealizes_no_sserror : forall c T e,
srealizes c T -> ~ sstep segs c e SError.
Proof. intros c T e [H _]. exact (srealizesE_no_sserror c T e H). Qed.

Lemma srzM_silent1 : forall b c c' T,
node_ok segs c unit (fun _ => []) (fun _ => c') ->
srealizesM b c' T ->
srealizesM b c T.
Proof.
intros b c c' T Hnode Hc.
apply (srzM_conseq b c (t_alt (fun _ : unit => t_emit [] T))).
- apply (srzM_node b c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode).
intros []; exact Hc.
- eapply t_eq_trans;
[ apply (t_alt_unit (fun _ : unit => t_emit [] T))
| apply t_emit_nil_eq; eapply srealizesM_nonempty; exact Hc ].
Qed.
Lemma srz_silent1 : forall c c' T,
node_ok segs c unit (fun _ => []) (fun _ => c') ->
srealizes c' T ->
srealizes c T.
Proof. exact (srzM_silent1 true). Qed.

Lemma srzM_alt2 : forall b c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet)
(a0 : IA) (b0 : IB),
node_ok segs c (IA + IB) (fun _ => []) nx ->
(forall i, srealizesM b (nx (inl i)) A) ->
(forall i, srealizesM b (nx (inr i)) B) ->
srealizesM b c (t_alt2 A B).
Proof.
intros b c IA IB nx A B a0 b0 Hnode HA HB.
assert (HA0 : A []) by (eapply srealizesM_nonempty; apply (HA a0)).
assert (HB0 : B []) by (eapply srealizesM_nonempty; apply (HB b0)).
apply (srzM_conseq b c
(t_alt (fun i : IA + IB =>
t_emit [] (match i with inl _ => A | inr _ => B end)))).
- apply (srzM_node b c (IA + IB) (fun _ => []) nx
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
Lemma srz_alt2 : forall c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet)
(a0 : IA) (b0 : IB),
node_ok segs c (IA + IB) (fun _ => []) nx ->
(forall i, srealizes (nx (inl i)) A) ->
(forall i, srealizes (nx (inr i)) B) ->
srealizes c (t_alt2 A B).
Proof. exact (srzM_alt2 true). Qed.
Lemma srzM_step : forall b ms model ms' T,
m_halted model = None ->
m_vm_lazy model = [] ->
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
srealizesM b (mkCfg ms' model) T ->
srealizesM b (mkCfg ms model) T.
Proof.
intros b ms model ms' T Hh Hlazy Hsvc Hstep Hc.
eapply srzM_silent1; [apply node_instr; eassumption | exact Hc].
Qed.
Lemma srz_step : forall ms model ms' T,
m_halted model = None ->
m_vm_lazy model = [] ->
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
srealizes (mkCfg ms' model) T ->
srealizes (mkCfg ms model) T.
Proof. exact (srzM_step true). Qed.
Lemma srzM_msteps : forall b ms ms' model T,
m_halted model = None ->
m_vm_lazy model = [] ->
msteps segs ms ms' ->
srealizesM b (mkCfg ms' model) T ->
srealizesM b (mkCfg ms model) T.
Proof.
intros b ms ms' model T Hh Hlazy Hms;
induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH];
intro Hc; [exact Hc|].
eapply srzM_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
| apply IH; exact Hc].
Qed.
Lemma srz_msteps : forall ms ms' model T,
m_halted model = None ->
m_vm_lazy model = [] ->
msteps segs ms ms' ->
srealizes (mkCfg ms' model) T ->
srealizes (mkCfg ms model) T.
Proof. exact (srzM_msteps true). Qed.

Lemma srzM_exit : forall b ms model x8,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
is_exit_no x8 ->
srealizesM b (mkCfg ms model)
(t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
intros b ms model x8 Hh Hsvc Hx8.
apply srealizesM_weaken. apply srealizes_of_realizes. apply (rz_exit segs ms model x8); assumption.
Qed.
Lemma srz_exit : forall ms model x8,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
is_exit_no x8 ->
srealizes (mkCfg ms model)
(t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof. exact (srzM_exit true). Qed.
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




End b.

Ltac chain_mst_sp :=
first [ (eapply srz_msteps; [ sym_halted | sym_no_lazy | | ])
| chain_mst ].



Section d.
Variable segs : list Segment.
Variables (ms : machine_state) (model : Model) (x8 : word).
Variables (bs : list (list byte)) (cs : word).
Hypothesis Hh : m_halted model = None.
Hypothesis Hlazy : m_vm_lazy model = [].
Hypothesis Hfd : fd1chan model.
Hypothesis Hsvc : ms_svc_pending ms = Some x8.
Hypothesis Hno : bv_unsigned x8 = 222%Z.
Hypothesis Hargs : mmap_args_ok ms.
Hypothesis Hrefuse : forall e, In e mmap_errnos ->
to_spin segs (advance_past_svc (set_gpr0 ms (errno_ret e))) model.
Hypothesis Hgrant : forall a,
grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
YK0v.twm segs
(advance_past_svc
(apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
(mmap_model a (page_round_up (ms_gpr ms 1)) model) bs cs.
Hypothesis Hex : exists a,
grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true.
Hypothesis Hbs : bufs_modeled bs.



End d.
