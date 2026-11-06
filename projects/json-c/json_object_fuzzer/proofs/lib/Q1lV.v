(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QU8l.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QU8l. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qg4E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qg4E. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QybZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QybZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QuHC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuHC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdTb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdTb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHWH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHWH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qmth.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qmth.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qg31.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qg31.
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
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
to_spin segs (cfg_ms c) (cfg_model c) ->
m_halted (cfg_model c) = None ->
srealizes c t_nil
| srz_conseq : forall c T T',
srealizes c T -> t_eq T T' -> srealizes c T'

| srz_loop : forall (V : config -> Prop) (T : TSet) (c c_e : config),
V c ->
(forall c', V c' -> slbody V T c') ->
star_cfg segs (alloc_only_cfg false) c [] c_e ->
srealizes c_e T ->
srealizes c T
with slbody : (config -> Prop) -> TSet -> config -> Prop :=
| slb_exit : forall (V : config -> Prop) (T : TSet) c,
srealizes c T -> slbody V T c
| slb_node : forall (V : config -> Prop) (T : TSet) c (I : Type) (nx : I -> config)
(k : I -> bool),
node_ok segs c I (fun _ => []) nx ->
(forall i, k i = true -> slbody V T (nx i)) ->
(forall i, k i = false -> V (nx i)) ->
slbody V T c.

Scheme srealizes_mutind := Induction for srealizes Sort Prop
with slbody_mutind := Induction for slbody Sort Prop.
Combined Scheme srealizes_slbody_mutind from srealizes_mutind, slbody_mutind.

Lemma srz_spinning : forall c, spinning segs c -> srealizes c t_nil.
Proof. intros c [Hspin Hh]. exact (srz_spin c Hspin Hh). Qed.

Lemma srealizes_nonempty : forall c T, srealizes c T -> T [].
Proof.
intros c T H;
induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
| c Hspin Hh | c T T' H IH Heq
| V T c c_e HV Hbody Hw He IHe].
- exists i0. left. apply is_prefix_nil.
- reflexivity.
- reflexivity.
- apply Heq. exact IH.
- exact IHe.
Qed.

Lemma srealizes_pclosed : forall c T, srealizes c T ->
forall tr tr', T tr -> is_prefix tr' tr -> T tr'.
Proof.
intros c T H;
induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
| c Hspin Hh | c T T' H IH Heq
| V T c c_e HV Hbody Hw He IHe];
intros tr tr' HT Hp.
- destruct HT as [i [Hpre | (tr0 & -> & HT0)]]; exists i.
+ left. eapply is_prefix_trans; eauto.
+ apply is_prefix_app_split in Hp as [Hp | (tr0' & -> & Hp)].
* left. exact Hp.
* right. exists tr0'. split; [reflexivity | eapply IH; eauto].
- unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
- unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
- apply Heq. eapply IH; [apply Heq; exact HT | exact Hp].
- eapply IHe; eauto.
Qed.

Inductive starn : nat -> config -> list event -> config -> Prop :=
| starn_refl : forall c, starn O c [] c
| starn_step : forall n c1 evs c2 tr c3,
sstep_cfg segs (alloc_only_cfg false) c1 evs (SNext c2) ->
starn n c2 tr c3 ->
starn (S n) c1 (evs ++ tr) c3.

Lemma star_starn : forall c tr c', star_cfg segs (alloc_only_cfg false) c tr c' -> exists n, starn n c tr c'.
Proof.
intros c tr c' H; induction H as [c | c1 evs c2 tr c3 Hss Hstar (n & IH)].
- exists O. apply starn_refl.
- exists (S n). eapply starn_step; eauto.
Qed.

Lemma starn_star : forall n c tr c', starn n c tr c' -> star_cfg segs (alloc_only_cfg false) c tr c'.
Proof.
intros n c tr c' H; induction H as [c | n c1 evs c2 tr c3 Hss Hstar IH].
- apply star_cfg_refl.
- eapply star_cfg_step; eauto.
Qed.

#[local] Definition P_slb_sound (V : config -> Prop) (T : TSet) (c : config) : Prop :=
forall n : nat,
T [] ->
(forall c'' m tr c', V c'' -> (m < n)%nat -> starn m c'' tr c' -> T tr) ->
forall m tr c', (m <= n)%nat -> starn m c tr c' -> T tr.

Lemma srealizes_slbody_sound :
(forall c T, srealizes c T -> forall n tr c', starn n c tr c' -> T tr)
/\ (forall V T c, slbody V T c -> P_slb_sound V T c).
Proof.
apply srealizes_slbody_mutind.
-
intros c I evs nx T i0 Hnode Hcont IH n tr c' Hstar.
inversion Hstar as [|m c1 e c2 tr2 c3 Hss Hstar2]; subst.
+ exists i0. left. apply is_prefix_nil.
+ destruct Hnode as [_ Hsound].
destruct (Hsound e (SNext c2) Hss) as (i & -> & Heq2).
inversion Heq2; subst c2.
exists i. right. exists tr2. split; [reflexivity | eapply IH; exact Hstar2].
-
intros c Hh n tr c' Hstar.
destruct (star_halted_nil segs c tr c' Hh (star_cfg_sub segs _ _ _ _ (starn_star _ _ _ _ Hstar))) as [-> _]. reflexivity.
-
intros c Hspin Hh n tr c' Hstar.
destruct c as [ms model]; cbn in Hspin, Hh.
exact (spin_star_nil segs ms model tr c' Hspin Hh (star_cfg_sub segs _ _ _ _ (starn_star _ _ _ _ Hstar))).
-
intros c T T' H IH Heq n tr c' Hstar. apply Heq. eapply IH; exact Hstar.
-
intros V T c c_e HV Hbody IHbody Hw He IHe n.
assert (HT0 : T []) by (apply (IHe O [] c_e); apply starn_refl).
enough (HQ : forall n c0, V c0 -> forall tr c', starn n c0 tr c' -> T tr)
by (intros tr c' Hs; exact (HQ n c HV tr c' Hs)).
clear n. intros n.
induction n as [n IHn] using (well_founded_induction Wf_nat.lt_wf).
intros c0 HV0 tr c' Hstar.
refine (IHbody c0 HV0 n HT0 _ n tr c' (PeanoNat.Nat.le_refl n) Hstar).
intros c'' m tr2 c2 HV'' Hm Hs. exact (IHn m Hm c'' HV'' tr2 c2 Hs).
-
intros V T c H IH n _ _ m tr c' _ Hstar. eapply IH; exact Hstar.
-
intros V T c I nx k Hnode Hk IHk HV n HT0 Hlt m tr c' Hm Hstar.
inversion Hstar as [|m' c1 e c2 tr2 c3 Hss Hstar2]; subst.
+ exact HT0.
+ destruct Hnode as [_ Hsound].
destruct (Hsound e (SNext c2) Hss) as (i & -> & Heq2).
inversion Heq2; subst c2. cbn [app].
destruct (k i) eqn:Hki.
* refine (IHk i Hki n HT0 Hlt m' tr2 c' _ Hstar2). lia.
* apply (Hlt (nx i) m' tr2 c' (HV i Hki)); [lia | exact Hstar2].
Qed.

Lemma srealizes_star_only : forall c T, srealizes c T ->
forall tr c', star_cfg segs (alloc_only_cfg false) c tr c' -> T tr.
Proof.
intros c T H tr c' Hstar. destruct (star_starn _ _ _ Hstar) as (n & Hn).
eapply (proj1 srealizes_slbody_sound); eauto.
Qed.

Lemma srealizes_admits : forall c T, srealizes c T ->
forall tr, T tr -> obs_trace_cfg segs (alloc_only_cfg false) c tr.
Proof.
intros c T H;
induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
| c Hspin Hh | c T T' H IH Heq
| V T c c_e HV Hbody Hw He IHe];
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
- destruct (IHe tr HT) as (tr'' & c'' & Hstar & Hp).
exists tr'', c''. split; [| exact Hp].
change tr'' with ([] ++ tr''). eapply star_cfg_trans; [exact Hw | exact Hstar].
Qed.

Theorem srealizes_obs_iff : forall c T, srealizes c T ->
forall tr, obs_trace_cfg segs (alloc_only_cfg false) c tr <-> T tr.
Proof.
intros c T H tr. split.
- intros (tr' & c' & Hstar & Hp).
eapply srealizes_pclosed;
[exact H | eapply srealizes_star_only; eauto | exact Hp].
- apply srealizes_admits; exact H.
Qed.

Definition srz_path (c : config) : Prop :=
(exists T, srealizes c T)
\/ (exists V T, (forall c', V c' -> slbody V T c') /\ slbody V T c).

Lemma srealizes_slbody_step :
(forall c T, srealizes c T -> forall e c', sstep_cfg segs (alloc_only_cfg false) c e (SNext c') -> srz_path c')
/\ (forall V T c, slbody V T c ->
(forall c', V c' -> slbody V T c') ->
forall e c', sstep_cfg segs (alloc_only_cfg false) c e (SNext c') -> srz_path c').
Proof.
apply srealizes_slbody_mutind.
- intros c I evs nx T i0 Hnode Hcont IH e c' Hss.
destruct Hnode as [_ Hsound].
destruct (Hsound e (SNext c') Hss) as (i & _ & Heq2).
inversion Heq2; subst c'. left. exists (T i). apply Hcont.
- intros c Hh e c' Hss. exfalso. apply Hh. eapply sstep_halted_none; exact Hss.
- intros c Hspin Hh e c' Hss.
destruct (silent_loop_sstep segs (spinning segs) c e (SNext c')
(spinning_silent_loop segs) (conj Hspin Hh) (sstep_cfg_sub segs _ _ _ _ Hss))
as (_ & c'' & Heq2 & Hsp').
injection Heq2 as ->.
left. exists t_nil. exact (srz_spinning _ Hsp').
- intros c T T' H IH Heq e c' Hss. eapply IH; exact Hss.
- intros V T c c_e HV Hbody IHbody Hw He IHe e c' Hss.
eapply (IHbody c HV Hbody); exact Hss.
- intros V T c H IH _ e c' Hss. eapply IH; exact Hss.
- intros V T c I nx k Hnode Hk IHk HV Hbody e c' Hss.
destruct Hnode as [_ Hsound].
destruct (Hsound e (SNext c') Hss) as (i & _ & Heq2).
inversion Heq2; subst c'. right. exists V, T. split; [exact Hbody|].
destruct (k i) eqn:Hki.
+ apply Hk. exact Hki.
+ apply Hbody. apply HV. exact Hki.
Qed.

Lemma srealizes_slbody_no_sserror :
(forall c T, srealizes c T -> forall e, ~ sstep_cfg segs (alloc_only_cfg false) c e SError)
/\ (forall V T c, slbody V T c -> forall e, ~ sstep_cfg segs (alloc_only_cfg false) c e SError).
Proof.
apply srealizes_slbody_mutind.
- intros c I evs nx T i0 Hnode Hcont IH e Hss.
destruct Hnode as [_ Hsound].
destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate.
- intros c Hh e Hss. apply Hh. eapply sstep_halted_none; exact Hss.
- intros c Hspin Hh e Hss.
destruct c as [ms model]; cbn in Hspin, Hh.
exact (spin_no_sstep_error segs ms model Hspin Hh e (sstep_cfg_sub segs _ _ _ _ Hss)).
- intros c T T' H IH Heq e Hss. eapply IH; exact Hss.
- intros V T c c_e HV Hbody IHbody Hw He IHe e Hss. eapply (IHbody c HV); exact Hss.
- intros V T c H IH e Hss. eapply IH; exact Hss.
- intros V T c I nx k Hnode Hk IHk HV e Hss.
destruct Hnode as [_ Hsound].
destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate.
Qed.

Lemma srealizes_step : forall c T e c',
srealizes c T -> sstep_cfg segs (alloc_only_cfg false) c e (SNext c') -> srz_path c'.
Proof. intros c T e c' H Hss. eapply (proj1 srealizes_slbody_step); eauto. Qed.

Lemma srealizes_no_sserror : forall c T e,
srealizes c T -> ~ sstep_cfg segs (alloc_only_cfg false) c e SError.
Proof. intros c T e H. eapply (proj1 srealizes_slbody_no_sserror); eauto. Qed.

Theorem srealizes_no_error : forall c T,
srealizes c T -> ~ reaches_error_cfg segs (alloc_only_cfg false) c.
Proof.
intros c T H.
apply (inv_no_reaches_error_cfg segs srz_path).
- intros c1 e c2 [(T1 & H1) | (V & T1 & Hb & Hl)] Hss.
+ eapply srealizes_step; eauto.
+ eapply (proj2 srealizes_slbody_step); eauto.
- intros c1 e [(T1 & H1) | (V & T1 & Hb & Hl)] Hss.
+ eapply srealizes_no_sserror; eauto.
+ eapply (proj2 srealizes_slbody_no_sserror); eauto.
- left. exists T; exact H.
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

End WithSegs.

Ltac chain_mst_sp :=
first [ (eapply srz_msteps; [ sym_halted | sym_no_lazy | | ])
| chain_mst ].

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

Hypothesis Hrefuse : forall e, In e mmap_errnos ->
to_spin segs (advance_past_svc (set_gpr0 ms (errno_ret e))) model.

Hypothesis Hgrant : forall a,
grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
QuHC.twm segs
(advance_past_svc
(apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
(mmap_model a (page_round_up (ms_gpr ms 1)) model) bs cs.
Hypothesis Hex : exists a,
grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true.
Hypothesis Hbs : bufs_modeled bs.

End SpinBranchReal.
