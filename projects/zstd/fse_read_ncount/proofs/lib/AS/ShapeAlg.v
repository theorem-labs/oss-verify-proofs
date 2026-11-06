(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import SimInv ExitSim CatSim MmapSim AllocSim WallSim.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Cfg.
Import ListNotations.
Open Scope bv_scope.
Lemma is_prefix_app_split {A} : forall (l a b : list A),
is_prefix b (l ++ a) ->
is_prefix b l \/ exists b', b = l ++ b' /\ is_prefix b' a.
Proof.
induction l as [|x l IH]; intros a b H.
- right. exists b. split; [reflexivity | exact H].
- destruct b as [|y b]; cbn in H; [left; exact I|].
destruct H as [-> H]. destruct (IH a b H) as [Hp | (b' & -> & Hp)].
+ left. cbn. split; [reflexivity | exact Hp].
+ right. exists b'. split; [reflexivity | exact Hp].
Qed.
Lemma is_prefix_nil_r {A} : forall (a : list A), is_prefix a [] -> a = [].
Proof. destruct a; cbn; [reflexivity | contradiction]. Qed.
Definition TSet := list event -> Prop.
Definition t_eq (T T' : TSet) : Prop := forall tr, T tr <-> T' tr.
Lemma t_eq_refl : forall T, t_eq T T. Proof. firstorder. Qed.
Lemma t_eq_trans : forall T1 T2 T3, t_eq T1 T2 -> t_eq T2 T3 -> t_eq T1 T3.
Proof. firstorder. Qed.
Definition t_nil : TSet := fun tr => tr = [].
Definition t_emit (evs : list event) (T : TSet) : TSet :=
fun tr => is_prefix tr evs \/ exists tr', tr = evs ++ tr' /\ T tr'.
Definition t_alt {I : Type} (f : I -> TSet) : TSet := fun tr => exists i, f i tr.
Definition t_alt2 (A B : TSet) : TSet := fun tr => A tr \/ B tr.
Definition t_exit (code : word) (fs : Fs.Fs) : TSet :=
t_emit [ExitEv code fs] t_nil.
Lemma t_emit_nil_eq : forall T, T [] -> t_eq (t_emit [] T) T.
Proof.
intros T H0 tr. unfold t_emit. split.
- intros [Hp | (tr' & -> & HT)];
[apply is_prefix_nil_r in Hp; subst tr; exact H0 | exact HT].
- intro HT. right. exists tr. split; [reflexivity | exact HT].
Qed.
Lemma t_emit_has_nil : forall e T, t_emit e T [].
Proof. intros e T. left. apply is_prefix_nil. Qed.
Section WithSegs.
Variable segs : list Segment.
Definition node_ok (c : config) (I : Type)
(evs : I -> list event) (nx : I -> config) : Prop :=
(forall i, sstep_cfg segs ACFG c (evs i) (SNext (nx i)))
/\ (forall e st, sstep_cfg segs ACFG c e st -> exists i, e = evs i /\ st = SNext (nx i)).
Definition pnode_ok (c : config) (I : Type)
(evs : I -> list event) (nx : I -> config) : Prop :=
(forall i, sstep segs c (evs i) (SNext (nx i)))
/\ (forall e st, sstep segs c e st -> exists i, e = evs i /\ st = SNext (nx i)).
#[using="Type"] Lemma node_ok_of_pnode : forall c I evs nx,
cfg_transparent segs c -> pnode_ok c I evs nx -> node_ok c I evs nx.
Proof.
intros c I evs nx Htr [Hcomp Hsound]. split.
- intros i. apply Htr. apply Hcomp.
- intros e st Hss. apply Hsound. exact (sstep_of_cfg segs ACFG _ _ _ Hss).
Qed.
#[using="Type"] Lemma transparent_exit_no : forall ms model x8,
ms_svc_pending ms = Some x8 -> is_exit_no x8 -> cfg_transparent segs (mkCfg ms model).
Proof.
intros ms model x8 Hsvc [E|E]; apply (transparent_nonalloc segs ms model x8 Hsvc); rewrite E;
apply alloc_no_b_false; reflexivity.
Qed.
Inductive realizes : config -> TSet -> Prop :=
| rz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
(T : I -> TSet) (i0 : I),
node_ok c I evs nx ->
(forall i, realizes (nx i) (T i)) ->
realizes c (t_alt (fun i => t_emit (evs i) (T i)))
| rz_halt : forall c,
m_halted (cfg_model c) <> None ->
realizes c t_nil
| rz_conseq : forall c T T',
realizes c T -> t_eq T T' -> realizes c T'.
#[using="Type"] Lemma realizes_nonempty : forall c T, realizes c T -> T [].
Proof.
intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq].
- exists i0. left. apply is_prefix_nil.
- reflexivity.
- apply Heq. exact IH.
Qed.
#[using="Type"] Lemma realizes_star_only : forall c T, realizes c T ->
forall tr c', star_cfg segs ACFG c tr c' -> T tr.
Proof.
intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
intros tr c' Hstar.
- inversion Hstar as [|c1 e c2 tr2 c3 Hss Hstar2]; subst.
+ exists i0. left. apply is_prefix_nil.
+ destruct Hnode as [_ Hsound].
destruct (Hsound e (SNext c2) Hss) as (i & -> & Heq2).
inversion Heq2; subst c2.
exists i. right. exists tr2. split; [reflexivity | eapply IH; exact Hstar2].
- destruct (star_cfg_halted_nil segs ACFG c tr c' Hh Hstar) as [-> _]. reflexivity.
- apply Heq. eapply IH; exact Hstar.
Qed.
#[using="Type"] Lemma sstep_halted_none : forall c e st,
sstep segs c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H; inversion H; subst; cbn; assumption. Qed.
#[using="Type"] Lemma t_alt_unit : forall (f : unit -> TSet), t_eq (t_alt f) (f tt).
Proof.
intros f tr. split; [intros [[] Hf]; exact Hf | intro Hf; exists tt; exact Hf].
Qed.
#[using="Type"] Lemma rz_silent1 : forall c c' T,
node_ok c unit (fun _ => []) (fun _ => c') ->
realizes c' T ->
realizes c T.
Proof.
intros c c' T Hnode Hc.
apply (rz_conseq c (t_alt (fun _ : unit => t_emit [] T))).
- apply (rz_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode).
intros []; exact Hc.
- eapply t_eq_trans;
[ apply (t_alt_unit (fun _ : unit => t_emit [] T))
| apply t_emit_nil_eq; eapply realizes_nonempty; exact Hc ].
Qed.
#[using="Type"] Lemma rz_emit1 : forall c c' e T,
node_ok c unit (fun _ => e) (fun _ => c') ->
realizes c' T ->
realizes c (t_emit e T).
Proof.
intros c c' e T Hnode Hc.
apply (rz_conseq c (t_alt (fun _ : unit => t_emit e T))).
- apply (rz_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode).
intros []; exact Hc.
- apply t_alt_unit.
Qed.
#[using="Type"] Lemma rz_exit : forall ms model x8,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
is_exit_no x8 ->
realizes (mkCfg ms model)
(t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
intros ms model x8 Hh Hsvc Hx8.
set (code := bv_and (ms_gpr ms 0) (Z_to_bv 64 255)).
unfold t_exit.
eapply (rz_emit1 (mkCfg ms model) (mkCfg ms (with_halted code model))).
- apply node_ok_of_pnode; [exact (transparent_exit_no ms model x8 Hsvc Hx8) |]. split.
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
- apply rz_halt. cbn. discriminate.
Qed.
End WithSegs.
