(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YK15.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK16.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK1i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable.R Require Import Cfg.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Lemma is_prefix_app_r {A} : forall (l m a : list A),
is_prefix a l -> is_prefix a (l ++ m).
Proof.
induction l as [|x l IH]; intros m a H.
- destruct a; [apply is_prefix_nil | cbn in H; contradiction].
- destruct a as [|y a]; cbn in *; [exact I|].
destruct H as [-> H]. split; [reflexivity | apply IH; exact H].
Qed.
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
Lemma t_eq_sym : forall T T', t_eq T T' -> t_eq T' T. Proof. firstorder. Qed.
Lemma t_eq_trans : forall T1 T2 T3, t_eq T1 T2 -> t_eq T2 T3 -> t_eq T1 T3.
Proof. firstorder. Qed.
Definition t_nil : TSet := fun tr => tr = [].
Definition t_emit (evs : list event) (T : TSet) : TSet :=
fun tr => is_prefix tr evs \/ exists tr', tr = evs ++ tr' /\ T tr'.
Definition t_alt {I : Type} (f : I -> TSet) : TSet := fun tr => exists i, f i tr.
Definition t_alt2 (A B : TSet) : TSet := fun tr => A tr \/ B tr.
Definition t_exit (code : word) (fs : Fs.Fs) : TSet :=
t_emit [ExitEv code fs] t_nil.
Definition wr_index (buf : list byte) : Type :=
{n : nat | (1 <= n)%nat /\ (n <= length buf)%nat}.
Definition wr_full (buf : list byte) (Hnb : (1 <= length buf)%nat)
: wr_index buf :=
exist _ (length buf) (conj Hnb (Nat.le_refl _)).
Definition t_write_ch (ch : word) (buf : list byte) (T : TSet) : TSet :=
t_alt (fun i : wr_index buf =>
t_emit (map (WriteEv ch) (firstn (proj1_sig i) buf)) T).
Definition t_writes_pick (bufs : list (list byte)) (T : TSet) : TSet :=
fold_right (t_write_ch (Z_to_bv 64 1)) T bufs.
Lemma t_emit_nil_eq : forall T, T [] -> t_eq (t_emit [] T) T.
Proof.
intros T H0 tr. unfold t_emit. split.
- intros [Hp | (tr' & -> & HT)];
[apply is_prefix_nil_r in Hp; subst tr; exact H0 | exact HT].
- intro HT. right. exists tr. split; [reflexivity | exact HT].
Qed.
Lemma t_writes_pick_nil : forall T, t_writes_pick [] T = T. Proof. reflexivity. Qed.
Lemma t_writes_pick_cons : forall buf bufs T,
t_writes_pick (buf :: bufs) T = t_write_ch (Z_to_bv 64 1) buf (t_writes_pick bufs T).
Proof. reflexivity. Qed.
Definition t_writes_ch (ch : word) (bufs : list (list byte)) (T : TSet) : TSet :=
fold_right (fun buf acc => t_emit (map (WriteEv ch) buf) acc) T bufs.
Definition t_writes (bufs : list (list byte)) (T : TSet) : TSet :=
t_writes_ch (Z_to_bv 64 1) bufs T.
Lemma t_writes_nil : forall T, t_writes [] T = T. Proof. reflexivity. Qed.
Lemma t_writes_cons : forall buf bufs T,
t_writes (buf :: bufs) T
= t_emit (map (WriteEv (Z_to_bv 64 1)) buf) (t_writes bufs T).
Proof. reflexivity. Qed.
Lemma t_writes_ch_cons : forall ch buf bufs T,
t_writes_ch ch (buf :: bufs) T
= t_emit (map (WriteEv ch) buf) (t_writes_ch ch bufs T).
Proof. reflexivity. Qed.
Lemma t_emit_has_nil : forall e T, t_emit e T [].
Proof. intros e T. left. apply is_prefix_nil. Qed.
Lemma t_writes_ch_exit_has_nil : forall ch bufs code fs,
t_writes_ch ch bufs (t_exit code fs) [].
Proof.
intros ch [|b bs] code fs; cbn [t_writes_ch fold_right];
apply t_emit_has_nil.
Qed.
Lemma t_writes_ch_exit_iff : forall ch bufs code fs tr,
t_writes_ch ch bufs (t_exit code fs) tr
<-> is_prefix tr (wevents_ch ch bufs ++ [ExitEv code fs]).
Proof.
intros ch bufs; induction bufs as [|buf bufs IH]; intros code fs tr.
- cbn [wevents_ch app]. unfold t_writes_ch, fold_right, t_exit, t_emit, t_nil.
split.
+ intros [H | (tr' & -> & ->)]; [exact H | rewrite app_nil_r; apply is_prefix_refl].
+ intro H. left. exact H.
- rewrite t_writes_ch_cons. cbn [wevents_ch]. rewrite <- app_assoc.
unfold t_emit at 1. split.
+ intros [H | (tr' & -> & Hc)].
* apply is_prefix_app_r; exact H.
* apply is_prefix_app_mono. apply IH. exact Hc.
+ intro H. apply is_prefix_app_split in H as [H | (tr' & -> & H)].
* left; exact H.
* right. exists tr'. split; [reflexivity | apply IH; exact H].
Qed.
Lemma t_writes_exit_iff : forall bufs code fs tr,
t_writes bufs (t_exit code fs) tr
<-> is_prefix tr (wevents bufs ++ [ExitEv code fs]).
Proof.
intros bufs code fs tr. unfold t_writes.
rewrite t_writes_ch_exit_iff, wevents_ch_fd1. reflexivity.
Qed.
Lemma t_alt_wall : forall (ch : word) (rest : list byte) (T : TSet),
T [] -> (1 <= length rest)%nat ->
t_eq (t_alt (fun i : wr_index rest =>
t_emit (map (WriteEv ch) (firstn (proj1_sig i) rest))
(t_emit (map (WriteEv ch) (skipn (proj1_sig i) rest)) T)))
(t_emit (map (WriteEv ch) rest) T).
Proof.
intros ch rest T HT Hnb tr. split.
- intros [[n [Hn1 Hn2]] Hi]. cbn [proj1_sig] in Hi.
destruct Hi as [Hp | (tr1 & -> & Hi)].
+ left. eapply is_prefix_trans; [exact Hp|].
rewrite <- (firstn_skipn n rest) at 2. rewrite map_app.
apply is_prefix_app_r. apply is_prefix_refl.
+ destruct Hi as [Hp | (tr2 & -> & Ht)].
* left.
rewrite <- (firstn_skipn n rest) at 2. rewrite map_app.
apply is_prefix_app_mono. exact Hp.
* right. exists tr2. split; [|exact Ht].
rewrite app_assoc, <- map_app, firstn_skipn. reflexivity.
- intros [Hp | (tr' & -> & Ht)].
+ exists (wr_full rest Hnb). unfold wr_full. cbn [proj1_sig].
rewrite firstn_all. left. exact Hp.
+ exists (wr_full rest Hnb). unfold wr_full. cbn [proj1_sig].
rewrite firstn_all, skipn_all. right.
exists tr'. split; [reflexivity|].
cbn [map]. right. exists tr'. split; [reflexivity | exact Ht].
Qed.
Lemma t_writes_ch_pick_exit_iff : forall ch bufs code fs tr,
Forall (fun b => (1 <= length b)%nat) bufs ->
(fold_right (t_write_ch ch) (t_exit code fs) bufs tr
<-> exists full, wpick ch bufs full /\
is_prefix tr (full ++ [ExitEv code fs])).
Proof.
intros ch bufs code fs tr Hall; revert tr;
induction Hall as [|buf bufs Hnb Hall IH]; intros tr.
- cbn [fold_right]. unfold t_exit, t_emit, t_nil.
split.
+ intros [H | (tr' & -> & ->)].
* exists []. split; [apply wp_nil | exact H].
* exists []. split; [apply wp_nil|].
rewrite app_nil_r. cbn [app]. apply is_prefix_refl.
+ intros (full & Hw & Hp). inversion Hw; subst full.
left. exact Hp.
- cbn [fold_right]. unfold t_write_ch at 1, t_alt at 1.
split.
+ intros [[n [Hn1 Hn2]] Hi]. cbn [proj1_sig] in Hi.
destruct Hi as [H | (tr' & -> & Hc)].
* exists (map (WriteEv ch) (firstn n buf) ++ wevents_ch ch bufs).
split; [apply wp_cons; [exact Hn1 | exact Hn2 | apply wpick_wevents; exact Hall]|].
rewrite <- app_assoc.
eapply is_prefix_trans; [exact H | apply is_prefix_app_r; apply is_prefix_refl].
* apply IH in Hc. destruct Hc as (full & Hw & Hp).
exists (map (WriteEv ch) (firstn n buf) ++ full).
split; [apply wp_cons; assumption|].
rewrite <- app_assoc. apply is_prefix_app_mono. exact Hp.
+ intros (full & Hw & Hp).
inversion Hw as [|buf' bufs' n tr0 Hn1 Hn2 Hw0]; subst.
rewrite <- app_assoc in Hp.
apply is_prefix_app_split in Hp as [Hp | (tr' & -> & Hp)].
* exists (exist _ n (conj Hn1 Hn2)). cbn [proj1_sig]. left. exact Hp.
* exists (exist _ n (conj Hn1 Hn2)). cbn [proj1_sig]. right.
exists tr'. split; [reflexivity|].
apply IH. exists tr0. split; assumption.
Qed.
Lemma t_writes_pick_exit_iff : forall bufs code fs tr,
Forall (fun b => (1 <= length b)%nat) bufs ->
(t_writes_pick bufs (t_exit code fs) tr
<-> exists full, wpick (Z_to_bv 64 1) bufs full /\
is_prefix tr (full ++ [ExitEv code fs])).
Proof. intros. apply t_writes_ch_pick_exit_iff. assumption. Qed.
Section d.
Variable segs : list Segment.
Definition node_ok (c : config) (I : Type)
(evs : I -> list event) (nx : I -> config) : Prop :=
(forall i, sstep_cfg segs ACFG c (evs i) (SNext (nx i)))
/\ (forall e st, sstep_cfg segs ACFG c e st -> exists i, e = evs i /\ st = SNext (nx i)).
Definition pnode_ok (c : config) (I : Type)
(evs : I -> list event) (nx : I -> config) : Prop :=
(forall i, sstep segs c (evs i) (SNext (nx i)))
/\ (forall e st, sstep segs c e st -> exists i, e = evs i /\ st = SNext (nx i)).
Lemma node_ok_of_pnode : forall c I evs nx,
cfg_transparent segs c -> pnode_ok c I evs nx -> node_ok c I evs nx.
Proof.
intros c I evs nx Htr [Hc Hs]. split.
- intros i. apply Htr. apply Hc.
- intros e st Hss. apply Hs. exact (sstep_of_cfg segs ACFG c e st Hss).
Qed.
Lemma transparent_exit : forall ms model x8,
ms_svc_pending ms = Some x8 -> is_exit_no x8 -> cfg_transparent segs (mkCfg ms model).
Proof.
intros ms model x8 Hsvc [E|E]; (eapply transparent_nonalloc_no; [exact Hsvc | exact E | reflexivity]).
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
Lemma realizes_nonempty : forall c T, realizes c T -> T [].
Proof.
intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq].
- exists i0. left. apply is_prefix_nil.
- reflexivity.
- apply Heq. exact IH.
Qed.
Lemma realizes_pclosed : forall c T, realizes c T ->
forall tr tr', T tr -> is_prefix tr' tr -> T tr'.
Proof.
intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
intros tr tr' HT Hp.
- destruct HT as [i [Hpre | (tr0 & -> & HT0)]]; exists i.
+ left. eapply is_prefix_trans; eauto.
+ apply is_prefix_app_split in Hp as [Hp | (tr0' & -> & Hp)].
* left. exact Hp.
* right. exists tr0'. split; [reflexivity | eapply IH; eauto].
- unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
- apply Heq. eapply IH; [apply Heq; exact HT | exact Hp].
Qed.
Lemma realizes_star_only : forall c T, realizes c T ->
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
Lemma realizes_admits : forall c T, realizes c T ->
forall tr, T tr -> obs_trace_cfg segs ACFG c tr.
Proof.
intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
intros tr HT.
- destruct Hnode as [Hcomp _].
destruct HT as [i [Hpre | (tr0 & -> & HT0)]].
+ exists (evs i), (nx i). split; [apply star_cfg_one; apply Hcomp | exact Hpre].
+ destruct (IH i tr0 HT0) as (tr'' & c'' & Hstar & Hp).
exists (evs i ++ tr''), c''.
split; [eapply star_cfg_step; [apply Hcomp | exact Hstar] | apply is_prefix_app_mono; exact Hp].
- unfold t_nil in HT; subst tr. apply obs_trace_cfg_nil.
- apply IH. apply Heq. exact HT.
Qed.
Theorem realizes_obs_iff : forall c T, realizes c T ->
forall tr, obs_trace_cfg segs ACFG c tr <-> T tr.
Proof.
intros c T H tr. split.
- intros (tr' & c' & Hstar & Hp).
eapply realizes_pclosed; [exact H | eapply realizes_star_only; eauto | exact Hp].
- apply realizes_admits; exact H.
Qed.
Lemma sstep_halted_none : forall c e st,
sstep_cfg segs ACFG c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H; inversion H; subst; cbn; assumption. Qed.
Lemma realizes_step : forall c T e c',
realizes c T -> sstep_cfg segs ACFG c e (SNext c') -> exists T', realizes c' T'.
Proof.
intros c T e c' H; revert e c';
induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
intros e c' Hss.
- destruct Hnode as [_ Hsound].
destruct (Hsound e (SNext c') Hss) as (i & _ & Heq2).
inversion Heq2; subst c'. exists (T i). apply Hcont.
- exfalso. apply Hh. eapply sstep_halted_none; exact Hss.
- eapply IH; exact Hss.
Qed.
Lemma realizes_no_sserror : forall c T e,
realizes c T -> ~ sstep_cfg segs ACFG c e SError.
Proof.
intros c T e H; revert e;
induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
intros e Hss.
- destruct Hnode as [_ Hsound].
destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate.
- apply Hh. eapply sstep_halted_none; exact Hss.
- eapply IH; exact Hss.
Qed.
Definition rz_path (c : config) : Prop := exists T, realizes c T.
Theorem realizes_no_error : forall c T, realizes c T -> ~ reaches_error_cfg segs ACFG c.
Proof.
intros c T H.
apply (inv_no_reaches_error_cfg segs ACFG rz_path).
- intros c1 e c2 (T1 & H1) Hss. eapply realizes_step; eauto.
- intros c1 e (T1 & H1) Hss. eapply realizes_no_sserror; eauto.
- exists T; exact H.
Qed.
Lemma t_alt_unit : forall (f : unit -> TSet), t_eq (t_alt f) (f tt).
Proof.
intros f tr. split; [intros [[] Hf]; exact Hf | intro Hf; exists tt; exact Hf].
Qed.
Lemma rz_silent1 : forall c c' T,
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
Lemma rz_emit1 : forall c c' e T,
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
Lemma rz_alt2 : forall c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet)
(a0 : IA) (b0 : IB),
node_ok c (IA + IB) (fun _ => []) nx ->
(forall i, realizes (nx (inl i)) A) ->
(forall i, realizes (nx (inr i)) B) ->
realizes c (t_alt2 A B).
Proof.
intros c IA IB nx A B a0 b0 Hnode HA HB.
assert (HA0 : A []) by (eapply realizes_nonempty; apply (HA a0)).
assert (HB0 : B []) by (eapply realizes_nonempty; apply (HB b0)).
apply (rz_conseq c
(t_alt (fun i : IA + IB =>
t_emit [] (match i with inl _ => A | inr _ => B end)))).
- apply (rz_node c (IA + IB) (fun _ => []) nx
(fun i => match i with inl _ => A | inr _ => B end) (inl a0) Hnode).
intros [i|i]; [apply HA | apply HB].
- intro tr. unfold t_alt2. split.
+ intros [[i|i] Hi];
[ left; exact (proj1 (t_emit_nil_eq A HA0 tr) Hi)
| right; exact (proj1 (t_emit_nil_eq B HB0 tr) Hi) ].
+ intros [H | H];
[ exists (inl a0); exact (proj2 (t_emit_nil_eq A HA0 tr) H)
| exists (inr b0); exact (proj2 (t_emit_nil_eq B HB0 tr) H) ].
Qed.
Lemma rz_silent_allI : forall c (I : Type) (nx : I -> config) (i0 : I) T,
node_ok c I (fun _ => []) nx ->
(forall i, realizes (nx i) T) ->
realizes c T.
Proof.
intros c I nx i0 T Hnode Hc.
assert (HT0 : T []) by (eapply realizes_nonempty; apply (Hc i0)).
apply (rz_conseq c (t_alt (fun _ : I => t_emit [] T))).
- apply (rz_node c I (fun _ => []) nx (fun _ => T) i0 Hnode). exact Hc.
- intro tr. split.
+ intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
+ intro HT. exists i0. exact (proj2 (t_emit_nil_eq T HT0 tr) HT).
Qed.
Lemma node_instr : forall ms model ms',
m_halted model = None ->
m_vm_lazy model = [] ->
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
node_ok (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
intros ms model ms' Hh Hlazy Hsvc Hstep.
apply node_ok_of_pnode; [apply transparent_instr; exact Hsvc|]. split.
- intros []. apply (sstep_instr segs ms model ms' model);
[assumption | assumption |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
- intros e st Hss.
destruct (sstep_instr_inv segs ms model ms' e st Hlazy Hsvc Hstep Hss) as [-> ->].
exists tt. split; reflexivity.
Qed.
Lemma rz_step : forall ms model ms' T,
m_halted model = None ->
m_vm_lazy model = [] ->
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
realizes (mkCfg ms' model) T ->
realizes (mkCfg ms model) T.
Proof.
intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
eapply rz_silent1; [apply node_instr; eassumption | exact Hc].
Qed.
Lemma rz_msteps : forall ms ms' model T,
m_halted model = None ->
m_vm_lazy model = [] ->
msteps segs ms ms' ->
realizes (mkCfg ms' model) T ->
realizes (mkCfg ms model) T.
Proof.
intros ms ms' model T Hh Hlazy Hms;
induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH];
intro Hc; [exact Hc|].
eapply rz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
| apply IH; exact Hc].
Qed.
Lemma node_write1 : forall ms model x8 buf,
m_halted model = None ->
m_vm_lazy model = [] ->
fd1chan model ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = Z_to_bv 64 1 ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
buf_modeled buf ->
(1 <= length buf)%nat ->
node_ok (mkCfg ms model) (wr_index buf)
(fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) buf))
(fun i => mkCfg (advance_past_svc
(set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
model).
Proof.
intros ms model x8 buf Hh Hlazy Hfd Hsvc Hno Hg Hr Hbm Hnb.
apply node_ok_of_pnode; [eapply transparent_nonalloc_no; [exact Hsvc | exact Hno | reflexivity]|]. split.
- intros [n [Hn1 Hn2]]. cbn [proj1_sig].
rewrite <- (apply_effect_copyins_no_write ms (len_word (firstn n buf))
[(ms_gpr ms 1, n)]).
apply (sstep_syscall segs ms model x8
(with_copyins [(ms_gpr ms 1, n)]
(mkEffect (len_word (firstn n buf)) [] [])) model
model (map (WriteEv (Z_to_bv 64 1)) (firstn n buf))).
+ exact Hh.
+ exact Hsvc.
+ apply write1_ok_n; assumption.
+ exact Hh.
+ apply materialize_model_accesses_no_lazy. exact Hlazy.
- intros e st Hss.
destruct (sstep_write_inv segs ms model x8 buf e st
Hh Hlazy Hfd Hsvc Hno Hg Hr Hbm Hnb Hss)
as (n & Hn1 & Hn2 & -> & ->).
exists (exist _ n (conj Hn1 Hn2)). split; reflexivity.
Qed.
Lemma rz_write1 : forall ms model x8 buf T,
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
realizes (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model) T) ->
realizes (mkCfg ms model) (t_write_ch (Z_to_bv 64 1) buf T).
Proof.
intros ms model x8 buf T Hh Hlazy Hfd Hsvc Hno Hg Hr Hbm Hnb Hc.
unfold t_write_ch.
apply (rz_node (mkCfg ms model) (wr_index buf)
(fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) buf))
(fun i => mkCfg (advance_past_svc
(set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
model)
(fun _ => T) (wr_full buf Hnb)).
- apply (node_write1 ms model x8 buf); assumption.
- intros [n [Hn1 Hn2]]. cbn [proj1_sig]. apply Hc; assumption.
Qed.
Lemma rz_exit : forall ms model x8,
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
- apply rz_halt. cbn. discriminate.
Qed.
Lemma rz_munmap : forall ms model x8 T,
m_halted model = None ->
m_vm_lazy model = [] ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 215%Z ->
munmap_args_ok ms model ->
realizes (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) T ->
realizes (mkCfg ms model) T.
Proof.
intros ms model x8 T Hh Hlazy Hsvc Hno Hargs Hc.
eapply rz_silent1; [| exact Hc].
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
End d.
Lemma cat_realizes : forall segs ms model bufs code,
m_halted model = None ->
m_vm_lazy model = [] ->
fd1chan model ->
to_wexit segs ms bufs code ->
bufs_modeled bufs ->
realizes segs (mkCfg ms model) (t_writes_pick bufs (t_exit code (m_fs model))).
Proof.
intros segs ms model bufs code Hh Hlazy Hfd Hte. revert model Hh Hlazy Hfd.
induction Hte as
[ms x8 Hsvc Hx8
| ms x8 buf bufs code Hsvc Hno Hg Hr Hnb Hcont IH
| ms ms' bufs code Hsvc Hstep Hte IH];
intros model Hh Hlazy Hfd Hbm.
- rewrite t_writes_pick_nil. eapply rz_exit; eassumption.
- apply Forall_cons_iff in Hbm as [Hb Hbs].
rewrite t_writes_pick_cons. eapply rz_write1; try eassumption.
intros n Hn1 Hn2. apply IH; assumption.
- eapply rz_step; try eassumption. apply IH; assumption.
Qed.
Lemma exitline_realizes_aux : forall segs ms bufs code model,
to_wexit segs ms bufs code -> bufs = [] ->
m_halted model = None ->
m_vm_lazy model = [] ->
realizes segs (mkCfg ms model) (t_exit code (m_fs model)).
Proof.
intros segs ms bufs code model Hte.
induction Hte as
[ms x8 Hsvc Hx8
| ms x8 buf bufs code Hsvc Hno Hg Hr Hnb Hcont IH
| ms ms' bufs code Hsvc Hstep Hte IH]; intros Hbufs Hh;
[| discriminate Hbufs |]; intro Hlazy.
- eapply rz_exit; eassumption.
- eapply rz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep |].
apply IH; [solve [assumption | reflexivity] | exact Hh | exact Hlazy].
Qed.
Lemma exitline_realizes : forall segs ms code model,
to_wexit segs ms [] code ->
m_halted model = None ->
m_vm_lazy model = [] ->
realizes segs (mkCfg ms model) (t_exit code (m_fs model)).
Proof.
intros segs ms code model Hte Hh Hlazy.
exact (exitline_realizes_aux segs ms [] code model Hte eq_refl Hh Hlazy).
Qed.
Lemma rz_wall1_mut : forall segs model,
m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
(forall ms rest k, to_wall segs (Z_to_bv 64 1) ms rest k ->
buf_modeled rest ->
forall T : TSet, T [] ->
(forall ms', k ms' -> realizes segs (mkCfg ms' model) T) ->
realizes segs (mkCfg ms model)
(t_emit (map (WriteEv (Z_to_bv 64 1)) rest) T))
/\ (forall ms rest k, to_wall_tail segs (Z_to_bv 64 1) ms rest k ->
buf_modeled rest ->
forall T : TSet, T [] ->
(forall ms', k ms' -> realizes segs (mkCfg ms' model) T) ->
realizes segs (mkCfg ms model)
(t_emit (map (WriteEv (Z_to_bv 64 1)) rest) T)).
Proof.
intros segs model Hh Hlazy Hfd.
apply (to_wall_mutind segs (Z_to_bv 64 1)
(fun ms rest k => buf_modeled rest -> forall T : TSet, T [] ->
(forall ms', k ms' -> realizes segs (mkCfg ms' model) T) ->
realizes segs (mkCfg ms model)
(t_emit (map (WriteEv (Z_to_bv 64 1)) rest) T))
(fun ms rest k => buf_modeled rest -> forall T : TSet, T [] ->
(forall ms', k ms' -> realizes segs (mkCfg ms' model) T) ->
realizes segs (mkCfg ms model)
(t_emit (map (WriteEv (Z_to_bv 64 1)) rest) T))).
-
intros ms x8 rest k Hsvc Hno Hg Hr Hnb Hcont IH Hbm T HT Hk.
eapply rz_conseq.
{ apply (rz_node segs (mkCfg ms model) (wr_index rest)
(fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) rest))
(fun i => mkCfg (advance_past_svc
(set_gpr0 ms (len_word (firstn (proj1_sig i) rest))))
model)
(fun i => t_emit (map (WriteEv (Z_to_bv 64 1))
(skipn (proj1_sig i) rest)) T)
(wr_full rest Hnb)).
- apply (node_write1 segs ms model x8 rest); assumption.
- intros [n [Hn1 Hn2]]. cbn [proj1_sig].
apply (IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbm) T HT Hk). }
apply t_alt_wall; [exact HT | exact Hnb].
-
intros ms k Hk Hbm T HT Hcont.
eapply rz_conseq; [apply Hcont; exact Hk|].
cbn [map]. apply t_eq_sym. apply t_emit_nil_eq. exact HT.
-
intros ms rest k Hnb Hw IH Hbm T HT Hk. exact (IH Hbm T HT Hk).
-
intros ms ms' rest k Hsvc Hstep Ht IH Hbm T HT Hk.
eapply rz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
| exact (IH Hbm T HT Hk)].
Qed.
Lemma wall_realizes : forall segs ms model bufs code,
m_halted model = None ->
m_vm_lazy model = [] ->
fd1chan model ->
to_wallexit segs (Z_to_bv 64 1) bufs code ms ->
bufs_modeled bufs ->
realizes segs (mkCfg ms model) (t_writes bufs (t_exit code (m_fs model))).
Proof.
intros segs ms model bufs code Hh Hlazy Hfd Hw Hbm. revert ms Hw Hbm.
induction bufs as [|buf rest IH]; intros ms Hw Hbm.
- exact (exitline_realizes segs ms code model Hw Hh Hlazy).
- destruct Hw as [Hnb Ht]. apply Forall_cons_iff in Hbm as [Hb Hbs].
rewrite t_writes_cons.
eapply (proj2 (rz_wall1_mut segs model Hh Hlazy Hfd)).
+ exact Ht.
+ exact Hb.
+ unfold t_writes. apply t_writes_ch_exit_has_nil.
+ intros ms' Hk. apply IH; [exact Hk | exact Hbs].
Qed.
Lemma twm_realizes_mut : forall segs,
(forall ms model bufs code, YK0v.twm segs ms model bufs code ->
m_halted model = None -> m_vm_lazy model = [] -> fd1chan model -> bufs_modeled bufs ->
realizes segs (mkCfg ms model) (t_writes bufs (t_exit code (m_fs model))))
/\ (forall ms model rest bufs code, YK0v.twm_pend segs ms model rest bufs code ->
m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
buf_modeled rest -> bufs_modeled bufs ->
realizes segs (mkCfg ms model)
(t_emit (map (WriteEv (Z_to_bv 64 1)) rest)
(t_writes bufs (t_exit code (m_fs model)))))
/\ (forall ms model rest bufs code, YK0v.twm_tail segs ms model rest bufs code ->
m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
buf_modeled rest -> bufs_modeled bufs ->
realizes segs (mkCfg ms model)
(t_emit (map (WriteEv (Z_to_bv 64 1)) rest)
(t_writes bufs (t_exit code (m_fs model))))).
Proof.
intros segs.
apply (YK0v.twm_mutind segs
(fun ms model bufs code =>
m_halted model = None -> m_vm_lazy model = [] -> fd1chan model -> bufs_modeled bufs ->
realizes segs (mkCfg ms model) (t_writes bufs (t_exit code (m_fs model))))
(fun ms model rest bufs code =>
m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
buf_modeled rest -> bufs_modeled bufs ->
realizes segs (mkCfg ms model)
(t_emit (map (WriteEv (Z_to_bv 64 1)) rest)
(t_writes bufs (t_exit code (m_fs model)))))
(fun ms model rest bufs code =>
m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
buf_modeled rest -> bufs_modeled bufs ->
realizes segs (mkCfg ms model)
(t_emit (map (WriteEv (Z_to_bv 64 1)) rest)
(t_writes bufs (t_exit code (m_fs model)))))).
-
intros ms model x8 Hsvc Hx8 Hh Hlazy Hfd Hbm. eapply rz_exit; eassumption.
-
intros ms model buf bufs code Hnb Hp IH Hh Hlazy Hfd Hbm.
apply Forall_cons_iff in Hbm as [Hb Hbs].
rewrite t_writes_cons. exact (IH Hh Hlazy Hfd Hb Hbs).
-
intros ms model x8 bufs code Hsvc Hno Hargs Hte IH Hh Hlazy Hfd Hbm.
eapply rz_munmap; try eassumption.
rewrite <- (munmap_model_fs (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model).
apply IH; [rewrite munmap_model_halted; exact Hh
| exact (munmap_model_no_lazy _ _ _ Hlazy)
| apply munmap_model_fd1chan; exact Hfd | exact Hbm].
-
intros ms ms' model bufs code Hsvc Hstep Hte IH Hh Hlazy Hfd Hbm.
eapply rz_step; try eassumption. apply IH; assumption.
-
intros ms model x8 rest bufs code Hsvc Hno Hg Hr Hnb Hcont IH Hh Hlazy Hfd Hbr Hbm.
eapply rz_conseq.
{ apply (rz_node segs (mkCfg ms model) (wr_index rest)
(fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) rest))
(fun i => mkCfg (advance_past_svc
(set_gpr0 ms (len_word (firstn (proj1_sig i) rest))))
model)
(fun i => t_emit (map (WriteEv (Z_to_bv 64 1))
(skipn (proj1_sig i) rest))
(t_writes bufs (t_exit code (m_fs model))))
(wr_full rest Hnb)).
- apply (node_write1 segs ms model x8 rest); assumption.
- intros [n [Hn1 Hn2]]. cbn [proj1_sig].
apply (IH n Hn1 Hn2 Hh Hlazy Hfd (buf_modeled_skipn n rest Hbr) Hbm). }
apply t_alt_wall;
[unfold t_writes; apply t_writes_ch_exit_has_nil | exact Hnb].
-
intros ms model bufs code Hte IH Hh Hlazy Hfd Hbr Hbm.
eapply rz_conseq; [apply IH; assumption|].
cbn [map]. apply t_eq_sym. apply t_emit_nil_eq.
unfold t_writes. apply t_writes_ch_exit_has_nil.
-
intros ms model rest bufs code Hnb Hp IH Hh Hlazy Hfd Hbr Hbm.
exact (IH Hh Hlazy Hfd Hbr Hbm).
-
intros ms ms' model rest bufs code Hsvc Hstep Ht IH Hh Hlazy Hfd Hbr Hbm.
eapply rz_step; try eassumption. exact (IH Hh Hlazy Hfd Hbr Hbm).
Qed.
Lemma twm_realizes : forall segs ms model bufs code,
m_halted model = None ->
m_vm_lazy model = [] ->
fd1chan model ->
YK0v.twm segs ms model bufs code ->
bufs_modeled bufs ->
realizes segs (mkCfg ms model) (t_writes bufs (t_exit code (m_fs model))).
Proof.
intros segs ms model bufs code Hh Hlazy Hfd Hte.
exact (proj1 (twm_realizes_mut segs) ms model bufs code Hte Hh Hlazy Hfd).
Qed.
Definition t_writes_ch_pick (ch : word) (bufs : list (list byte)) (T : TSet) : TSet :=
fold_right (t_write_ch ch) T bufs.
Lemma t_writes_ch_pick_1 : forall bufs T, t_writes_ch_pick (Z_to_bv 64 1) bufs T = t_writes_pick bufs T.
Proof. reflexivity. Qed.
Lemma t_writes_ch_pick_cons : forall ch buf bufs T,
t_writes_ch_pick ch (buf :: bufs) T = t_write_ch ch buf (t_writes_ch_pick ch bufs T).
Proof. reflexivity. Qed.
Lemma node_write_ch : forall segs ms model fd ch x8 buf,
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model -> fd32 fd = fd ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = fd ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
buf_modeled buf ->
(1 <= length buf)%nat ->
node_ok segs (mkCfg ms model) (wr_index buf)
(fun i => map (WriteEv ch) (firstn (proj1_sig i) buf))
(fun i => mkCfg (advance_past_svc
(set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
model).
Proof.
intros segs ms model fd ch x8 buf Hh Hlazy Hfdc H32 Hsvc Hno Hg Hr Hbm Hnb.
apply node_ok_of_pnode; [eapply transparent_nonalloc_no; [exact Hsvc | exact Hno | reflexivity]|]. split.
- intros [n [Hn1 Hn2]]. cbn [proj1_sig].
rewrite <- (apply_effect_copyins_no_write ms (len_word (firstn n buf))
[(ms_gpr ms 1, n)]).
apply (sstep_syscall segs ms model x8
(with_copyins [(ms_gpr ms 1, n)]
(mkEffect (len_word (firstn n buf)) [] [])) model
model (map (WriteEv ch) (firstn n buf))).
+ exact Hh.
+ exact Hsvc.
+ eapply write_ch_ok_n; eassumption.
+ exact Hh.
+ apply materialize_model_accesses_no_lazy. exact Hlazy.
- intros e st Hss.
destruct (sstep_write_ch_inv segs fd ch H32 ms model x8 buf e st
Hh Hlazy Hfdc Hsvc Hno Hg Hr Hbm Hnb Hss)
as (n & Hn1 & Hn2 & -> & ->).
exists (exist _ n (conj Hn1 Hn2)). split; reflexivity.
Qed.
Lemma rz_write_ch : forall segs ms model fd ch x8 buf T,
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model -> fd32 fd = fd ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = fd ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
buf_modeled buf ->
(1 <= length buf)%nat ->
(forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
realizes segs
(mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model) T) ->
realizes segs (mkCfg ms model) (t_write_ch ch buf T).
Proof.
intros segs ms model fd ch x8 buf T Hh Hlazy Hfdc H32 Hsvc Hno Hg Hr Hbm Hnb Hc.
unfold t_write_ch.
apply (rz_node segs (mkCfg ms model) (wr_index buf)
(fun i => map (WriteEv ch) (firstn (proj1_sig i) buf))
(fun i => mkCfg (advance_past_svc
(set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
model)
(fun _ => T) (wr_full buf Hnb)).
- eapply node_write_ch; eassumption.
- intros [n [Hn1 Hn2]]. cbn [proj1_sig]. apply Hc; assumption.
Qed.
Lemma cat_realizes_ch : forall segs fd ch ms model bufs code,
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model -> fd32 fd = fd ->
to_wexit_ch segs fd ms bufs code ->
bufs_modeled bufs ->
realizes segs (mkCfg ms model) (t_writes_ch_pick ch bufs (t_exit code (m_fs model))).
Proof.
intros segs fd ch ms model bufs code Hh Hlazy Hfdc H32 Hte.
revert model Hh Hlazy Hfdc.
induction Hte as
[ms x8 Hsvc Hx8
| ms x8 buf bufs code Hsvc Hno Hg Hr Hnb Hcont IH
| ms ms' bufs code Hsvc Hstep Hte IH];
intros model Hh Hlazy Hfdc Hbm.
- eapply rz_exit; eassumption.
- apply Forall_cons_iff in Hbm as [Hb Hbs].
rewrite t_writes_ch_pick_cons. eapply rz_write_ch; try eassumption.
intros n Hn1 Hn2. apply IH; assumption.
- eapply rz_step; try eassumption. apply IH; assumption.
Qed.
