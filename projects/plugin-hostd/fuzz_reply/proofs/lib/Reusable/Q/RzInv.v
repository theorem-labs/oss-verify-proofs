From Stdlib Require Import List Classical_Prop IndefiniteDescription.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK15 YM06.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.R Require Import Cfg.
Import ListNotations.
Section a. Context {fx : YK11.FPState}.
Variable segs : list Segment.
Record rz_pkg := RzPkg { pk_J : Type; pk_evs : pk_J -> list event; pk_nx : pk_J -> config; pk_T : pk_J -> TSet;
pk_j0 : pk_J }.
Definition pk_good (c : config) (X : TSet) (p : rz_pkg) : Prop :=
node_ok segs c (pk_J p) (pk_evs p) (pk_nx p) /\ (forall j, realizes segs (pk_nx p j) (pk_T p j)) /\
(t_eq X (t_alt (fun j => t_emit (pk_evs p j) (pk_T p j))) \/
((forall j, pk_evs p j = []) /\ t_eq X (t_alt (pk_T p)))).
Lemma realizes_pkg : forall c X, realizes segs c X -> ~ budget_refused_at segs c -> m_halted (cfg_model c) = None ->
exists p, pk_good c X p.
Proof using.
intros c X H.
induction H as [c I evs nx T i0 Hn Hc IH | c Hh | c T T' H IH Heq | c I nx T i0 Hn Hc IH | c T Hb];
intros Hnb Hnh.
- exists (RzPkg I evs nx T i0). split; [exact Hn|]. split; [exact Hc|]. left. apply t_eq_refl.
- exfalso. exact (Hh Hnh).
- destruct (IH Hnb Hnh) as (p & Hn & Hc & [E | [E1 E]]); exists p; (split; [exact Hn|]); (split; [exact Hc|]).
+ left. exact (t_eq_trans _ _ _ (t_eq_sym _ _ Heq) E).
+ right. split; [exact E1 | exact (t_eq_trans _ _ _ (t_eq_sym _ _ Heq) E)].
- exists (RzPkg I (fun _ => []) nx T i0). split; [exact Hn|]. split; [exact Hc|].
right. split; [reflexivity | apply t_eq_refl].
- exfalso. exact (Hnb Hb).
Qed.
Lemma realizes_union : forall c (I : Type) (T : I -> TSet) (i0 : I),
~ budget_refused_at segs c -> m_halted (cfg_model c) = None ->
(forall i, realizes segs c (T i)) -> realizes segs c (t_alt T).
Proof using.
intros c I T i0 Hnb Hnh HR.
pose (pk := fun i => proj1_sig (constructive_indefinite_description _ (realizes_pkg c (T i) (HR i) Hnb Hnh))).
assert (G : forall i, pk_good c (T i) (pk i)).
{ intros i. exact (proj2_sig (constructive_indefinite_description _ (realizes_pkg c (T i) (HR i) Hnb Hnh))). }
set (P := fun i => pk_J (pk i)). set (K := sigT P).
set (kevs := fun k : K => pk_evs (pk (projT1 k)) (projT2 k)).
set (knx := fun k : K => pk_nx (pk (projT1 k)) (projT2 k)).
set (kT := fun k : K => pk_T (pk (projT1 k)) (projT2 k)).
set (k0 := @existT I P i0 (pk_j0 (pk i0)) : K).
assert (Hch : forall k, realizes segs (knx k) (kT k)).
{ intros [i j]. unfold knx, kT. cbn [projT1 projT2]. destruct (G i) as (_ & Hc & _). apply Hc. }
assert (Hcomp : forall k, sstep_cfg segs ACFG c (kevs k) (SNext (knx k))).
{ intros [i j]. unfold knx, kevs. cbn [projT1 projT2]. destruct (G i) as ([Hc _] & _ & _). apply Hc. }
assert (Hsnd : forall e st, sstep_cfg segs ACFG c e st -> exists k, e = kevs k /\ st = SNext (knx k)).
{ intros e st Hs. destruct (G i0) as ([_ Hs0] & _ & _). destruct (Hs0 e st Hs) as (j & -> & ->).
exists (@existT I P i0 j). split; reflexivity. }
destruct (classic (exists i, T i [])) as [[i1 Hi1] | Hnone].
- apply (rz_conseq segs c (t_alt (fun k => t_emit (kevs k) (kT k)))).
+ exact (rz_node segs c K kevs knx kT k0 (conj Hcomp Hsnd) Hch).
+ intros tr. split.
* intros [[i j] Ht]. unfold kevs, kT in Ht. cbn [projT1 projT2] in Ht.
destruct (G i) as (_ & _ & [E | [E1 E]]).
-- exists i. apply E. exists j. exact Ht.
-- rewrite E1 in Ht. destruct Ht as [Hp | (tr' & -> & Ht)].
++ apply is_prefix_nil_r in Hp. subst tr. exists i1. exact Hi1.
++ exists i. apply E. exists j. exact Ht.
* intros [i Ht]. destruct (G i) as (_ & _ & [E | [E1 E]]).
-- apply E in Ht. destruct Ht as [j Ht]. exists (@existT I P i j). exact Ht.
-- apply E in Ht. destruct Ht as [j Ht]. exists (@existT I P i j). unfold kevs, kT. cbn [projT1 projT2].
rewrite E1. right. exists tr. split; [reflexivity | exact Ht].
- assert (S : forall i, (forall j, pk_evs (pk i) j = []) /\ t_eq (T i) (t_alt (pk_T (pk i)))).
{ intros i. destruct (G i) as (_ & _ & [E | S]); [|exact S]. exfalso. apply Hnone. exists i.
apply E. exists (pk_j0 (pk i)). left. apply is_prefix_nil. }
apply (rz_conseq segs c (t_alt kT)).
+ apply (rz_silent segs c K knx kT k0); [split|exact Hch].
* intros [i j]. pose proof (Hcomp (@existT I P i j)) as Hc. unfold kevs in Hc. cbn [projT1 projT2] in Hc.
rewrite (proj1 (S i) j) in Hc. exact Hc.
* intros e st Hs. destruct (Hsnd e st Hs) as ([i j] & -> & ->). exists (@existT I P i j).
split; [unfold kevs; cbn [projT1 projT2]; exact (proj1 (S i) j) | reflexivity].
+ intros tr. split.
* intros [[i j] Ht]. exists i. apply (proj2 (S i)). exists j. exact Ht.
* intros [i Ht]. apply (proj2 (S i)) in Ht. destruct Ht as [j Ht]. exists (@existT I P i j). exact Ht.
Qed.
Lemma realizes_det_inv : forall c c' T,
node_ok segs c unit (fun _ => []) (fun _ => c') ->
~ budget_refused_at segs c -> m_halted (cfg_model c) = None -> m_halted (cfg_model c') = None ->
realizes segs c T -> realizes segs c' T.
Proof using.
intros c c' T [_ Hdet] Hnb Hnh Hnh' H.
destruct (classic (budget_refused_at segs c')) as [Hb' | Hnb']; [apply rz_cut; exact Hb'|].
destruct (realizes_pkg c T H Hnb Hnh) as (p & [Hc _] & Hch & HE).
assert (D : forall j, pk_evs p j = [] /\ pk_nx p j = c').
{ intros j. destruct (Hdet _ _ (Hc j)) as ([] & E1 & E2). injection E2 as E2. split; [exact E1 | exact E2]. }
destruct HE as [E | [_ E]].
- apply (rz_conseq segs c' (t_alt (fun j => t_emit [] (pk_T p j)))).
+ apply (realizes_union c' (pk_J p) _ (pk_j0 p) Hnb' Hnh'). intros j. apply realizes_emit_nil.
rewrite <- (proj2 (D j)). apply Hch.
+ intros tr. split.
* intros [j Ht]. apply E. exists j. cbn beta in Ht |- *. rewrite (proj1 (D j)). exact Ht.
* intros Ht. apply E in Ht. destruct Ht as [j Ht]. exists j. cbn beta in Ht |- *. rewrite (proj1 (D j)) in Ht.
exact Ht.
- apply (rz_conseq segs c' (t_alt (pk_T p))).
+ apply (realizes_union c' (pk_J p) _ (pk_j0 p) Hnb' Hnh'). intros j. rewrite <- (proj2 (D j)). apply Hch.
+ apply t_eq_sym. exact E.
Qed.
Lemma SR_det_inv : forall ms model ms' Q,
m_halted model = None -> m_vm_lazy model = [] -> ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
SR segs (mkCfg ms model) Q -> SR segs (mkCfg ms' model) Q.
Proof using.
intros ms model ms' Q Hh Hlz Hsvc Hstep H T HK.
exact (realizes_det_inv (mkCfg ms model) (mkCfg ms' model) T (node_instr segs ms model ms' Hh Hlz Hsvc Hstep)
(budget_refused_at_no_lazy_instr segs ms model Hlz Hsvc) Hh Hh (H T HK)).
Qed.
End a.
