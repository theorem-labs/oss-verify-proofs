From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YK11 YK0i YK0n YK15 YM06 YM06_cf YO0d YK15_cfw.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Uniform.
Import ListNotations.
Open Scope bv_scope.
Section a. Context {fx : YK11.FPState}.
Variable B : malloc_syms.
Let segs := ms_segs B.
Lemma crz_alt2 : forall c (IA IB : Type) (nx : IA + IB -> config) (A B' : TSet)
(a0 : IA) (b0 : IB),
node_ok segs c (IA + IB) (fun _ => []) nx -> ~ budget_refused_at segs c -> place_uniform segs c -> canon_fit_at segs c ->
(forall i, crealizes B (nx (inl i)) A) ->
(forall i, crealizes B (nx (inr i)) B') ->
crealizes B c (t_alt2 A B').
Proof using.
intros c IA IB nx A B' a0 b0 Hn Hb Hp Hf HA HB. apply crealizes_intro.
- exact (rz_alt2 segs c IA IB nx A B' a0 b0 Hn (fun i => crealizes_realizes B _ _ (HA i))
    (fun i => crealizes_realizes B _ _ (HB i))).
- apply (cut_free_node segs c (IA + IB) _ nx Hn Hb).
  intros [i|i]; [exact (crealizes_cut_free B _ _ (HA i)) | exact (crealizes_cut_free B _ _ (HB i))].
- apply (uniform_node segs c (IA + IB) _ nx Hn Hp Hf).
  intros [i|i]; [exact (crealizes_uniform B _ _ (HA i)) | exact (crealizes_uniform B _ _ (HB i))].
Qed.
Lemma place_uniform_allI : forall c (I : Type) (nx : I -> config) T,
node_ok segs c I (fun _ => []) nx -> (forall i, crealizes B (nx i) T) -> place_uniform segs c.
Proof using.
intros c I nx T [_ Hc] H x8 len _ e1 c1 e2 c2 H1 H2.
destruct (Hc e1 _ H1) as (i & -> & E1). destruct (Hc e2 _ H2) as (j & -> & E2).
injection E1 as ->. injection E2 as ->. split; [reflexivity|]. intros tr.
rewrite (realizes_obs_iff segs (nx i) T (crealizes_realizes B _ _ (H i)) (crealizes_cut_free B _ _ (H i)) tr).
exact (iff_sym (realizes_obs_iff segs (nx j) T (crealizes_realizes B _ _ (H j)) (crealizes_cut_free B _ _ (H j)) tr)).
Qed.
Lemma crz_silent_allI : forall c (I : Type) (nx : I -> config) (i0 : I) T,
node_ok segs c I (fun _ => []) nx -> ~ budget_refused_at segs c -> canon_fit_at segs c ->
(forall i, crealizes B (nx i) T) ->
crealizes B c T.
Proof using.
intros c I nx i0 T Hn Hb Hf H. apply crealizes_intro.
- exact (rz_silent_allI segs c I nx i0 T Hn (fun i => crealizes_realizes B _ _ (H i))).
- exact (cut_free_node segs c I _ nx Hn Hb (fun i => crealizes_cut_free B _ _ (H i))).
- exact (uniform_node segs c I _ nx Hn (place_uniform_allI c I nx T Hn H) Hf (fun i => crealizes_uniform B _ _ (H i))).
Qed.
Lemma crz_alt2_sys : forall ms model x8 (IA IB : Type) (nx : IA + IB -> config) (A B' : TSet)
(a0 : IA) (b0 : IB),
ms_svc_pending ms = Some x8 -> alloc_no_b (bv_unsigned x8) = false ->
node_ok segs (mkCfg ms model) (IA + IB) (fun _ => []) nx ->
(forall i, crealizes B (nx (inl i)) A) ->
(forall i, crealizes B (nx (inr i)) B') ->
crealizes B (mkCfg ms model) (t_alt2 A B').
Proof using.
intros ms model x8 IA IB nx A B' a0 b0 Hsvc Hno Hn HA HB.
exact (crz_alt2 _ IA IB nx A B' a0 b0 Hn (nr_node_sys segs ms model x8 _ _ nx Hn Hsvc Hno)
  (place_uniform_sys segs ms model x8 Hsvc Hno) (canon_fit_sys segs ms model x8 Hsvc Hno) HA HB).
Qed.
Lemma crz_silent_allI_sys : forall ms model x8 (I : Type) (nx : I -> config) (i0 : I) T,
ms_svc_pending ms = Some x8 -> alloc_no_b (bv_unsigned x8) = false ->
node_ok segs (mkCfg ms model) I (fun _ => []) nx ->
(forall i, crealizes B (nx i) T) ->
crealizes B (mkCfg ms model) T.
Proof using.
intros ms model x8 I nx i0 T Hsvc Hno Hn H.
exact (crz_silent_allI _ I nx i0 T Hn (nr_node_sys segs ms model x8 I _ nx Hn Hsvc Hno)
  (canon_fit_sys segs ms model x8 Hsvc Hno) H).
Qed.
End a.
