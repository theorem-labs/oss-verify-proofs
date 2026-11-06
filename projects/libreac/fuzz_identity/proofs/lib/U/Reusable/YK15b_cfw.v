From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK11 YK0i YK0n YK15 YM06 YM06_cf YO0d YK15_cfw.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import SlotAgree AgreeLift.
Import ListNotations.
Open Scope bv_scope.
Section a. Context {fx : YK11.FPState}.
Variable B : malloc_syms.
Let segs := ms_segs B.
Lemma crz_alt2 : forall c (IA IB : Type) (nx : IA + IB -> config) (A B' : TSet)
(a0 : IA) (b0 : IB),
node_ok segs c (IA + IB) (fun _ => []) nx -> ~ budget_refused_at segs c ->
(forall i, crealizes B (nx (inl i)) A) ->
(forall i, crealizes B (nx (inr i)) B') ->
crealizes B c (t_alt2 A B').
Proof using.
intros c IA IB nx A B' a0 b0 Hn Hb HA HB. split.
- exact (rz_alt2 segs c IA IB nx A B' a0 b0 Hn (fun i => proj1 (HA i)) (fun i => proj1 (HB i))).
- apply (cut_free_node segs c (IA + IB) _ nx Hn Hb).
intros [i|i]; [exact (proj2 (HA i)) | exact (proj2 (HB i))].
Qed.
Lemma crz_silent_allI : forall c (I : Type) (nx : I -> config) (i0 : I) T,
node_ok segs c I (fun _ => []) nx -> ~ budget_refused_at segs c ->
(forall i, crealizes B (nx i) T) ->
crealizes B c T.
Proof using.
intros c I nx i0 T Hn Hb H. split.
- exact (rz_silent_allI segs c I nx i0 T Hn (fun i => proj1 (H i))).
- exact (cut_free_node segs c I _ nx Hn Hb (fun i => proj2 (H i))).
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
exact (crz_alt2 _ IA IB nx A B' a0 b0 Hn (nr_node_sys segs ms model x8 _ _ nx Hn Hsvc Hno) HA HB).
Qed.
Lemma crz_silent_allI_sys : forall ms model x8 (I : Type) (nx : I -> config) (i0 : I) T,
ms_svc_pending ms = Some x8 -> alloc_no_b (bv_unsigned x8) = false ->
node_ok segs (mkCfg ms model) I (fun _ => []) nx ->
(forall i, crealizes B (nx i) T) ->
crealizes B (mkCfg ms model) T.
Proof using.
intros ms model x8 I nx i0 T Hsvc Hno Hn H.
exact (crz_silent_allI _ I nx i0 T Hn (nr_node_sys segs ms model x8 I _ nx Hn Hsvc Hno) H).
Qed.
End a.
