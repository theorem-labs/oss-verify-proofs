(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma live_remove_neq : forall (l : list (Z * Z)) p e, In e (live_remove p l) -> fst e <> p.
Proof.
  intros l p e He. unfold live_remove in He. apply stdpp.base.list_elem_of_In in He.
  apply stdpp.list_basics.list.list_elem_of_filter in He. destruct He as (H & _).
  cbv beta in H. destruct (Z.eqb_spec (fst e) p) as [E|NE]; [cbn in H; destruct H| exact NE].
Qed.

Definition neq (x y : Z) : Prop := x <> y.

Lemma nodup_nth_neq : forall {A} (l : list A) (i j : nat) (x y : A),
  List.NoDup l -> nth_error l i = Some x -> nth_error l j = Some y -> i <> j -> x <> y.
Proof.
  intros A l i j x y ND Hi Hj NE E. subst y.
  assert (Li : (i < length l)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  exact (NE (proj1 (List.NoDup_nth_error l) ND i j Li (eq_trans Hi (eq_sym Hj)))).
Qed.

Section Kit2.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma freed_apart : forall Σ m p n (live' : list (Z * Z)) usp a,
  ART RT Σ m -> In (p, n) (rt_live RT Σ) -> 0 <= n ->
  (forall e, In e live' -> In e (rt_live RT Σ) /\ fst e <> p) -> rt_sp0 RT Σ - STACK_WIN <= usp ->
  aclient live' (rt_frames RT Σ) usp a -> ~ (p <= a < p + n).
Proof using AF.
  intros Σ m p n live' usp a ART0 INP N0 SUB LOW [H|[H|[H|[H|H]]]] Hr.
  - pose proof (af_live_range RT AF Σ m p n ART0 INP). lia.
  - pose proof (client_static_range a H). pose proof (af_live_range RT AF Σ m p n ART0 INP). ul.
  - destruct H as (q & k & Hin & Hq). destruct (SUB _ Hin) as (HinΣ & NE). cbn [fst] in NE.
    destruct (in_split _ _ INP) as (l1 & l2 & EL).
    assert (HIN2 : In (q, k) (l1 ++ l2)).
    { rewrite EL in HinΣ. apply in_app_or in HinΣ. apply in_or_app. destruct HinΣ as [X|[X|X]]; [left; exact X| injection X as E1 E2; lia| right; exact X]. }
    pose proof (af_live_disj RT AF Σ m p n q k l1 l2 ART0 EL HIN2). lia.
  - destruct H as (f & k & Hin & Hf). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & _ & _ & X). specialize (X p n INP). lia.
  - destruct H as (f & k & Hin & Hf). pose proof (af_fshadow_apart RT AF Σ m f k ART0 Hin) as (X & _). specialize (X p n INP). lia.
Qed.

Lemma fobj_sub : forall Σ m a n k n', fobj RT Σ m a n -> k mod 8 = 0 -> 0 <= k -> 0 <= n' -> k + 8 * ((n' + 7) / 8) <= 8 * ((n + 7) / 8) ->
  fobj RT Σ m (a + k) n'.
Proof using AF.
  intros Σ m a n k n' (A8 & N0 & (f & c & Hin & FL & FH) & HB) K8 K0 N0' HK.
  assert (Q : 0 <= (n + 7) / 8) by (apply Z.div_pos; lia). assert (Q' : 0 <= (n' + 7) / 8) by (apply Z.div_pos; lia).
  split; [rewrite Z.add_mod, A8, K8 by lia; reflexivity|]. split; [exact N0'|]. split; [exists f, c; split; [exact Hin| lia]|].
  assert (ES : shad (a + k) = shad a + k / 8).
  { unfold shad. pose proof (Z.div_mod k 8 ltac:(lia)) as DK. rewrite K8 in DK. replace (a + k) with (a + (k / 8) * 8) by lia. rewrite Z.div_add by lia. lia. }
  assert (EK : 0 <= k / 8) by (apply Z.div_pos; lia).
  assert (LE : k / 8 + (n' + 7) / 8 <= (n + 7) / 8) by (pose proof (Z.div_mod k 8 ltac:(lia)) as DK; rewrite K8 in DK; lia).
  replace (Z.to_nat ((n + 7) / 8)) with (Z.to_nat (k / 8) + (Z.to_nat ((n' + 7) / 8) + Z.to_nat ((n + 7) / 8 - k / 8 - (n' + 7) / 8)))%nat in HB by lia.
  rewrite !repeat_app in HB. apply bytes_at_app in HB as [_ HB]. apply bytes_at_app in HB as [HB _].
  rewrite repeat_length, Z2Nat.id in HB by lia. rewrite ES. exact HB.
Qed.

Lemma fobj_pres_fp : forall Σ Σ' live sp W m m' a n, ART RT Σ m -> fobj RT Σ m a n ->
  rt_pres_fp live (rt_frames RT Σ) sp W m m' -> rt_frames RT Σ' = rt_frames RT Σ ->
  (forall r, In r W -> exists f c, In (f, c) (rt_frames RT Σ) /\ f <= fst r /\ snd r <= f + fs_size c) ->
  fobj RT Σ' m' a n.
Proof using AF.
  intros Σ Σ' live sp W m m' a n HA FO PRES FRS HW.
  apply (fobj_agree RT AF Σ Σ' m m' a n HA FO FRS).
  destruct (fobj_shadow_range RT AF Σ m a n HA FO) as (f & c & Hin & S1 & S2 & Q0).
  intros x Hx. cbv beta in Hx. apply PRES.
  - right; right; right; right. exists f, c. split; [exact Hin| lia].
  - apply outside_of_not_in_ranges'. intros (lo & hi & HinW & Hr). destruct (HW _ HinW) as (f' & c' & Hin' & L1 & L2). cbn [fst snd] in L1, L2.
    pose proof (af_fshadow_apart RT AF Σ m f c HA Hin) as (_ & X). specialize (X f' c' Hin'). lia.
Qed.

End Kit2.
