(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import ShapeAlgBase ShapeCfg NodesCfg LedgerCfg LazyCfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma maps_subtract_app : forall l1 l2 lo hi,
  maps_subtract (l1 ++ l2) lo hi = maps_subtract l1 lo hi ++ maps_subtract l2 lo hi.
Proof.
  induction l1 as [|[a s] l1 IH]; intros l2 lo hi; [reflexivity|].
  cbn [app maps_subtract]. rewrite IH, app_assoc. reflexivity.
Qed.

Lemma maps_subtract_all_app : forall cuts l1 l2,
  maps_subtract_all (l1 ++ l2) cuts = maps_subtract_all l1 cuts ++ maps_subtract_all l2 cuts.
Proof.
  induction cuts as [|[a n] cuts IH]; intros l1 l2; [reflexivity|].
  cbn [maps_subtract_all]. rewrite maps_subtract_app. apply IH.
Qed.

Lemma maps_subtract_all_nil : forall cuts, maps_subtract_all [] cuts = [].
Proof. induction cuts as [|[a n] cuts IH]; [reflexivity|]. cbn [maps_subtract_all maps_subtract]. exact IH. Qed.

(* [comment removed for export] *)
Lemma maps_subtract_inside_nil : forall l lo hi,
  Forall (fun p => lo <= e_lo p /\ e_hi p <= hi) l -> maps_subtract l lo hi = [].
Proof.
  induction l as [|[a s] l IH]; intros lo hi H; [reflexivity|].
  inversion H as [|? ? [H1 H2] Hl]; subst. cbn [maps_subtract].
  unfold e_lo, e_hi, e_sz in H1, H2. cbn [fst snd] in H1, H2.
  rewrite (iv_subtract_inside a s lo hi H1 H2). cbn [app]. exact (IH lo hi Hl).
Qed.

(* [comment removed for export] *)
Lemma maps_subtract_keeps_inside : forall l lo hi p0,
  lo <= hi -> hi < 2 ^ 64 ->
  Forall (fun q => 0 < e_sz q /\ e_inside q p0) l ->
  Forall (fun q => 0 < e_sz q /\ e_inside q p0) (maps_subtract l lo hi).
Proof.
  intros l lo hi p0 Hle Hhi Hl. apply Forall_forall. intros q Hq.
  assert (Hpos : Forall (fun p => 0 < e_sz p) l) by (eapply Forall_impl; [|exact Hl]; intros p [H _]; exact H).
  destruct (maps_subtract_In l lo hi q Hle Hhi Hpos Hq) as (p & Hp & Hqpos & Hin & _).
  destruct (proj1 (Forall_forall _ _) Hl p Hp) as [_ Hpin].
  split; [exact Hqpos|]. unfold e_inside in *. lia.
Qed.

Definition cut_ok (c : word * word) : Prop := e_hi c < 2 ^ 64.

Lemma msa_keeps_inside : forall cuts l p0,
  Forall cut_ok cuts ->
  Forall (fun q => 0 < e_sz q /\ e_inside q p0) l ->
  Forall (fun q => 0 < e_sz q /\ e_inside q p0) (maps_subtract_all l cuts).
Proof.
  induction cuts as [|[a n] cuts IH]; intros l p0 Hc Hl; [exact Hl|].
  inversion Hc as [|? ? Hc1 Hcs]; subst. cbn [maps_subtract_all]. apply IH; [exact Hcs|].
  apply maps_subtract_keeps_inside; [pose proof (u64_range n); lia | exact Hc1 | exact Hl].
Qed.

(* [comment removed for export] *)
Lemma msa_inside_cut_nil : forall cuts l p0 r,
  Forall cut_ok cuts -> In r cuts -> e_inside p0 r ->
  Forall (fun q => 0 < e_sz q /\ e_inside q p0) l ->
  maps_subtract_all l cuts = [].
Proof.
  induction cuts as [|[a n] cuts IH]; intros l p0 r Hc Hr Hin Hl; [contradiction|].
  inversion Hc as [|? ? Hc1 Hcs]; subst. cbn [maps_subtract_all].
  destruct Hr as [<- | Hr].
  - rewrite maps_subtract_inside_nil; [apply maps_subtract_all_nil|].
    eapply Forall_impl; [|exact Hl]. intros q [_ Hq]. unfold e_inside, e_hi, e_lo, e_sz in *.
    cbn [fst snd] in *. lia.
  - apply (IH _ p0 r Hcs Hr Hin).
    apply maps_subtract_keeps_inside; [pose proof (u64_range n); lia | exact Hc1 | exact Hl].
Qed.

Definition e_inside_b (p r : word * word) : bool := (e_lo r <=? e_lo p) && (e_hi p <=? e_hi r).
Definition eager_bound (lazy maps : list (word * word)) : Z :=
  fold_right (fun p acc => (if existsb (e_inside_b p) lazy then 0 else e_sz p) + acc) 0 maps.

Theorem eager_used_le_bound : forall m,
  Forall (fun p => 0 < e_sz p) (vm_maps (m_vmmaps m)) ->
  Forall cut_ok (vm_noaccess (m_vmmaps m)) -> Forall cut_ok (m_vm_lazy m) ->
  eager_used m <= eager_bound (m_vm_lazy m) (vm_maps (m_vmmaps m)).
Proof.
  intros m Hpos Hna Hlz. unfold eager_used, vm_backed_maps.
  set (na := vm_noaccess (m_vmmaps m)) in *. set (lz := m_vm_lazy m) in *.
  induction (vm_maps (m_vmmaps m)) as [|p maps IH]; cbn [eager_bound fold_right].
  - rewrite !maps_subtract_all_nil. cbn. lia.
  - inversion Hpos as [|? ? Hp Hps]; subst.
    change (p :: maps) with ([p] ++ maps). rewrite !maps_subtract_all_app, live_bytes_app.
    specialize (IH Hps). fold (eager_bound lz maps) in *.
    assert (Hself : Forall (fun q => 0 < e_sz q /\ e_inside q p) [p]).
    { constructor; [|constructor]. split; [exact Hp | unfold e_inside; lia]. }
    destruct (existsb (e_inside_b p) lz) eqn:E.
    + apply existsb_exists in E as (r & Hr & Hb). unfold e_inside_b in Hb.
      apply andb_true_iff in Hb as [B1 B2]. apply Z.leb_le in B1, B2.
      rewrite (msa_inside_cut_nil lz (maps_subtract_all [p] na) p r Hlz Hr ltac:(unfold e_inside; lia)
                 (msa_keeps_inside na [p] p Hna Hself)).
      cbn [live_bytes]. lia.
    + pose proof (live_bytes_maps_subtract_all_le lz (maps_subtract_all [p] na)) as H1.
      pose proof (live_bytes_maps_subtract_all_le na [p]) as H2.
      rewrite live_bytes_cons in H2. cbn [live_bytes] in H2. lia.
Qed.
