(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Placement.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import RelSpec MmapSim.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
(* 08b1429: a PROT_NONE grant lands where Linux puts it ([Placement.linux_place_is],
   as in the model's [Common/RefNodes.grant_ok_na]); the admissibility part is kept
   for the consumers that read a grant as a placement. *)
Definition grant_ok_na (hint : word) (m : Model) (a : word) (n : Z) : bool :=
  linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a && place_ok (m_vmmaps m) a n.

Lemma grant_ok_grant_ok_na : forall hint m a n,
  grant_ok hint m a n = true -> grant_ok_na hint m a n = true.
Proof.
  intros hint m a n H. unfold grant_ok_na.
  rewrite (grant_ok_place hint m a n H), (grant_ok_place_ok hint m a n H). reflexivity.
Qed.

Lemma grant_ok_na_place_ok : forall hint m a n,
  grant_ok_na hint m a n = true -> place_ok (m_vmmaps m) a n = true.
Proof. intros hint m a n H. unfold grant_ok_na in H. apply andb_true_iff in H as [_ H]. exact H. Qed.

Lemma grant_ok_na_unpack : forall hint m a n,
  grant_ok_na hint m a n = true ->
  bv_unsigned a mod page_size = 0 /\ 0 < bv_unsigned a /\
  bv_unsigned a + n <= alloc_top (m_vmmaps m) /\
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n) = true.
Proof. intros hint m a n H. exact (place_ok_unpack _ _ _ (grant_ok_na_place_ok hint m a n H)). Qed.

Lemma u64_lit_gap : forall z, 0 <= z -> z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z H0 H1. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  unfold bv_modulus. change (Z.of_N 64) with 64. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition gap_floor : Z := 0x100000000.

Lemma gap_floor_val : gap_floor = 4294967296.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition cand (N : Z) (j : nat) : Z := gap_floor + Z.of_nat j * (2 * N).

Definition zconflict (a n : Z) (p : word * word) : Prop :=
  a < bv_unsigned (fst p) + bv_unsigned (snd p) /\ bv_unsigned (fst p) < a + n.

Definition zconflictb (a n : Z) (p : word * word) : bool :=
  (a <? bv_unsigned (fst p) + bv_unsigned (snd p)) && (bv_unsigned (fst p) <? a + n).

Lemma zconflictb_spec : forall a n p, zconflictb a n p = true <-> zconflict a n p.
Proof.
  intros a n p. unfold zconflictb, zconflict. rewrite andb_true_iff, !Z.ltb_lt. tauto.
Qed.

Lemma cand_spacing : forall N j k, 0 <= N -> (j < k)%nat -> cand N j + 2 * N <= cand N k.
Proof. intros N j k HN H. unfold cand, gap_floor. nia. Qed.

(* [comment removed for export] *)
Lemma conflict_unique : forall N n p j k,
  0 <= n <= N -> bv_unsigned (snd p) <= N ->
  zconflict (cand N j) n p -> zconflict (cand N k) n p -> j = k.
Proof.
  intros N n p j k Hn Hs [A1 A2] [B1 B2].
  destruct (Nat.lt_trichotomy j k) as [Hlt | [Heq | Hgt]]; [| exact Heq |].
  - pose proof (cand_spacing N j k ltac:(lia) Hlt). lia.
  - pose proof (cand_spacing N k j ltac:(lia) Hgt). lia.
Qed.

(* [comment removed for export] *)
Lemma filter_keep_all_but_one : forall (P : nat -> bool) (js : list nat),
  List.NoDup js ->
  (forall j k, In j js -> In k js -> P j = true -> P k = true -> j = k) ->
  (length js <= S (length (List.filter (fun j => negb (P j)) js)))%nat.
Proof.
  intros P js Hnd Huniq. induction js as [|j js IH]; [cbn; lia|].
  inversion Hnd as [|x l Hnotin Hnd']; subst.
  cbn [List.filter List.length]. destruct (P j) eqn:Pj; cbn [negb].
  - (* [comment removed for export] *)
    assert (Hall : forall k, In k js -> P k = false).
    { intros k Hk. destruct (P k) eqn:Pk; [|reflexivity].
      exfalso. assert (j = k) by (apply Huniq; [left; reflexivity | right; exact Hk | exact Pj | exact Pk]).
      subst k. exact (Hnotin Hk). }
    assert (Hid : List.filter (fun j0 => negb (P j0)) js = js).
    { clear -Hall. induction js as [|k js IH]; [reflexivity|].
      cbn [List.filter]. rewrite (Hall k (or_introl eq_refl)). cbn [negb]. f_equal. apply IH.
      intros k' Hk'. apply Hall. right. exact Hk'. }
    rewrite Hid. lia.
  - cbn [List.length].
    assert (IH' : (length js <= S (length (List.filter (fun j0 : nat => negb (P j0)) js)))%nat).
    { apply IH; [exact Hnd'|]. intros a b Ha Hb Pa Pb. apply Huniq; [right | right | |]; assumption. }
    lia.
Qed.

Lemma pick_candidate : forall (N n : Z) (l : list (word * word)) (js : list nat),
  0 <= n <= N ->
  Forall (fun p => bv_unsigned (snd p) <= N) l ->
  List.NoDup js -> (length l < length js)%nat ->
  exists j, In j js /\ forall p, In p l -> ~ zconflict (cand N j) n p.
Proof.
  intros N n l. induction l as [|p l IH]; intros js Hn Hsz Hnd Hlen.
  - destruct js as [|j js]; [cbn in Hlen; lia|]. exists j. split; [left; reflexivity | intros q []].
  - inversion Hsz as [|p' l' Hp Hl]; subst.
    set (js' := List.filter (fun j => negb (zconflictb (cand N j) n p)) js).
    assert (Hnd' : List.NoDup js') by (apply List.NoDup_filter; exact Hnd).
    assert (Hlen' : (length js <= S (length js'))%nat).
    { apply filter_keep_all_but_one; [exact Hnd|].
      intros j k _ _ Pj Pk. apply zconflictb_spec in Pj. apply zconflictb_spec in Pk.
      eapply (conflict_unique N n p); eassumption. }
    destruct (IH js' Hn Hl Hnd' ltac:(cbn in Hlen; lia)) as (j & Hj & Hfree).
    exists j. unfold js' in Hj. apply filter_In in Hj as [Hj Hnp]. split; [exact Hj|].
    intros q [<- | Hq].
    + intros Hc. apply zconflictb_spec in Hc. rewrite Hc in Hnp. discriminate.
    + apply Hfree. exact Hq.
Qed.

Lemma region_free_of_noconflict : forall l (a n : Z),
  0 <= a -> 0 <= n -> a + n < 2 ^ 64 ->
  (forall p, In p l -> ~ zconflict a n p) ->
  region_free l (Z_to_bv 64 a) (Z_to_bv 64 n) = true.
Proof.
  induction l as [|[b s] l IH]; intros a n Ha Hn Hnw Hno; [reflexivity|].
  cbn [region_free]. rewrite IH; [| lia | lia | lia | intros p Hp; apply Hno; right; exact Hp].
  rewrite andb_true_r. apply negb_true_iff. unfold iv_overlap.
  rewrite !u64_lit_gap by lia.
  specialize (Hno (b, s) (or_introl eq_refl)). unfold zconflict in Hno. cbn [fst snd] in Hno.
  apply andb_false_iff. destruct (Z_lt_le_dec a (bv_unsigned b + bv_unsigned s)).
  - right. apply Z.ltb_ge. lia.
  - left. apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)
Lemma grant_ok_over_budget : forall hint (m : Model) (a : word) (n : Z),
  vm_limit (m_vmmaps m) < vm_backing_used m + n ->
  grant_ok hint m a n = false.
Proof.
  intros hint m a n H. unfold grant_ok.
  rewrite (proj2 (Z.leb_gt _ _) H). rewrite !andb_false_r. reflexivity.
Qed.
