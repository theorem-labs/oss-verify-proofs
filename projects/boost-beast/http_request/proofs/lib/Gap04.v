(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import RelSpec MmapSim.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
Definition grant_ok_na (hint : word) (m : Model) (a : word) (n : Z) : bool :=
  place_ok (m_vmmaps m) a n.

Lemma grant_ok_grant_ok_na : forall hint m a n,
  grant_ok hint m a n = true -> grant_ok_na hint m a n = true.
Proof. intros hint m a n H. exact (grant_ok_place hint m a n H). Qed.

Lemma grant_ok_na_unpack : forall hint m a n,
  grant_ok_na hint m a n = true ->
  bv_unsigned a mod page_size = 0 /\ 0 < bv_unsigned a /\
  bv_unsigned a + n <= alloc_top (m_vmmaps m) /\
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n) = true.
Proof. intros hint m a n H. exact (place_ok_unpack _ _ _ H). Qed.

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
Lemma grant_exists_na_gen : forall hint (m : Model) (N n C : Z),
  0 < N -> N mod page_size = 0 -> 0 <= n <= N ->
  Forall (fun p => bv_unsigned (snd p) <= N) (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
  Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= C ->
  gap_floor + C * (2 * N) + N <= alloc_top (m_vmmaps m) ->
  exists a, grant_ok_na hint m a n = true /\ gap_floor <= bv_unsigned a.
Proof.
  intros hint m N n C HN HNal Hn Hsz Hcnt Hband.
  pose proof (alloc_top_lt (m_vmmaps m)) as Htop. unfold two_pow_64 in Htop.
  set (l := vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) in *.
  destruct (pick_candidate N n l (seq 0 (S (length l))) Hn Hsz (List.seq_NoDup _ _) ltac:(rewrite length_seq; lia))
    as (j & Hj & Hfree).
  apply in_seq in Hj.
  exists (Z_to_bv 64 (cand N j)).
  pose proof gap_floor_val as Hfv.
  assert (Hc : gap_floor <= cand N j <= gap_floor + C * (2 * N)) by (unfold cand; nia).
  unfold grant_ok_na, place_ok. rewrite !u64_lit_gap by lia. split; [|lia].
  assert (E1 : cand N j mod page_size = 0).
  { unfold cand. rewrite Hfv. unfold page_size in *. rewrite Z.add_mod, Z.mul_assoc, Z.mul_mod, HNal by lia.
    rewrite Z.mul_0_r. reflexivity. }
  rewrite (proj2 (Z.eqb_eq _ _) E1), (proj2 (Z.ltb_lt 0 _)) by lia.
  rewrite (proj2 (Z.leb_le _ _)) by lia.
  fold l. rewrite (region_free_of_noconflict l (cand N j) n) by (first [lia | exact Hfree]).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma grant_exists_gen : forall hint (m : Model) (N n C : Z),
  0 < N -> N mod page_size = 0 -> 0 <= n <= N ->
  Forall (fun p => bv_unsigned (snd p) <= N) (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
  Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= C ->
  gap_floor + C * (2 * N) + N <= alloc_top (m_vmmaps m) ->
  vm_backing_used m + n <= vm_limit (m_vmmaps m) ->
  exists a, grant_ok hint m a n = true /\ gap_floor <= bv_unsigned a.
Proof.
  intros hint m N n C HN HNal Hn Hsz Hcnt Hband Hlive.
  destruct (grant_exists_na_gen hint m N n C HN HNal Hn Hsz Hcnt Hband) as (a & Ha & Hfl).
  exists a. split; [|exact Hfl]. apply grant_ok_intro; [exact Ha | exact Hlive].
Qed.

(* [comment removed for export] *)
Lemma grant_exists : forall hint (m : Model) (n : Z),
  0 <= n <= 2 ^ 30 ->
  Forall (fun p => bv_unsigned (snd p) <= 2 ^ 30) (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
  Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= 40000 ->
  alloc_top_min <= alloc_top (m_vmmaps m) ->
  vm_backing_used m + n <= vm_limit (m_vmmaps m) ->
  exists a, grant_ok hint m a n = true /\ gap_floor <= bv_unsigned a.
Proof.
  intros hint m n Hn Hsz Hcnt Htop Hlive.
  apply (grant_exists_gen hint m (2 ^ 30) n 40000); try assumption; try lia.
  - reflexivity.
  - unfold alloc_top_min, gap_floor in *. lia.
Qed.

Lemma grant_exists_na : forall hint (m : Model) (n : Z),
  0 <= n <= 2 ^ 30 ->
  Forall (fun p => bv_unsigned (snd p) <= 2 ^ 30) (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
  Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= 40000 ->
  alloc_top_min <= alloc_top (m_vmmaps m) ->
  exists a, grant_ok_na hint m a n = true /\ gap_floor <= bv_unsigned a.
Proof.
  intros hint m n Hn Hsz Hcnt Htop.
  apply (grant_exists_na_gen hint m (2 ^ 30) n 40000); try assumption; try lia.
  - reflexivity.
  - unfold alloc_top_min, gap_floor in *. lia.
Qed.

(* [comment removed for export] *)
Lemma grant_exists_big : forall hint (m : Model) (n : Z),
  0 <= n <= 2 ^ 35 ->
  Forall (fun p => bv_unsigned (snd p) <= 2 ^ 35) (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
  Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= 1000 ->
  alloc_top_min <= alloc_top (m_vmmaps m) ->
  vm_backing_used m + n <= vm_limit (m_vmmaps m) ->
  exists a, grant_ok hint m a n = true /\ gap_floor <= bv_unsigned a.
Proof.
  intros hint m n Hn Hsz Hcnt Htop Hlive.
  apply (grant_exists_gen hint m (2 ^ 35) n 1000); try assumption; try lia.
  - reflexivity.
  - unfold alloc_top_min, gap_floor in *. lia.
Qed.

(* [comment removed for export] *)
Lemma grant_ok_over_budget : forall hint (m : Model) (a : word) (n : Z),
  vm_limit (m_vmmaps m) < vm_backing_used m + n ->
  grant_ok hint m a n = false.
Proof.
  intros hint m a n H. unfold grant_ok.
  rewrite (proj2 (Z.leb_gt _ _) H). rewrite !andb_false_r. reflexivity.
Qed.
