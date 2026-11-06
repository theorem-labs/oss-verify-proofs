(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Adapted by Theorem Labs, 2026-10-28 (h-hreply-k2), for plugin-hostd/fuzz_reply. Donor text, all at
   origin/ossv/recipes 754c3cdb4cc (Apache-2.0 OR MIT; the three lines above are the donors' header):
   proofs/cgif/cgif_file_fuzzer/lib/YG01.v:140-142 (universe_ok: name, signature and its last two clauses) and :337
   (wf_depot: name and the NoDup /\ incl form); YFem.v:33-36 (depot_len_bound: name and the NoDup_incl_length step);
   YG00.v:36 (kUnwindMax); proofs/boost-beast/http_request/lib/As/AsIface.v:295-296 (trace_ok's body, as sites_ok),
   AS_InstDefs.v:63-64 (depot_tr's id clause) and AsDepotInv.v:44-45 (the names d_ids, d_hash). PATHMAP row:
   the cgif YG01.v donor. The rest of the file is new. *)
(* fuzz_reply, both ASan builds: the depot gives at most one id per distinct trace, so the ids of a run are at most
   the ids the depot holds at main plus the length of the trace list. Shared by lib/A (asan) and lib/B (asan-ubsan);
   it holds no address of either image and no trace list. Each build instantiates it with its own list
   (lib/A/Prog/AsDepotIds_a.v, lib/B/Prog/AsDepotIds_b.v).

   Shape: the released cgif route (origin/ossv/recipes 754c3cdb4cc, proofs/cgif/cgif_file_fuzzer/lib/):
   universe_ok (YG01.v:140-142), wf_depot = NoDup depot /\ incl depot U (YG01.v:337), depot_len_bound
   (YFem.v:33-36). Two changes, each because of the image:
   - The depot here is keyed by the 64-bit hash, not by the trace. Put (llvmorg-20.1.8 sanitizer_stackdepotbase.h:
     115-148) hashes the trace (:121), looks for an equal hash in its bucket (:122-138) and takes a new id
     `++n_uniq_ids` only on a miss (:139); sanitizer_stackdepot.cpp:33-35 `eq` compares the hash only. In the
     images: asan Put 0x7432c, the chain compare 0x74484 (`bne` of the node's u64 at +0, 0x7447c, with the hash; no
     other field), the new id 0x744e8 (`amoadd.w` on n_uniq_ids); asan-ubsan Put 0x74384, compare 0x744dc, new id
     0x74540. A trace of size 0 returns id 0 and stores nothing (asan 0x7437c, asan-ubsan 0x743d4). Keying by hash
     covers collisions: two traces with one hash give one id, never two.
   - The depot at main, K0, is kept apart from the ids the run adds, E. The released route's two conventions are
     then lemmas, not prose (ids_two_sides below):
       depot side: d_ids counts every id; id 1 is the start-up trace of __asan_register_globals, which the depot
         holds at main (boost-beast AsMainIfaceDepot.v:30-31, depot0 with d_ids = 1), and depot_tr constrains only
         ids 2 .. d_ids (AS_InstDefs.v:63-64);
       list side: TRLIST does not hold the start-up trace (trace_list_a.v / trace_list_b.v), and its length N is
         the number of traces the run's allocator calls can record (prefix closure included).
     The main bound, depot_new_ids_bound (ids added by the run <= N), does not depend on K0. Only
     ids_two_sides_startup1 (d_ids <= 1 + N) uses length K0 = 1, which the at-main certificate states. *)
From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
Local Open Scope Z_scope.

(* The body of the released trace_ok (boost-beast AsIface.v:295-296) over a site table, as trace_list_a.v /
   trace_list_b.v state TRSITES_ok: for each (call pc, pc0, return addresses), pc0 is not a return address and
   every non-empty prefix of pc0 :: return addresses is in TRL. *)
Definition sites_ok (TRL : list (list Z)) (SITES : list (Z * Z * list Z)) : Prop :=
  Forall (fun s : Z * Z * list Z =>
            ~ In (snd (fst s)) (snd s) /\ forall j, (1 <= j)%nat -> In (firstn j (snd (fst s) :: snd s)) TRL) SITES.

(* The trace a site records under trace-depth limit mcs: the first mcs words of pc0 :: return addresses.
   AsTRWalkStop.get_stack_trace_stop gives this form at a site whose walk stops after the wrapper's frame record. *)
Definition site_trace (mcs : nat) (s : Z * Z * list Z) : list Z := firstn mcs (snd (fst s) :: snd s).

Lemma site_trace_in : forall TRL SITES s mcs,
    sites_ok TRL SITES -> In s SITES -> site_trace mcs s = [] \/ In (site_trace mcs s) TRL.
Proof.
  intros TRL SITES s mcs OK IN. unfold site_trace. destruct mcs as [|m]; [left; reflexivity|]. right.
  apply (proj2 (proj1 (Forall_forall _ _) OK s IN)). lia.
Qed.

(* A run's Put calls, in order, record traces that are empty or made at a site of the table. *)
Definition recorded_at (SITES : list (Z * Z * list Z)) (mcs : nat) (ts : list (list Z)) : Prop :=
  Forall (fun t => t = [] \/ exists s, In s SITES /\ t = site_trace mcs s) ts.

(* cgif's universe_ok (YG01.v:140-142) with the released trace-list cap TRLEN <= 256 (boost-beast
   AS_InstHeap.v:360, AS_InstTR.v:14) in place of DEPOT_MAX, and kUnwindMax = 30 (asan_stack.h:24). *)
Definition TRLEN_MAX : nat := 256.
Definition kUnwindMax : nat := 30.
Definition universe_ok (U : list (list Z)) : Prop :=
  (length U <= TRLEN_MAX)%nat /\ Forall (fun t => (length t <= kUnwindMax)%nat) U /\ NoDup U.

Section Depot.
  Variable dhash : list Z -> Z.   (* sanitizer_stackdepot.cpp:37-42: MurMur2 over size, frames and tag *)

  (* Put: the depot's keys in id order (id k holds the k-th key); d_ids is their number. *)
  Definition dput (K : list Z) (t : list Z) : list Z :=
    match t with
    | [] => K
    | _ :: _ => if existsb (Z.eqb (dhash t)) K then K else K ++ [dhash t]
    end.
  Definition dputs (K : list Z) (ts : list (list Z)) : list Z := fold_left dput ts K.

  Definition d_ids (K : list Z) : Z := Z.of_nat (length K).
  Definition d_hash (K : list Z) (id : Z) : Z := nth (Z.to_nat (id - 1)) K 0.

  (* cgif's wf_depot (YG01.v:337), keyed by hash and split at main: the keys are those at main, K0, then keys E of
     traces in U, with no key twice. *)
  Definition wf_depot (K0 : list Z) (U : list (list Z)) (K : list Z) : Prop :=
    NoDup K /\ exists E, K = K0 ++ E /\ incl E (map dhash U).

  Lemma wf_depot_init : forall K0 U, NoDup K0 -> wf_depot K0 U K0.
  Proof. intros K0 U H. split; [exact H|]. exists []. split; [symmetry; apply app_nil_r | intros x []]. Qed.

  Lemma dput_wf : forall K0 U K t, wf_depot K0 U K -> t = [] \/ In t U -> wf_depot K0 U (dput K t).
  Proof.
    intros K0 U K t (ND & E & -> & INC) HT. unfold dput. destruct t as [|x r] eqn:Et.
    { split; [exact ND|]. exists E. auto. }
    destruct HT as [HT|HT]; [discriminate|].
    destruct (existsb (Z.eqb (dhash (x :: r))) (K0 ++ E)) eqn:EX.
    { split; [exact ND|]. exists E. auto. }
    assert (NIN : ~ In (dhash (x :: r)) (K0 ++ E)).
    { intros IN. assert (existsb (Z.eqb (dhash (x :: r))) (K0 ++ E) = true) as C.
      { apply existsb_exists. exists (dhash (x :: r)). split; [exact IN | apply Z.eqb_refl]. }
      rewrite C in EX. discriminate. }
    split.
    - apply NoDup_app; [exact ND | constructor; [intros [] | constructor] |].
      intros y Hy Hy'. destruct Hy' as [<-|[]]. exact (NIN Hy).
    - exists (E ++ [dhash (x :: r)]). split; [rewrite app_assoc; reflexivity|].
      intros y Hy. apply in_app_or in Hy as [Hy|[<-|[]]]; [exact (INC y Hy)|].
      apply in_map. exact HT.
  Qed.

  Lemma dputs_wf : forall K0 U ts K,
      wf_depot K0 U K -> Forall (fun t => t = [] \/ In t U) ts -> wf_depot K0 U (dputs K ts).
  Proof.
    intros K0 U ts. induction ts as [|t ts IH]; intros K W F; [exact W|].
    inversion F as [|? ? Ht Fs]; subst. change (dputs K (t :: ts)) with (dputs (dput K t) ts).
    apply IH; [apply dput_wf; assumption | exact Fs].
  Qed.

  (* The list-side count: the ids a run adds to the depot are at most the length of the trace list. *)
  Lemma depot_new_ids_bound : forall K0 U K, wf_depot K0 U K -> (length K - length K0 <= length U)%nat.
  Proof.
    intros K0 U K (ND & E & -> & INC). rewrite length_app.
    assert (NDE : NoDup E) by (apply NoDup_app_remove_l in ND; exact ND).
    pose proof (NoDup_incl_length NDE INC) as L. rewrite length_map in L. lia.
  Qed.

  (* cgif's depot_len_bound (YFem.v:33-36), split at main. *)
  Lemma depot_len_bound : forall K0 U K, wf_depot K0 U K -> (length K <= length K0 + length U)%nat.
  Proof.
    intros K0 U K W. pose proof (depot_new_ids_bound K0 U K W) as B.
    destruct W as (_ & E & -> & _). rewrite length_app in *. lia.
  Qed.

  Lemma depot_len_bound_universe : forall K0 U K,
      universe_ok U -> wf_depot K0 U K -> (length K <= length K0 + TRLEN_MAX)%nat.
  Proof. intros K0 U K (HU & _) W. pose proof (depot_len_bound K0 U K W). lia. Qed.

  (* The released depot_tr's id clause (AS_InstDefs.v:63-64), with its lower id 2 replaced by length K0 + 1: every
     id the run added holds the hash of a trace of U. *)
  Lemma depot_tr_ids : forall K0 U K, wf_depot K0 U K ->
      forall id, Z.of_nat (length K0) + 1 <= id <= d_ids K -> In (d_hash K id) (map dhash U).
  Proof.
    intros K0 U K (ND & E & -> & INC) id Hid. unfold d_ids, d_hash in *. rewrite length_app in Hid.
    rewrite app_nth2 by lia. apply INC. apply nth_In. lia.
  Qed.

  (* The two conventions side by side. d_ids, the depot-side count, is the ids held at main plus the ids the run
     added; the second, the list-side count, is at most the length of the trace list. *)
  Lemma ids_two_sides : forall K0 U K, wf_depot K0 U K ->
      d_ids K = Z.of_nat (length K0) + Z.of_nat (length K - length K0)
      /\ Z.of_nat (length K - length K0) <= Z.of_nat (length U).
  Proof.
    intros K0 U K W. pose proof (depot_new_ids_bound K0 U K W) as B. unfold d_ids.
    destruct W as (_ & E & -> & _). rewrite length_app in *. split; lia.
  Qed.

  (* With the at-main depot of the released route (one id, the start-up trace: depot0, AsMainIfaceDepot.v:30-31)
     the two sides meet as the released route states them: d_ids <= 1 + N, and depot_tr's clause for ids >= 2. The
     premise length K0 = 1 is the at-main certificate's; this lemma is closed only where that certificate exists
     for the image in question. *)
  Lemma ids_two_sides_startup1 : forall K0 U K, length K0 = 1%nat -> wf_depot K0 U K ->
      d_ids K <= 1 + Z.of_nat (length U)
      /\ (forall id, 2 <= id <= d_ids K -> In (d_hash K id) (map dhash U)).
  Proof.
    intros K0 U K L0 W. pose proof (ids_two_sides K0 U K W) as [E B]. rewrite L0 in E. split; [lia|].
    intros id Hid. apply (depot_tr_ids K0 U K W). rewrite L0. lia.
  Qed.

  (* The run-level bound: from any duplicate-free depot at main, a run whose Put calls record traces made at the
     sites of a table that satisfies sites_ok TRL keeps wf_depot K0 TRL, adds at most length TRL ids, and so has at
     most length K0 + length TRL ids. The trace-depth limit mcs is a parameter: a table built for the walking branch
     (pc0 = the wrapper's second GetCurrentPc) instantiates it with mcs > 2, a table built for the short branch with
     mcs <= 2, and the statement is the same. *)
  Theorem depot_ids_bound : forall TRL SITES K0 mcs ts,
      sites_ok TRL SITES -> NoDup K0 -> recorded_at SITES mcs ts ->
      wf_depot K0 TRL (dputs K0 ts)
      /\ (length (dputs K0 ts) - length K0 <= length TRL)%nat
      /\ d_ids (dputs K0 ts) <= Z.of_nat (length K0) + Z.of_nat (length TRL).
  Proof.
    intros TRL SITES K0 mcs ts OK ND REC.
    assert (W : wf_depot K0 TRL (dputs K0 ts)).
    { apply dputs_wf; [apply wf_depot_init; exact ND|].
      eapply Forall_impl; [|exact REC]. intros t [->|(s & IN & ->)]; [left; reflexivity|].
      exact (site_trace_in TRL SITES s mcs OK IN). }
    split; [exact W|]. split; [exact (depot_new_ids_bound _ _ _ W)|].
    pose proof (depot_len_bound _ _ _ W). unfold d_ids. lia.
  Qed.
End Depot.
