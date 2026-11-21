(** * BtStep — the combine loop, and (B-lower) closes.

    OWNER: huffman-id.  Last of the four heap-touching functions, after BtCover.v
    (bt_init), BtForce2.v (bt_force2) and PqDown.v (pqdownheap / bt_heapify).

    THE INVARIANT, and it is prettier than I expected.  The loop moves elements
    from the LIVE heap [heap[1 .. heap_len]] to the PARKED region
    [heap[heap_max .. HEAP_SIZE-1]], two per trip, while [heap_len] drops by one
    and [heap_max] by two.  For that to be sound the two windows must never
    collide, and the invariant that does it is

        2 * heap_len + 1 <= heap_max

    which a trip preserves EXACTLY: [2*(hlen-1) + 1 = 2*hlen - 1 <= hmax - 2] is
    literally [2*hlen + 1 <= hmax] again.  Not "preserved with slack" — the same
    inequality.

    AND IT IS TIGHT AT ENTRY IN A WAY THAT EXPLAINS A CONSTANT.  At the loop's
    start [heap_max = HEAP_SIZE], so the invariant is [2*heap_len + 1 <=
    HEAP_SIZE], and [heap_len <= L_CODES] because that is how many symbols there
    are.  zlib defines [HEAP_SIZE = 2*L_CODES + 1] ([Trees.v:81], 573 = 2*286+1).
    **So HEAP_SIZE is exactly the smallest value for which the live and parked
    windows can never overlap** — the "+1" in [2*L_CODES+1] is not slack, it is
    the whole margin, and one fewer would let the parked region collide with the
    live heap on the last trip. I did not set out to find that; it fell out of
    asking what the loop needs, which is the argument for deriving the side
    conditions rather than importing them.

    WHAT IS STILL NOT CLAIMED.  This file proves that nothing is LOST — every
    symbol in the heap at loop entry is in the live-or-parked union at exit. It
    does NOT prove that the parked region contains only symbols (the loop also
    parks internal nodes), nor anything about the heap ORDER or the resulting code
    lengths' optimality. For (B-lower)'s purpose — [gb_pass1] visits every
    nonzero-frequency symbol — coverage is what is needed, and the extra
    population of internal nodes is harmless because [gb_pass1] assigns them
    lengths too. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import BtCover PqDown BtForce2.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** [pqdownheap] does not touch anything outside the live window

    Needed because the trip's two parked writes must survive the second
    [pqdownheap], and because parked elements from earlier trips must survive
    both. *)
Lemma pq_down_outside : forall fuel t dep hp hlen v k j,
  1 <= k <= hlen -> (j < 1 \/ hlen < j) ->
  pq_down fuel t dep hp hlen v k j = hp j.
Proof.
  induction fuel as [|f IH]; intros t dep hp hlen v k j Hk Hj.
  - cbn [pq_down]. apply zset_other. lia.
  - cbn [pq_down].
    destruct (Z.leb (2 * k) hlen) eqn:Ej;
      [apply Z.leb_le in Ej | apply zset_other; lia].
    remember (if (Z.ltb (2 * k) hlen)
                 && smaller t dep (hp (2 * k + 1)) (hp (2 * k))
              then 2 * k + 1 else 2 * k) as j' eqn:Ejp.
    assert (Hj' : 1 <= j' <= hlen).
    { subst j'.
      destruct ((Z.ltb (2 * k) hlen)
                  && smaller t dep (hp (2 * k + 1)) (hp (2 * k))) eqn:Eb.
      - apply andb_prop in Eb as [Hlt _]. apply Z.ltb_lt in Hlt. lia.
      - lia. }
    destruct (smaller t dep v (hp j')) eqn:Es.
    + apply zset_other. lia.
    + rewrite (IH t dep (zset hp k (hp j')) hlen v j' j Hj' Hj).
      apply zset_other. lia.
Qed.

Lemma pqdownheap_outside : forall t dep hp hlen k j,
  1 <= k <= hlen -> (j < 1 \/ hlen < j) ->
  pqdownheap t dep hp hlen k j = hp j.
Proof.
  intros. unfold pqdownheap. apply pq_down_outside; assumption.
Qed.

(** ** One trip, stated on the SHAPE rather than on [bt_step]

    Taking the intermediate arrays as parameters with their defining equations
    keeps the proof readable and — more importantly — makes every index side
    condition explicit instead of buried in a [cbv zeta] normal form.  The
    subtraction shapes ([hmax1 = hmax - 1], [hmax2 = hmax1 - 1]) mirror
    [bt_step]'s own, so the application below unifies syntactically. *)
Lemma step_shape_covers :
  forall hp hlen hlen1 hmax hmax1 hmax2 n m node t dep t2 dep1
         A1 A2 A3 A4 A5 A6 s,
  2 <= hlen -> 2 * hlen + 1 <= hmax -> hmax <= HEAP_SIZE ->
  hlen1 = hlen - 1 -> hmax1 = hmax - 1 -> hmax2 = hmax1 - 1 ->
  n = hp 1 ->
  A1 = zset hp 1 (hp hlen) ->
  A2 = pqdownheap t dep A1 hlen1 1 ->
  m = A2 1 ->
  A3 = zset A2 hmax1 n ->
  A4 = zset A3 hmax2 m ->
  A5 = zset A4 1 node ->
  A6 = pqdownheap t2 dep1 A5 hlen1 1 ->
  (InHeap hp 1 hlen s \/ InHeap hp hmax (HEAP_SIZE - 1) s) ->
  (InHeap A6 1 hlen1 s \/ InHeap A6 hmax2 (HEAP_SIZE - 1) s).
Proof.
  intros hp hlen hlen1 hmax hmax1 hmax2 n m node t dep t2 dep1
         A1 A2 A3 A4 A5 A6 s
         Hlen Hgap Hhs Eh1 Em1 Em2 En EA1 EA2 Em EA3 EA4 EA5 EA6 Hcov.
  (* the windows are far apart; everything below is a consequence *)
  assert (Hsep : hlen1 < hmax2) by lia.
  assert (Hone : 1 <= hlen1) by lia.

  (* F1: the parked region is untouched by the whole trip *)
  assert (F1 : forall j, hmax <= j <= HEAP_SIZE - 1 -> A6 j = hp j).
  { intros j Hj.
    subst A6. rewrite pqdownheap_outside by lia.
    subst A5. rewrite zset_other by lia.
    subst A4. rewrite zset_other by lia.
    subst A3. rewrite zset_other by lia.
    subst A2. rewrite pqdownheap_outside by lia.
    subst A1. rewrite zset_other by lia. reflexivity. }

  (* F2: the first extracted element is parked at [hmax1] and stays there *)
  assert (F2 : A6 hmax1 = n).
  { subst A6. rewrite pqdownheap_outside by lia.
    subst A5. rewrite zset_other by lia.
    subst A4. rewrite zset_other by lia.
    subst A3. apply zset_same. }

  (* F3: the second extracted element is parked at [hmax2] and stays there *)
  assert (F3 : A6 hmax2 = m).
  { subst A6. rewrite pqdownheap_outside by lia.
    subst A5. rewrite zset_other by lia.
    subst A4. apply zset_same. }

  (* F4: anything live in [A2] is still covered at the end of the trip *)
  assert (F4 : InHeap A2 1 hlen1 s ->
               InHeap A6 1 hlen1 s \/ InHeap A6 hmax2 (HEAP_SIZE - 1) s).
  { intros [i [Hi Heq]].
    destruct (Z.eq_dec i 1) as [->|Hne].
    - (* it is the new root, i.e. [m]: parked at [hmax2] *)
      right. exists hmax2. split; [lia|]. rewrite F3. rewrite Em. exact Heq.
    - (* strictly below the root: survives both the parking writes and the
         second sift, the latter by [pqdownheap_preserves] *)
      left. subst A6. apply pqdownheap_preserves; [lia|].
      exists i. split; [lia|].
      subst A5. rewrite zset_other by lia.
      subst A4. rewrite zset_other by lia.
      subst A3. rewrite zset_other by lia. exact Heq. }

  destruct Hcov as [[j0 [Hj0 Heq]]|[j0 [Hj0 Heq]]].
  - (* it was live *)
    destruct (Z.eq_dec j0 1) as [->|Hne].
    + (* the root: extracted as [n] and parked at [hmax1] *)
      right. exists hmax1. split; [lia|]. rewrite F2. rewrite En. exact Heq.
    + (* not the root: lands in [A1]'s live window, then [A2]'s, then F4 *)
      apply F4. subst A2. apply pqdownheap_preserves; [lia|].
      destruct (Z.eq_dec j0 hlen) as [->|Hne2].
      * (* the last slot, which the trip moves to the root *)
        exists 1. split; [lia|]. subst A1. rewrite zset_same. exact Heq.
      * exists j0. split; [lia|]. subst A1. rewrite zset_other by lia. exact Heq.
  - (* it was already parked: F1 *)
    right. exists j0. split; [lia|]. rewrite F1 by lia. exact Heq.
Qed.

(** ** The invariant and the coverage predicate, on [BtSt] *)

Definition Gap (st : BtSt) : Prop := 2 * b_hlen st + 1 <= b_hmax st.

Definition Covered (st : BtSt) (s : Z) : Prop :=
  InHeap (b_heap st) 1 (b_hlen st) s
  \/ InHeap (b_heap st) (b_hmax st) (HEAP_SIZE - 1) s.

(** A trip preserves the gap EXACTLY — same inequality, not a weakened one. *)
Lemma bt_step_gap : forall st st',
  2 <= b_hlen st -> Gap st ->
  (bt_step st = BtCont st' \/ bt_step st = BtDone st') ->
  Gap st'.
Proof.
  intros st st' Hlen Hgap Hst. unfold Gap in *.
  unfold bt_step in Hst. cbv zeta in Hst.
  (* TWO separate traps here, both of which made [lia] say "Cannot find witness".
     (1) [inversion] leaves [R = st'] unsubstituted, so nothing reduces — hence
         the [subst].
     (2) BARE [cbn] then unfolds [Z.mul] itself, turning [2 * (hlen - 1)] into a
         raw [match] on the binary representation, which [lia] cannot read.  The
         delta list is the fix: reduce the RECORD PROJECTIONS and nothing else. *)
  destruct (Z.leb 2 (b_hlen st - 1));
    destruct Hst as [Hst|Hst]; try discriminate;
    inversion Hst; subst; cbn [b_hlen b_hmax]; lia.
Qed.

(** THE TRIP LEMMA. *)
Theorem bt_step_covers : forall st st' s,
  2 <= b_hlen st -> Gap st -> b_hmax st <= HEAP_SIZE ->
  (bt_step st = BtCont st' \/ bt_step st = BtDone st') ->
  Covered st s -> Covered st' s.
Proof.
  intros st st' s Hlen Hgap Hhs Hst Hcov.
  unfold Covered in *. unfold Gap in Hgap.
  unfold bt_step in Hst. cbv zeta in Hst.
  destruct (Z.leb 2 (b_hlen st - 1));
    destruct Hst as [Hst|Hst]; try discriminate;
    inversion Hst; subst; cbn [b_heap b_hlen b_hmax];
    eapply step_shape_covers with (hp := b_heap st) (hlen := b_hlen st)
      (hmax := b_hmax st) (t := b_tree st) (dep := b_dep st)
      (node := b_node st);
    try reflexivity; try exact Hlen; try exact Hgap; try exact Hhs;
    try exact Hcov.
Qed.

(** ** The loop

    [bt_loop] runs trips until [heap_len < 2].  Both the gap and the coverage are
    carried; the [heap_max <= HEAP_SIZE] side condition is carried too, since
    [heap_max] only decreases. *)
Lemma bt_loop_covers : forall fuel st s,
  2 <= b_hlen st -> Gap st -> b_hmax st <= HEAP_SIZE ->
  Covered st s ->
  match bt_loop fuel st with
  | Some stf => Covered stf s
  | None => True
  end.
Proof.
  induction fuel as [|f IH]; intros st s Hlen Hgap Hhs Hcov.
  - cbn [bt_loop]. exact I.
  - cbn [bt_loop].
    destruct (bt_step st) as [st'|st'] eqn:Est.
    + (* another trip *)
      assert (Hor : bt_step st = BtCont st' \/ bt_step st = BtDone st')
        by (left; exact Est).
      pose proof (bt_step_covers st st' s Hlen Hgap Hhs Hor Hcov) as Hc'.
      pose proof (bt_step_gap st st' Hlen Hgap Hor) as Hg'.
      (* the loop continued, so [heap_len >= 2] at the new state *)
      assert (Hlen' : 2 <= b_hlen st').
      { unfold bt_step in Est. cbv zeta in Est.
        destruct (Z.leb 2 (b_hlen st - 1)) eqn:E2; [|discriminate].
        apply Z.leb_le in E2. inversion Est. subst. cbn [b_hlen]. lia. }
      assert (Hhs' : b_hmax st' <= HEAP_SIZE).
      { unfold bt_step in Est. cbv zeta in Est.
        destruct (Z.leb 2 (b_hlen st - 1)); [|discriminate].
        inversion Est. subst. cbn [b_hmax]. lia. }
      apply IH; assumption.
    + (* last trip *)
      assert (Hor : bt_step st = BtCont st' \/ bt_step st = BtDone st')
        by (right; exact Est).
      exact (bt_step_covers st st' s Hlen Hgap Hhs Hor Hcov).
Qed.

(** ** (B-lower)'s heap half, end to end

    Entry state: [heap_max = HEAP_SIZE], so [Gap] is [2*heap_len + 1 <=
    HEAP_SIZE] — and since [HEAP_SIZE = 2*L_CODES + 1], that is exactly
    [heap_len <= L_CODES]. *)
Lemma gap_at_entry : forall hlen hp dep t node,
  hlen <= L_CODES ->
  Gap {| b_tree := t; b_heap := hp; b_dep := dep;
         b_hlen := hlen; b_hmax := HEAP_SIZE; b_node := node |}.
Proof.
  intros. unfold Gap. cbn [b_hlen b_hmax].
  unfold HEAP_SIZE, L_CODES in *. lia.
Qed.

(** And the constant is TIGHT: at [heap_len = L_CODES] the entry gap holds with
    equality, so [HEAP_SIZE - 1] would break it. *)
Example heap_size_is_exactly_tight :
  2 * L_CODES + 1 = HEAP_SIZE /\ ~ (2 * L_CODES + 1 <= HEAP_SIZE - 1).
Proof. unfold HEAP_SIZE, L_CODES. split; [reflexivity | lia]. Qed.

Theorem combine_loop_covers : forall fuel hlen hp dep t node s,
  2 <= hlen -> hlen <= L_CODES ->
  (InHeap hp 1 hlen s \/ InHeap hp HEAP_SIZE (HEAP_SIZE - 1) s) ->
  match bt_loop fuel {| b_tree := t; b_heap := hp; b_dep := dep;
                        b_hlen := hlen; b_hmax := HEAP_SIZE;
                        b_node := node |} with
  | Some stf => Covered stf s
  | None => True
  end.
Proof.
  intros fuel hlen hp dep t node s H2 Hl Hin.
  apply bt_loop_covers.
  - cbn [b_hlen]. exact H2.
  - apply gap_at_entry. exact Hl.
  - cbn [b_hmax]. lia.
  - unfold Covered. cbn [b_heap b_hlen b_hmax]. exact Hin.
Qed.

Print Assumptions pqdownheap_outside.
Print Assumptions step_shape_covers.
Print Assumptions bt_step_covers.
Print Assumptions bt_loop_covers.
Print Assumptions combine_loop_covers.
Print Assumptions heap_size_is_exactly_tight.
