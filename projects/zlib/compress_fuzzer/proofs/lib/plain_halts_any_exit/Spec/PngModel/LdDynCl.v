(** * LdDynCl — item (v-2b): the decoder's reconstructed code-length vector IS
      the emitter's code-length tree.

    OWNER: ld-seams.  Pin and shadowing check in LdDynSeam.v.

    The emitter sends [blcodes] three-bit lengths in [bl_order] order and STOPS
    ([Trees.v:824]); the decoder reads that many and scatters them back through
    [cl_order], filling every untransmitted symbol with 0 ([DeflateSpec.v:646],
    RFC 1951's rule). For the round trip the two have to agree at all NINETEEN
    positions, which splits into two facts of very different character:

      TRANSMITTED  (rank < blcodes): the permutations must invert each other.
      UNTRANSMITTED (rank >= blcodes): the decoder writes 0, so the emitter's
                    tree must actually HAVE 0 there -- which is a property of
                    [bbl_scan], the downward scan that chose [blcodes].

    The second is the interesting one and it is where a real encoder could be
    wrong: [scatter_cl] does not fail on a symbol it was never told about, it
    silently returns 0. So if [bbl_scan] ever stopped ABOVE a nonzero length,
    the header would decode to a DIFFERENT tree with no error anywhere. That is
    a silent-wrong-answer path, not a stuck one, and the lemma below is what
    closes it: everything strictly above the returned index is zero, established
    by the scan's own guard on the way down. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees DeflateSpec ZBitsOut ZBitsBridge BwStream.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  HuffGenCodes ClStream SendItems SendGo SendGoLens SendGoWf SendTreeRT.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import LdDynSeam LdDynHdr.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** 1. [cl_order] is a permutation of 0..18, as a computation

    Nineteen positions, one [vm_compute]. Stated as a list equality rather than
    nineteen lemmas so that editing either table breaks this in milliseconds. *)

Lemma cl_order_positions :
  map (fun k => pos_of k cl_order) (seq 0 19)
  = [Some 3; Some 17; Some 15; Some 13; Some 11; Some 9; Some 7; Some 5;
     Some 4; Some 6; Some 8; Some 10; Some 12; Some 14; Some 16; Some 18;
     Some 0; Some 1; Some 2]%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma pos_of_cl_order_total : forall k, (k < 19)%nat ->
  exists i, pos_of k cl_order = Some i.
Proof.
  intros k Hk.
  destruct k as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|k]]]]]]]]]]]]]]]]]]];
    try (vm_compute; eexists; reflexivity).
  lia.
Qed.

(** ** 2. Reading [scatter_cl] and [sat_vals] at a position *)

Lemma scatter_cl_at : forall vals s, (s < 19)%nat ->
  nth s (scatter_cl vals) 0%nat
  = match pos_of s cl_order with
    | None => 0%nat
    | Some i => nth i vals 0%nat
    end.
Proof.
  intros vals s Hs.
  (* [f] is bound to a NAME so that [map_nth]'s pattern [nth _ (map ?f _) (?f ?d)]
     unifies first-order.  Written beta-reduced, the default is not an
     application and the rewrite finds no subterm. *)
  set (f := fun j => match pos_of j cl_order with
                     | None => 0%nat
                     | Some i => nth i vals 0%nat
                     end).
  change (scatter_cl vals) with (map f (seq 0 19)).
  rewrite (nth_indep (map f (seq 0 19)) 0%nat (f 0%nat))
    by (rewrite length_map, length_seq; lia).
  rewrite map_nth. rewrite seq_nth by lia. cbn [Nat.add]. subst f. reflexivity.
Qed.

Lemma sat_vals_at : forall fuel rank blcodes bl i,
  (Z.of_nat i < blcodes - rank) ->
  nth i (sat_vals fuel rank blcodes bl) 0%nat
  = (if Z.of_nat i <? Z.of_nat fuel
     then Z.to_nat (t_len bl (bl_order (rank + Z.of_nat i)))
     else 0%nat).
Proof.
  induction fuel as [|f IH]; intros rank blcodes bl i Hi.
  - cbn [sat_vals]. destruct i; cbn [nth]; reflexivity.
  - cbn [sat_vals].
    destruct (Z.leb blcodes rank) eqn:Eg.
    + apply Z.leb_le in Eg. lia.
    + apply Z.leb_gt in Eg.
      destruct i as [|i'].
      * cbn [nth]. replace (rank + Z.of_nat 0) with rank by lia.
        replace (Z.of_nat 0 <? Z.of_nat (S f)) with true
          by (symmetry; apply Z.ltb_lt; lia).
        reflexivity.
      * cbn [nth].
        rewrite (IH (rank + 1) blcodes bl i') by lia.
        replace (rank + 1 + Z.of_nat i') with (rank + Z.of_nat (S i')) by lia.
        destruct (Z.of_nat i' <? Z.of_nat f) eqn:E1;
          [ replace (Z.of_nat (S i') <? Z.of_nat (S f)) with true
              by (symmetry; apply Z.ltb_lt; apply Z.ltb_lt in E1; lia)
          | replace (Z.of_nat (S i') <? Z.of_nat (S f)) with false
              by (symmetry; apply Z.ltb_ge; apply Z.ltb_ge in E1; lia) ];
          reflexivity.
Qed.

(** Out of range, [sat_vals] is short and [nth] returns the default 0, which is
    exactly what [scatter_cl] would have written anyway. *)
Lemma sat_vals_beyond : forall fuel rank blcodes bl i,
  0 <= blcodes - rank <= Z.of_nat fuel ->
  (blcodes - rank <= Z.of_nat i) ->
  nth i (sat_vals fuel rank blcodes bl) 0%nat = 0%nat.
Proof.
  intros fuel rank blcodes bl i Hf Hi.
  apply nth_overflow.
  pose proof (sat_vals_length fuel rank blcodes bl Hf) as HL. lia.
Qed.

(** ** 3. THE ZERO TAIL: [bbl_scan] leaves nothing nonzero above it

    This is the fact that makes the untransmitted positions safe. Proved from
    the scan's own guard: it only steps from [i] to [i-1] after checking that
    [t_len bl (bl_order i)] is zero. *)

Lemma bbl_scan_zeros_above : forall fuel bl i j,
  bbl_scan fuel bl i < j <= i ->
  t_len bl (bl_order j) = 0.
Proof.
  induction fuel as [|f IH]; intros bl i j Hj.
  - cbn [bbl_scan] in Hj. lia.
  - cbn [bbl_scan] in Hj.
    destruct (Z.ltb i 3) eqn:E3; [lia|].
    destruct (negb (Z.eqb (t_len bl (bl_order i)) 0)) eqn:Ez; [lia|].
    apply negb_false_iff in Ez. apply Z.eqb_eq in Ez.
    destruct (Z.eq_dec j i) as [Hji|Hji].
    + subst j. exact Ez.
    + apply (IH bl (i - 1) j). lia.
Qed.

(** The form the header consumer wants: with [blcodes = mbi + 1] as
    [build_bl_tree] computes it ([Trees.v:803]), every rank at or above
    [blcodes] carries length zero. *)
Corollary bbl_scan_zero_tail : forall fuel bl i j,
  bbl_scan fuel bl i + 1 <= j <= i ->
  t_len bl (bl_order j) = 0.
Proof.
  intros fuel bl i j Hj. apply (bbl_scan_zeros_above fuel bl i j). lia.
Qed.

(** ** 4. THE AGREEMENT

    The nineteen-entry vector the decoder reconstructs from the header is the
    length vector of the emitter's own code-length tree. Both halves are here:
    the permutation inverts on the transmitted prefix, and the zero tail covers
    the rest. *)

Theorem scattered_sat_vals_is_the_tree :
  forall fuel bl blcodes,
  0 <= blcodes <= 19 ->
  blcodes <= Z.of_nat fuel ->
  (forall j, 0 <= j <= 18 -> 0 <= t_len bl (bl_order j)) ->
  (forall j, blcodes <= j <= 18 -> t_len bl (bl_order j) = 0) ->
  LensOf bl (scatter_cl (sat_vals fuel 0 blcodes bl)).
Proof.
  intros fuel bl blcodes Hbc Hfuel Hnn Htail k Hk.
  rewrite scatter_cl_length in Hk.
  rewrite scatter_cl_at by lia.
  destruct (pos_of k cl_order) as [i|] eqn:Ep.
  - (* [i] is the rank at which symbol [k]'s length was (or was not) sent *)
    pose proof (pos_of_correct cl_order k i Ep) as Hne.
    assert (Hlt : (i < length cl_order)%nat).
    { apply nth_error_Some. rewrite Hne. discriminate. }
    assert (Hi19 : (i < 19)%nat) by (rewrite cl_order_length in Hlt; lia).
    assert (Hnthi : nth i cl_order 0%nat = k).
    { rewrite (nth_error_nth' cl_order 0%nat Hlt) in Hne.
      injection Hne as Hne'. exact Hne'. }
    assert (Hblo : bl_order (Z.of_nat i) = Z.of_nat k).
    { rewrite bl_order_at. rewrite Nat2Z.id, Hnthi. reflexivity. }
    destruct (Z_lt_le_dec (Z.of_nat i) blcodes) as [Hsent|Hge].
    + (* TRANSMITTED *)
      rewrite (sat_vals_at fuel 0 blcodes bl i) by lia.
      replace (Z.of_nat i <? Z.of_nat fuel) with true
        by (symmetry; apply Z.ltb_lt; lia).
      replace (0 + Z.of_nat i) with (Z.of_nat i) by lia.
      rewrite Hblo.
      assert (0 <= t_len bl (Z.of_nat k)).
      { rewrite <- Hblo. apply Hnn. lia. }
      lia.
    + (* UNTRANSMITTED: the decoder writes 0 and the tree agrees *)
      rewrite (sat_vals_beyond fuel 0 blcodes bl i) by lia.
      assert (Hz : t_len bl (bl_order (Z.of_nat i)) = 0) by (apply Htail; lia).
      rewrite Hblo in Hz. rewrite Hz. reflexivity.
  - exfalso.
    destruct (pos_of_cl_order_total k Hk) as [i Hi].
    rewrite Ep in Hi. discriminate Hi.
Qed.

Print Assumptions scatter_cl_at.
Print Assumptions sat_vals_at.
Print Assumptions bbl_scan_zeros_above.
Print Assumptions scattered_sat_vals_is_the_tree.
