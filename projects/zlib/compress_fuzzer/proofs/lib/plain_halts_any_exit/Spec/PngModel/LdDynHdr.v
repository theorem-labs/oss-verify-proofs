(** * LdDynHdr — item (v-1) and (v-2a): the dynamic header's fields and the
      code-length vector.

    OWNER: ld-seams.  See LdDynSeam.v for the pin on huffman-id's staged tree
    and the shadowing check.

    [send_all_trees] ([Trees.v:827-833]) emits, in order:

      bw_send_bits (lcodes - 257) 5      HLIT
      bw_send_bits (dcodes - 1)   5      HDIST
      bw_send_bits (blcodes - 4)  4      HCLEN
      sat_ranks    ...                   blcodes three-bit code lengths, bl_order
      send_tree    (literal tree)        \  huffman-id's round trip, joined to a
      send_tree    (distance tree)       /  mid-stream writer in LdDynSeam.v

    and [decode_dynamic_tables] ([DeflateSpec.v:891]) reads

      read_bits 5 / read_bits 5 / read_bits 4
      read_cl_lengths (hclen + 4)        = read_3bit_vals then scatter_cl
      read_lengths cl (nlit + ndist)     one call spanning BOTH trees (LdDynSplit.v)

    This file does the first four lines. Two things are deliberately NOT folded
    together: the emitter's bit list and the decoder's value list get separate
    mirrors ([sat_bits] / [sat_vals]), following huffman-id's [send_items]
    device, because the round trip is then two independent inductions rather
    than one simultaneous one.

    FUEL DISCIPLINE.  [sat_ranks] takes LITERAL fuel ([Z.to_nat BL_CODES + 1]),
    which puts it in the cell where a folded definition meeting its own
    unfolding is fatal.  So every lemma here is stated over SYMBOLIC fuel and
    the literal is reached through a fuel-independence lemma, never by unfolding
    twenty times.  That was the one hazard I flagged correctly in §LD-VSCOPE. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees DeflateSpec ZBitsOut ZBitsBridge BwStream.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  HuffGenCodes ClStream SendItems SendGo SendGoLens SendGoWf SendTreeRT.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import LdDynSeam.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Lemma z2n3 : Z.to_nat 3 = 3%nat. Proof. reflexivity. Qed.
Lemma z2n4 : Z.to_nat 4 = 4%nat. Proof. reflexivity. Qed.
Lemma z2n5 : Z.to_nat 5 = 5%nat. Proof. reflexivity. Qed.

(** ** 1. The three header fields *)

Definition hdr_bits (lcodes dcodes blcodes : Z) : list bool :=
  write_bits 5%nat (lcodes - 257)
    ++ write_bits 5%nat (dcodes - 1)
    ++ write_bits 4%nat (blcodes - 4).

Definition hdr_send (lcodes dcodes blcodes : Z) (b : BW) : BW :=
  bw_send_bits (blcodes - 4) 4
    (bw_send_bits (dcodes - 1) 5
      (bw_send_bits (lcodes - 257) 5 b)).

Lemma header_stream : forall lcodes dcodes blcodes b,
  bw_wf b ->
  0 <= lcodes - 257 < 32 -> 0 <= dcodes - 1 < 32 -> 0 <= blcodes - 4 < 16 ->
  bw_stream (hdr_send lcodes dcodes blcodes b)
    = bw_stream b ++ hdr_bits lcodes dcodes blcodes
  /\ bw_wf (hdr_send lcodes dcodes blcodes b).
Proof.
  intros lcodes dcodes blcodes b Hwf Hl Hd Hc.
  assert (H32 : (2:Z) ^ 5 = 32) by reflexivity.
  assert (H16 : (2:Z) ^ 4 = 16) by reflexivity.
  assert (Hw1 : bw_wf (bw_send_bits (lcodes - 257) 5 b))
    by (apply bw_send_bits_inv; [exact Hwf | lia | rewrite H32; lia]).
  assert (Hw2 : bw_wf (bw_send_bits (dcodes - 1) 5
                        (bw_send_bits (lcodes - 257) 5 b)))
    by (apply bw_send_bits_inv; [exact Hw1 | lia | rewrite H32; lia]).
  unfold hdr_send, hdr_bits. split.
  (* [<- !app_assoc] terminates: right-association is a normal form, so the
     rule's RHS pattern cannot reappear indefinitely. *)
  - rewrite (bw_send_bits_bits (blcodes - 4) 4 _ Hw2)
      by (try rewrite H16; try rewrite H32; lia).
    rewrite (bw_send_bits_bits (dcodes - 1) 5 _ Hw1)
      by (try rewrite H16; try rewrite H32; lia).
    rewrite (bw_send_bits_bits (lcodes - 257) 5 b Hwf)
      by (try rewrite H16; try rewrite H32; lia).
    rewrite z2n4, z2n5, <- !app_assoc. reflexivity.
  - apply bw_send_bits_inv; [exact Hw2 | lia | rewrite H16; lia].
Qed.

Lemma header_decode : forall lcodes dcodes blcodes rest,
  0 <= lcodes - 257 < 32 -> 0 <= dcodes - 1 < 32 -> 0 <= blcodes - 4 < 16 ->
  read_bits 5%nat (hdr_bits lcodes dcodes blcodes ++ rest)
    = Some (lcodes - 257,
            write_bits 5%nat (dcodes - 1) ++ write_bits 4%nat (blcodes - 4) ++ rest)
  /\ read_bits 5%nat (write_bits 5%nat (dcodes - 1)
                        ++ write_bits 4%nat (blcodes - 4) ++ rest)
    = Some (dcodes - 1, write_bits 4%nat (blcodes - 4) ++ rest)
  /\ read_bits 4%nat (write_bits 4%nat (blcodes - 4) ++ rest)
    = Some (blcodes - 4, rest).
Proof.
  intros lcodes dcodes blcodes rest Hl Hd Hc.
  unfold hdr_bits.
  split; [|split].
  - rewrite <- !app_assoc.
    apply read_bits_write_bits. cbn [Z.of_nat]. change (2 ^ Z.of_nat 5%nat) with 32.
    lia.
  - apply read_bits_write_bits. change (2 ^ Z.of_nat 5%nat) with 32. lia.
  - apply read_bits_write_bits. change (2 ^ Z.of_nat 4%nat) with 16. lia.
Qed.

(** The RFC's field offsets, which are exactly where an off-by-one would hide:
    the decoder adds back what the emitter subtracted. *)
Corollary header_recovers_the_counts : forall lcodes dcodes blcodes,
  257 <= lcodes -> 1 <= dcodes -> 4 <= blcodes ->
  (Z.to_nat (lcodes - 257) + 257)%nat = Z.to_nat lcodes
  /\ (Z.to_nat (dcodes - 1) + 1)%nat = Z.to_nat dcodes
  /\ (Z.to_nat (blcodes - 4) + 4)%nat = Z.to_nat blcodes.
Proof. intros lcodes dcodes blcodes Hl Hd Hc. repeat split; lia. Qed.

(** ** 2. [sat_ranks]: the code-length vector, emitter and decoder mirrors *)

Fixpoint sat_bits (fuel : nat) (rank blcodes : Z) (bl : Tree) : list bool :=
  match fuel with
  | O => []
  | S f =>
      if Z.leb blcodes rank then []
      else write_bits 3%nat (t_len bl (bl_order rank))
             ++ sat_bits f (rank + 1) blcodes bl
  end.

Fixpoint sat_vals (fuel : nat) (rank blcodes : Z) (bl : Tree) : list nat :=
  match fuel with
  | O => []
  | S f =>
      if Z.leb blcodes rank then []
      else Z.to_nat (t_len bl (bl_order rank)) :: sat_vals f (rank + 1) blcodes bl
  end.

(** Fuel independence, so the literal [Z.to_nat BL_CODES + 1] is reached by a
    rewrite rather than by twenty unfoldings. *)
Lemma sat_bits_fuel_indep : forall f1 f2 rank blcodes bl,
  blcodes - rank <= Z.of_nat f1 -> blcodes - rank <= Z.of_nat f2 ->
  sat_bits f1 rank blcodes bl = sat_bits f2 rank blcodes bl.
Proof.
  induction f1 as [|f1 IH]; intros f2 rank blcodes bl H1 H2.
  - cbn [sat_bits]. destruct f2 as [|f2]; [reflexivity|].
    cbn [sat_bits]. destruct (Z.leb blcodes rank) eqn:Eg; [reflexivity|].
    apply Z.leb_gt in Eg. cbn [Z.of_nat] in H1. lia.
  - destruct f2 as [|f2].
    + cbn [sat_bits]. destruct (Z.leb blcodes rank) eqn:Eg; [reflexivity|].
      apply Z.leb_gt in Eg. cbn [Z.of_nat] in H2. lia.
    + cbn [sat_bits]. destruct (Z.leb blcodes rank) eqn:Eg; [reflexivity|].
      apply Z.leb_gt in Eg.
      rewrite (IH f2 (rank + 1) blcodes bl) by lia. reflexivity.
Qed.

Lemma sat_vals_fuel_indep : forall f1 f2 rank blcodes bl,
  blcodes - rank <= Z.of_nat f1 -> blcodes - rank <= Z.of_nat f2 ->
  sat_vals f1 rank blcodes bl = sat_vals f2 rank blcodes bl.
Proof.
  induction f1 as [|f1 IH]; intros f2 rank blcodes bl H1 H2.
  - cbn [sat_vals]. destruct f2 as [|f2]; [reflexivity|].
    cbn [sat_vals]. destruct (Z.leb blcodes rank) eqn:Eg; [reflexivity|].
    apply Z.leb_gt in Eg. cbn [Z.of_nat] in H1. lia.
  - destruct f2 as [|f2].
    + cbn [sat_vals]. destruct (Z.leb blcodes rank) eqn:Eg; [reflexivity|].
      apply Z.leb_gt in Eg. cbn [Z.of_nat] in H2. lia.
    + cbn [sat_vals]. destruct (Z.leb blcodes rank) eqn:Eg; [reflexivity|].
      apply Z.leb_gt in Eg.
      rewrite (IH f2 (rank + 1) blcodes bl) by lia. reflexivity.
Qed.

(** THE EMITTER HALF.  The range hypothesis is exactly what a code-length tree
    supplies ([ValidLengths cl 7] gives lengths below 8, and 3 bits hold 0..7):
    it is a fact about the tree, not a convenience. *)
Lemma sat_ranks_stream : forall fuel rank blcodes bl b,
  bw_wf b ->
  (forall r, rank <= r < blcodes -> 0 <= t_len bl (bl_order r) < 8) ->
  bw_stream (sat_ranks fuel rank blcodes bl b)
    = bw_stream b ++ sat_bits fuel rank blcodes bl
  /\ bw_wf (sat_ranks fuel rank blcodes bl b).
Proof.
  assert (H8 : (2:Z) ^ 3 = 8) by reflexivity.
  induction fuel as [|f IH]; intros rank blcodes bl b Hwf Hrange.
  - cbn [sat_ranks sat_bits]. rewrite app_nil_r. split; [reflexivity|exact Hwf].
  - cbn [sat_ranks sat_bits].
    destruct (Z.leb blcodes rank) eqn:Eg.
    + rewrite app_nil_r. split; [reflexivity|exact Hwf].
    + apply Z.leb_gt in Eg.
      assert (Hv : 0 <= t_len bl (bl_order rank) < 8) by (apply Hrange; lia).
      assert (Hwf' : bw_wf (bw_send_bits (t_len bl (bl_order rank)) 3 b))
        by (apply bw_send_bits_inv; [exact Hwf | lia | rewrite H8; lia]).
      destruct (IH (rank + 1) blcodes bl
                  (bw_send_bits (t_len bl (bl_order rank)) 3 b) Hwf')
        as [Hs Hi]; [intros r Hr; apply Hrange; lia|].
      split; [|exact Hi].
      rewrite Hs.
      rewrite (bw_send_bits_bits (t_len bl (bl_order rank)) 3 b Hwf)
        by (try lia; rewrite H8; lia).
      rewrite z2n3, <- app_assoc. reflexivity.
Qed.

(** THE DECODER HALF. *)
Lemma read_3bit_vals_sat : forall fuel rank blcodes bl rest,
  (forall r, rank <= r < blcodes -> 0 <= t_len bl (bl_order r) < 8) ->
  read_3bit_vals (length (sat_vals fuel rank blcodes bl))
                 (sat_bits fuel rank blcodes bl ++ rest)
  = Some (sat_vals fuel rank blcodes bl, rest).
Proof.
  induction fuel as [|f IH]; intros rank blcodes bl rest Hrange.
  - cbn [sat_vals sat_bits length read_3bit_vals]. reflexivity.
  - cbn [sat_vals sat_bits].
    destruct (Z.leb blcodes rank) eqn:Eg.
    + cbn [length read_3bit_vals]. reflexivity.
    + apply Z.leb_gt in Eg.
      assert (Hv : 0 <= t_len bl (bl_order rank) < 8) by (apply Hrange; lia).
      cbn [length]. cbn [read_3bit_vals].
      rewrite <- app_assoc.
      rewrite (read_bits_write_bits 3%nat (t_len bl (bl_order rank))
                 (sat_bits f (rank + 1) blcodes bl ++ rest))
        by (change (2 ^ Z.of_nat 3%nat) with 8; lia).
      rewrite (IH (rank + 1) blcodes bl rest)
        by (intros r Hr; apply Hrange; lia).
      reflexivity.
Qed.

(** The two mirrors agree on length, which is what lets the decoder be told how
    many values to read without being told the bits. *)
Lemma sat_vals_length : forall fuel rank blcodes bl,
  0 <= blcodes - rank <= Z.of_nat fuel ->
  Z.of_nat (length (sat_vals fuel rank blcodes bl)) = blcodes - rank.
Proof.
  induction fuel as [|f IH]; intros rank blcodes bl H.
  - cbn [sat_vals length]. cbn [Z.of_nat] in H. lia.
  - cbn [sat_vals].
    destruct (Z.leb blcodes rank) eqn:Eg.
    + apply Z.leb_le in Eg. cbn [length]. lia.
    + apply Z.leb_gt in Eg. cbn [length].
      rewrite Nat2Z.inj_succ. rewrite (IH (rank + 1) blcodes bl) by lia. lia.
Qed.

(** ** 3. THE HEADER PREFIX ROUND TRIP

    Everything [send_all_trees] emits BEFORE the two trees, decoded back: the
    three counts and the [blcodes] code lengths, with the remainder of the
    stream — which is the two trees' bits — untouched. *)

Theorem header_prefix_roundtrip :
  forall lcodes dcodes blcodes bl fuel b rest,
  bw_wf b ->
  0 <= lcodes - 257 < 32 -> 0 <= dcodes - 1 < 32 -> 0 <= blcodes - 4 < 16 ->
  0 <= blcodes <= Z.of_nat fuel ->
  (forall r, 0 <= r < blcodes -> 0 <= t_len bl (bl_order r) < 8) ->
  bw_stream (sat_ranks fuel 0 blcodes bl (hdr_send lcodes dcodes blcodes b))
    = bw_stream b ++ hdr_bits lcodes dcodes blcodes
                  ++ sat_bits fuel 0 blcodes bl
  /\ read_bits 5%nat (hdr_bits lcodes dcodes blcodes
                        ++ sat_bits fuel 0 blcodes bl ++ rest)
     = Some (lcodes - 257,
             write_bits 5%nat (dcodes - 1) ++ write_bits 4%nat (blcodes - 4)
               ++ sat_bits fuel 0 blcodes bl ++ rest)
  /\ read_3bit_vals (Z.to_nat (blcodes - 0))
       (sat_bits fuel 0 blcodes bl ++ rest)
     = Some (sat_vals fuel 0 blcodes bl, rest).
Proof.
  intros lcodes dcodes blcodes bl fuel b rest Hwf Hl Hd Hc Hfuel Hrange.
  destruct (header_stream lcodes dcodes blcodes b Hwf Hl Hd Hc) as [Hhs Hhw].
  destruct (sat_ranks_stream fuel 0 blcodes bl (hdr_send lcodes dcodes blcodes b)
              Hhw Hrange) as [Hss _].
  split.
  - rewrite Hss, Hhs, <- app_assoc. reflexivity.
  - split.
    + destruct (header_decode lcodes dcodes blcodes
                  (sat_bits fuel 0 blcodes bl ++ rest) Hl Hd Hc) as [H1 _].
      exact H1.
    + assert (Hlen : length (sat_vals fuel 0 blcodes bl) = Z.to_nat (blcodes - 0)).
      { assert (Hb : 0 <= blcodes - 0 <= Z.of_nat fuel) by lia.
        pose proof (sat_vals_length fuel 0 blcodes bl Hb) as H. lia. }
      rewrite <- Hlen.
      exact (read_3bit_vals_sat fuel 0 blcodes bl rest Hrange).
Qed.

Print Assumptions header_stream.
Print Assumptions header_decode.
Print Assumptions sat_ranks_stream.
Print Assumptions read_3bit_vals_sat.
Print Assumptions header_prefix_roundtrip.
