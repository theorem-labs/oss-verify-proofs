(** * ClStream — L-B part (iii-a): the RLE'd code-length stream round-trips.

    OWNER: huffman-id (claim §HUFFID; factorization posted at
    §HUFFID-III-STATEMENT).

    WHAT THIS IS.  A DEFLATE dynamic block does not send its code lengths
    literally.  It run-length encodes them with RFC 1951 §3.2.7's three repeat
    symbols — 16 (repeat the PREVIOUS length, 2 extra bits, 3..6 times),
    17 (repeat zero, 3 extra bits, 3..10 times) and 18 (repeat zero, 7 extra
    bits, 11..138 times) — and sends the result through a third Huffman code,
    the code-length tree, whose own bound is [MAX_BL_BITS = 7].

    This file proves the DECODE side inverts the EMIT side on that stream:
    [DeflateSpec.read_lengths], which is the model of inflate's CODELENS phase,
    returns exactly the length list the items denote and leaves the rest of the
    bit stream untouched.

    THE FACTORIZATION, and the honest boundary.  Part (iii) of L-B splits:

      (iii-a) THIS FILE.  The RLE stream at the BIT-LIST level against
              [read_lengths].  Needs no bit-writer bridge.
      (iii-b) NOT THIS FILE, and blocked.  That [Trees.send_tree]'s BW output IS
              this file's bit list.  It needs the lemma
                bw_bits (bw_send_bits v n b) = bw_bits b ++ write_bits n v
              which does not exist anywhere in the tree (measured: no lemma
              mentions both [bw_send_bits] and [write_bits]).  That bridge is
              layer L-C's; I have not claimed it.

    So [CLItem] below is the interface between the two halves: (iii-a) proves
    the items decode correctly, and (iii-b) — whoever owns the writer bridge —
    owes that [send_go] emits exactly these items.  The four constructors are
    in one-to-one correspondence with [send_go]'s four arms
    ([Trees.v:753-780]), which is why they are shaped this way rather than as a
    flat list of symbols:

      count' < mincnt      ->  a run of [CLit] (send_rep: literal codes)
      curlen <> 0          ->  optional [CLit curlen] then [CRep curlen k]
      curlen = 0, k <= 10  ->  [CZ3 k]
      otherwise            ->  [CZ11 k]

    Every range hypothesis below is RFC 1951's own, and each one is exactly
    what makes the corresponding [read_bits] round trip: 3..6 fits in 2 extra
    bits, 3..10 in 3, 11..138 in 7. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees DeflateSpec.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

(** ** The item stream *)

Inductive CLItem : Set :=
| CLit  (len : nat)        (** a literal code length, 0..15 *)
| CRep  (prev k : nat)     (** symbol 16: repeat [prev], [k] in 3..6 *)
| CZ3   (k : nat)          (** symbol 17: [k] zeros, [k] in 3..10 *)
| CZ11  (k : nat).         (** symbol 18: [k] zeros, [k] in 11..138 *)

Definition cl_item_lens (it : CLItem) : list nat :=
  match it with
  | CLit l   => [l]
  | CRep p k => repeat p k
  | CZ3 k    => repeat 0%nat k
  | CZ11 k   => repeat 0%nat k
  end.

Fixpoint cl_lens (items : list CLItem) : list nat :=
  match items with
  | [] => []
  | it :: tl => cl_item_lens it ++ cl_lens tl
  end.

(** The bits an item emits: its code-length codeword, then its extra field.
    The order is [send_code] first and [send_bits] second, matching
    [Trees.v:773-780] — [bw_send_bits (count' - 3) 2 (send_code REP_3_6 bl b)]
    applies [send_code] to the INNER writer, so the codeword reaches the
    stream first. *)
Definition cl_item_bits (cl : list nat) (it : CLItem) : option (list bool) :=
  match it with
  | CLit l =>
      match code_for cl 7%nat l with
      | Some cw => Some cw
      | None => None
      end
  | CRep _ k =>
      match code_for cl 7%nat 16%nat with
      | Some cw => Some (cw ++ write_bits 2%nat (Z.of_nat k - 3))
      | None => None
      end
  | CZ3 k =>
      match code_for cl 7%nat 17%nat with
      | Some cw => Some (cw ++ write_bits 3%nat (Z.of_nat k - 3))
      | None => None
      end
  | CZ11 k =>
      match code_for cl 7%nat 18%nat with
      | Some cw => Some (cw ++ write_bits 7%nat (Z.of_nat k - 11))
      | None => None
      end
  end.

Fixpoint cl_bits (cl : list nat) (items : list CLItem) : option (list bool) :=
  match items with
  | [] => Some []
  | it :: tl =>
      match cl_item_bits cl it, cl_bits cl tl with
      | Some b1, Some b2 => Some (b1 ++ b2)
      | _, _ => None
      end
  end.

(** Well-formedness, threaded through the accumulator because symbol 16's
    meaning DEPENDS on it: [rl_run 16] reads [last_len acc], so an item stream
    is only meaningful relative to what precedes it.  [CRep]'s [prev] field is
    required to agree, which is the one place a loose statement would have let
    a wrong stream through. *)
Fixpoint CLWf (acc : list nat) (items : list CLItem) : Prop :=
  match items with
  | [] => True
  | CLit l :: tl   => (l <= 15)%nat /\ CLWf (acc ++ [l]) tl
  | CRep p k :: tl => (3 <= k <= 6)%nat /\ last_len acc = Some p
                      /\ CLWf (acc ++ repeat p k) tl
  | CZ3 k :: tl    => (3 <= k <= 10)%nat /\ CLWf (acc ++ repeat 0%nat k) tl
  | CZ11 k :: tl   => (11 <= k <= 138)%nat /\ CLWf (acc ++ repeat 0%nat k) tl
  end.

(** ** Small facts *)

(** NOT provable without the well-formedness: the repeat counts are constrained
    by [CLWf], not by the item TYPE, so [CRep p 0] is a perfectly good [CLItem]
    denoting no lengths at all.  Taking the hypothesis is the honest fix; the
    alternative (a dependent item type) would push RFC ranges into every
    constructor application. *)
Lemma cl_item_lens_pos : forall acc it tl,
  CLWf acc (it :: tl) -> (1 <= length (cl_item_lens it))%nat.
Proof.
  intros acc it tl H; destruct it; cbn [cl_item_lens].
  - cbn [length]. lia.
  - cbn [CLWf] in H. destruct H as [Hk _]. rewrite repeat_length. lia.
  - cbn [CLWf] in H. destruct H as [Hk _]. rewrite repeat_length. lia.
  - cbn [CLWf] in H. destruct H as [Hk _]. rewrite repeat_length. lia.
Qed.

(** Every item denotes at least one length, so [need] strictly decreases and
    the fuel never binds — the same role [rl_run_pos] plays on the decode side. *)
Lemma cl_lens_app : forall it tl,
  length (cl_lens (it :: tl))
  = (length (cl_item_lens it) + length (cl_lens tl))%nat.
Proof. intros it tl. cbn [cl_lens]. rewrite length_app. reflexivity. Qed.

(** The extra field round trips exactly when the count is in RFC range. *)
Lemma extra_roundtrip : forall n k base rest,
  (base <= k)%nat -> (Z.of_nat k - Z.of_nat base < 2 ^ Z.of_nat n)%Z ->
  read_bits n (write_bits n (Z.of_nat k - Z.of_nat base) ++ rest)
  = Some (Z.of_nat k - Z.of_nat base, rest)%Z.
Proof.
  intros n k base rest Hb Hlt. apply read_bits_write_bits. lia.
Qed.

(** [cbn [read_lengths_fuel]] reduces the fixpoints it finds along the way even
    with a delta list, so it happily turns [write_bits 2 v] into a two-element
    literal list and then the [hdecode] rewrite no longer matches.  Sealing the
    two bit primitives keeps the goal in the shape the lemmas are stated about.
    Both are already Qed above and in [Bits.v], so nothing is lost. *)
Local Opaque write_bits read_bits.

(** ** THE INVERSE, generalised over the accumulator, the fuel and [need]

    [need] is a PARAMETER with an equation rather than the literal
    [length (cl_lens items)], because [read_lengths_fuel] matches on [need]
    first and [cbn] will not reduce that match unless [need] is
    constructor-headed.  Written the direct way the goal carries
    [match k + length (cl_lens tl) with ...] with [k] a variable and nothing
    reduces.  With the equation, [destruct need] supplies the constructor and
    [lia] carries the arithmetic. *)

Lemma read_lengths_fuel_cl : forall items cl acc bits rest f need,
  ValidLengths cl 7%nat ->
  CLWf acc items ->
  cl_bits cl items = Some bits ->
  need = length (cl_lens items) ->
  (need <= f)%nat ->
  read_lengths_fuel f cl need acc (bits ++ rest)
  = Some (acc ++ cl_lens items, rest).
Proof.
  induction items as [|it tl IH];
    intros cl acc bits rest f need HV Hwf Hb Hneed Hf.
  - cbn [cl_lens] in *. cbn [cl_bits] in Hb. inversion Hb; subst bits.
    cbn [length] in Hneed. subst need.
    rewrite app_nil_r.
    (* [read_lengths_fuel] recurses on FUEL, so cbn will not unfold it while
       the fuel is a variable -- even though the [need = 0] arm is decided.
       DeflateSpec's own read_lengths_fuel_indep destructs for the same
       reason. *)
    destruct f; reflexivity.
  - cbn [cl_bits] in Hb.
    destruct (cl_item_bits cl it) as [b1|] eqn:E1; [|discriminate].
    destruct (cl_bits cl tl) as [b2|] eqn:E2; [|discriminate].
    inversion Hb; subst bits. clear Hb.
    rewrite <- app_assoc.
    pose proof (cl_item_lens_pos acc it tl Hwf) as Hpos.
    rewrite cl_lens_app in Hneed.
    destruct need as [|n]; [lia|].
    destruct f as [|f]; [lia|].
    destruct it as [l|p k|k|k].
    + (* CLit: one literal code length *)
      cbn [cl_item_lens] in Hneed. cbn [length] in Hneed.
      destruct Hwf as [Hl15 Hwf'].
      cbn [cl_item_bits] in E1.
      destruct (code_for cl 7%nat l) as [cw|] eqn:Ecf; [|discriminate].
      inversion E1; subst b1. clear E1.
      cbn [read_lengths_fuel].
      rewrite (hdecode_code_for cl 7%nat l cw (b2 ++ rest) HV Ecf).
      replace (Nat.leb l 15) with true by (symmetry; apply Nat.leb_le; lia).
      rewrite (IH cl (acc ++ [l]) b2 rest f (S n - 1)%nat HV Hwf' E2) by lia.
      cbn [cl_lens cl_item_lens]. rewrite <- app_assoc. reflexivity.
    + (* CRep: symbol 16, repeat the previous length, 2 extra bits *)
      cbn [cl_item_lens] in Hneed. rewrite repeat_length in Hneed.
      destruct Hwf as [Hk [Hlast Hwf']].
      cbn [cl_item_bits] in E1.
      destruct (code_for cl 7%nat 16%nat) as [cw|] eqn:Ecf; [|discriminate].
      inversion E1; subst b1. clear E1.
      rewrite <- app_assoc.
      cbn [read_lengths_fuel].
      rewrite (hdecode_code_for cl 7%nat 16%nat cw
                 (write_bits 2%nat (Z.of_nat k - 3) ++ b2 ++ rest) HV Ecf).
      cbn [Nat.leb rl_run Nat.eqb]. rewrite Hlast.
      replace (Z.of_nat k - 3)%Z with (Z.of_nat k - Z.of_nat 3%nat)%Z
        by (cbn; lia).
      rewrite (extra_roundtrip 2%nat k 3%nat (b2 ++ rest)) by (cbn; lia).
      replace (Z.to_nat (Z.of_nat k - Z.of_nat 3%nat) + 3)%nat with k by lia.
      replace (Nat.ltb (S n) k) with false by (symmetry; apply Nat.ltb_ge; lia).
      rewrite (IH cl (acc ++ repeat p k) b2 rest f (S n - k)%nat HV Hwf' E2)
        by lia.
      cbn [cl_lens cl_item_lens]. rewrite <- app_assoc. reflexivity.
    + (* CZ3: symbol 17, 3..10 zeros, 3 extra bits *)
      cbn [cl_item_lens] in Hneed. rewrite repeat_length in Hneed.
      destruct Hwf as [Hk Hwf'].
      cbn [cl_item_bits] in E1.
      destruct (code_for cl 7%nat 17%nat) as [cw|] eqn:Ecf; [|discriminate].
      inversion E1; subst b1. clear E1.
      rewrite <- app_assoc.
      cbn [read_lengths_fuel].
      rewrite (hdecode_code_for cl 7%nat 17%nat cw
                 (write_bits 3%nat (Z.of_nat k - 3) ++ b2 ++ rest) HV Ecf).
      cbn [Nat.leb rl_run Nat.eqb].
      replace (Z.of_nat k - 3)%Z with (Z.of_nat k - Z.of_nat 3%nat)%Z
        by (cbn; lia).
      rewrite (extra_roundtrip 3%nat k 3%nat (b2 ++ rest)) by (cbn; lia).
      replace (Z.to_nat (Z.of_nat k - Z.of_nat 3%nat) + 3)%nat with k by lia.
      replace (Nat.ltb (S n) k) with false by (symmetry; apply Nat.ltb_ge; lia).
      rewrite (IH cl (acc ++ repeat 0%nat k) b2 rest f (S n - k)%nat HV Hwf' E2)
        by lia.
      cbn [cl_lens cl_item_lens]. rewrite <- app_assoc. reflexivity.
    + (* CZ11: symbol 18, 11..138 zeros, 7 extra bits *)
      cbn [cl_item_lens] in Hneed. rewrite repeat_length in Hneed.
      destruct Hwf as [Hk Hwf'].
      cbn [cl_item_bits] in E1.
      destruct (code_for cl 7%nat 18%nat) as [cw|] eqn:Ecf; [|discriminate].
      inversion E1; subst b1. clear E1.
      rewrite <- app_assoc.
      cbn [read_lengths_fuel].
      rewrite (hdecode_code_for cl 7%nat 18%nat cw
                 (write_bits 7%nat (Z.of_nat k - 11) ++ b2 ++ rest) HV Ecf).
      cbn [Nat.leb rl_run Nat.eqb].
      replace (Z.of_nat k - 11)%Z with (Z.of_nat k - Z.of_nat 11%nat)%Z
        by (cbn; lia).
      rewrite (extra_roundtrip 7%nat k 11%nat (b2 ++ rest)) by (cbn; lia).
      replace (Z.to_nat (Z.of_nat k - Z.of_nat 11%nat) + 11)%nat with k by lia.
      replace (Nat.ltb (S n) k) with false by (symmetry; apply Nat.ltb_ge; lia).
      rewrite (IH cl (acc ++ repeat 0%nat k) b2 rest f (S n - k)%nat HV Hwf' E2)
        by lia.
      cbn [cl_lens cl_item_lens]. rewrite <- app_assoc. reflexivity.
Qed.

(** ** (iii-a): the headline

    The RLE'd code-length stream decodes back to exactly the lengths it
    denotes, with the rest of the bit stream untouched.

    [rest] is universally quantified for the same reason as everywhere else in
    L-B: without it, a decoder that swallowed its whole input would satisfy the
    statement, and a length vector is followed immediately by the
    literal/length and distance code lengths, so stopping in the right place is
    the property that matters. *)
Theorem read_lengths_inverts_cl_bits : forall cl items bits rest,
  ValidLengths cl 7%nat ->
  CLWf [] items ->
  cl_bits cl items = Some bits ->
  read_lengths cl (length (cl_lens items)) (bits ++ rest)
  = Some (cl_lens items, rest).
Proof.
  intros cl items bits rest HV Hwf Hb. unfold read_lengths.
  rewrite (read_lengths_fuel_cl items cl [] bits rest
             (length (cl_lens items)) (length (cl_lens items))
             HV Hwf Hb (eq_refl _) (Nat.le_refl _)).
  reflexivity.
Qed.


(** ** WITNESS: the hypotheses are met, and the conclusion is closed

    Four hypotheses quantify [read_lengths_inverts_cl_bits].  A theorem whose
    hypotheses no object satisfies is indistinguishable from a sound one until
    someone produces one, so here is one.

    [clw] is a code-length tree assigning 2-bit codes to exactly the four
    symbols the stream uses: literals 2 and 3, plus repeat symbols 16 and 17.
    Its Kraft sum at 7 is 4 * 2^5 = 128 = 2^7, so it is a COMPLETE code. *)

Definition clw : list nat := [0;0;2;2;0;0;0;0;0;0;0;0;0;0;0;0;2;2;0]%nat.

(** One item of each kind that carries a repeat count, plus literals on both
    sides so the accumulator threading is exercised in both directions. *)
Definition itemsw : list CLItem := [CLit 3; CRep 3 4; CZ3 5; CLit 2].

Definition bitsw : list bool :=
  [false;true;  true;false;true;false;  true;true;false;true;false;  false;false].

Lemma clw_valid : ValidLengths clw 7%nat.
Proof. apply valid_lengths_b_true. vm_compute. reflexivity. Qed.

Lemma itemsw_wf : CLWf [] itemsw.
Proof.
  cbn [CLWf]. repeat split; try lia; reflexivity.
Qed.

Example itemsw_bits : cl_bits clw itemsw = Some bitsw.
Proof. vm_compute. reflexivity. Qed.

Example itemsw_lens : cl_lens itemsw = [3;3;3;3;3;0;0;0;0;0;2]%nat.
Proof. vm_compute. reflexivity. Qed.

Example itemsw_need : length (cl_lens itemsw) = 11%nat.
Proof. vm_compute. reflexivity. Qed.

(** The codes the tree assigns, for a reader checking the bit stream by hand:
    symbol 2 -> 00, 3 -> 01, 16 -> 10, 17 -> 11.  So [bitsw] reads
    01 | 10 10 | 11 010 | 00 — literal 3, then symbol 16 with extra 01 (= 1,
    so 1+3 = 4 repeats), then symbol 17 with extra 010 (= 2, so 2+3 = 5 zeros),
    then literal 2.  Eleven lengths from thirteen bits. *)
Example clw_codes :
  map (fun s => code_for clw 7%nat s) [2;3;16;17]%nat
  = [Some [false;false]; Some [false;true]; Some [true;false]; Some [true;true]].
Proof. vm_compute. reflexivity. Qed.

(** THE APPLIED CONCLUSION, for an arbitrary remainder. *)
Theorem itemsw_roundtrip : forall rest,
  read_lengths clw (length (cl_lens itemsw)) (bitsw ++ rest)
  = Some (cl_lens itemsw, rest).
Proof.
  intro rest.
  apply (read_lengths_inverts_cl_bits clw itemsw bitsw rest
           clw_valid itemsw_wf itemsw_bits).
Qed.

(** ** The accumulator conjunct is load bearing

    [CRep]'s [prev] field must agree with [last_len acc].  Dropping that
    conjunct would let an item stream claim a repeat of a length that is not
    the one the decoder will copy — and the decoder copies [last_len acc], so
    the two would silently disagree.  Here it is refuted rather than asserted:
    the same stream with [CRep 5] instead of [CRep 3] is NOT well formed. *)
Example CLWf_rejects_wrong_prev : ~ CLWf [] [CLit 3; CRep 5 4].
Proof.
  intro H. cbn [CLWf] in H.
  destruct H as [_ [_ [Hlast _]]]. vm_compute in Hlast. discriminate.
Qed.

(** ...and the range conjuncts likewise: 7 repeats do not fit symbol 16's two
    extra bits, so RFC 1951's 3..6 is not a stylistic choice. *)
Example CLWf_rejects_out_of_range : ~ CLWf [] [CLit 3; CRep 3 7].
Proof. intro H. cbn [CLWf] in H. destruct H as [_ [Hk _]]. lia. Qed.

Print Assumptions read_lengths_inverts_cl_bits.
Print Assumptions itemsw_roundtrip.
