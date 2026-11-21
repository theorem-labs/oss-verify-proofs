(** * LdDynSplit — item (v-5b): ONE [read_lengths] call spanning BOTH trees.

    OWNER: ld-seams.  Builds on huffman-id's staged [ClStream]/[SendItems]
    (see LdDynSeam.v for the pin and the shadowing check).

    ** THE OBLIGATION, and why it is not a corollary

    [send_all_trees] emits the literal/length tree and the distance tree with
    TWO [send_tree] calls ([Trees.v:832-833]).  [decode_dynamic_tables] reads
    them back with ONE [read_lengths] call for [nlit + ndist] lengths
    ([DeflateSpec.v:906]).  huffman-id's round trip is stated per tree, at
    [need = length (cl_lens items)] exactly, so it does not compose: the
    combined call runs at a LARGER [need], and [read_lengths_fuel] is
    need-DEPENDENT, not a prefix computation — its run arm rejects a repeat that
    would overshoot ([if Nat.ltb need k then None]).  Larger [need] admits runs
    the per-tree statement rejects, so the composition has to be proved, and it
    has to be proved in the direction where the guard is looser.

    ** THE HAZARD I EXPECTED, AND WHY IT DISSOLVED — worth the paragraph because
    the reason is a fact about their hypothesis, not about my proof

    At the head of the distance stream the decoder's accumulator is not empty:
    it holds all [nlit] literal lengths.  [CLWf]'s [CRep] clause reads
    [last_len acc].  So a repeat symbol at the head of the second tree's stream
    would copy THE LAST LITERAL LENGTH, across a boundary the encoder never
    sees, and my [CLWf_last_len_cong] (LdDynSeam.v) does NOT bridge it —
    congruence needs [last_len [] = last_len (cl_lens items1)], i.e.
    [None = Some _].

    I was ready to owe huffman-id a lemma that [send_tree_items] never begins
    with a repeat.  It is not needed: [CLWf [] items] with a [CRep] at the head
    demands [last_len [] = Some p], and [last_len [] = None].  **Their
    hypothesis already excludes the case**, so well-formedness at the empty
    accumulator implies it at ANY accumulator ([CLWf_nil_any_acc] below).  The
    implication is strictly one-directional and the converse is FALSE — see
    [LdDynSeam.CLWf_does_depend_on_the_accumulator], which is why this is stated
    as an implication and not an iff.

    So the encoder-side fact I thought was owed is discharged by the decoder
    side's well-formedness predicate.  Recording it because the reverse mistake
    — assuming a boundary is free — would have been invisible: every per-tree
    theorem stays green either way. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees DeflateSpec BwStream.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  HuffGenCodes ClStream SendItems SendGo SendGoLens SendGoWf SendTreeRT.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import LdDynSeam.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** [cbn] will happily turn [write_bits 2 v] into a two-element literal list,
    after which the [hdecode] rewrite no longer matches.  Same sealing
    huffman-id's ClStream.v uses, and for the same reason; both primitives are
    already proved. *)
Local Opaque write_bits read_bits.

(** ** 1. Well-formedness at [[]] transfers to any accumulator *)

(** The head item is the only one whose clause can read the incoming
    accumulator, and only [CRep] does. *)
Definition HeadIndep (items : list CLItem) : Prop :=
  match items with
  | CRep _ _ :: _ => False
  | _ => True
  end.

Lemma CLWf_nil_head_indep : forall items, CLWf [] items -> HeadIndep items.
Proof.
  intros items H. destruct items as [|it tl]; [exact I|].
  destruct it as [l|p k|k|k]; [exact I| |exact I|exact I].
  cbn [CLWf] in H. destruct H as [_ [Hprev _]].
  cbn [last_len rev] in Hprev. discriminate Hprev.
Qed.

Lemma CLWf_head_indep_any_acc : forall items acc acc',
  HeadIndep items -> CLWf acc items -> CLWf acc' items.
Proof.
  intros items acc acc' Hhi H.
  destruct items as [|it tl]; [exact I|].
  destruct it as [l|p k|k|k]; cbn [CLWf] in H |- *.
  - destruct H as [Hl Htl]. split; [exact Hl|].
    apply (CLWf_last_len_cong tl (acc ++ [l])); [|exact Htl].
    assert (Hne : [l] <> []) by (intro C; discriminate C).
    rewrite (last_len_app_nonnil acc [l] Hne),
            (last_len_app_nonnil acc' [l] Hne). reflexivity.
  - exact (match Hhi with end).
  - destruct H as [Hk Htl]. split; [exact Hk|].
    apply (CLWf_last_len_cong tl (acc ++ repeat 0%nat k)); [|exact Htl].
    assert (Hne : repeat 0%nat k <> []) by (apply repeat_nonnil; lia).
    rewrite (last_len_app_nonnil acc (repeat 0%nat k) Hne),
            (last_len_app_nonnil acc' (repeat 0%nat k) Hne). reflexivity.
  - destruct H as [Hk Htl]. split; [exact Hk|].
    apply (CLWf_last_len_cong tl (acc ++ repeat 0%nat k)); [|exact Htl].
    assert (Hne : repeat 0%nat k <> []) by (apply repeat_nonnil; lia).
    rewrite (last_len_app_nonnil acc (repeat 0%nat k) Hne),
            (last_len_app_nonnil acc' (repeat 0%nat k) Hne). reflexivity.
Qed.

Lemma CLWf_nil_any_acc : forall items acc, CLWf [] items -> CLWf acc items.
Proof.
  intros items acc H.
  exact (CLWf_head_indep_any_acc items [] acc (CLWf_nil_head_indep items H) H).
Qed.

(** ** 2. The residual-[need] split

    huffman-id's [read_lengths_fuel_cl] with [need] carrying a RESIDUAL [m]:
    reading a stream that denotes [items] leaves the decoder mid-flight, at
    [need = m] and accumulator [acc ++ cl_lens items], rather than finishing.
    Their induction, threaded with [m] and a second fuel [g] — the fuel
    bookkeeping goes through [read_lengths_fuel_indep] (DeflateSpec.v:863)
    rather than subtracting, so the statement stays readable at the call site. *)

Lemma read_lengths_fuel_cl_residual : forall items cl acc bits rest f g need m,
  ValidLengths cl 7%nat ->
  CLWf acc items ->
  cl_bits cl items = Some bits ->
  need = (length (cl_lens items) + m)%nat ->
  (need <= f)%nat -> (m <= g)%nat ->
  read_lengths_fuel f cl need acc (bits ++ rest)
  = read_lengths_fuel g cl m (acc ++ cl_lens items) rest.
Proof.
  induction items as [|it tl IH];
    intros cl acc bits rest f g need m HV Hwf Hb Hneed Hf Hg.
  - cbn [cl_bits] in Hb. inversion Hb; subst bits. clear Hb.
    cbn [cl_lens] in *. cbn [length] in Hneed. rewrite Nat.add_0_l in Hneed.
    rewrite app_nil_l, app_nil_r. subst need.
    apply read_lengths_fuel_indep; lia.
  - cbn [cl_bits] in Hb.
    destruct (cl_item_bits cl it) as [b1|] eqn:E1; [|discriminate].
    destruct (cl_bits cl tl) as [b2|] eqn:E2; [|discriminate].
    inversion Hb; subst bits. clear Hb.
    rewrite <- app_assoc.
    pose proof (cl_item_lens_pos acc it tl Hwf) as Hpos.
    (* QUALIFIED DELIBERATELY.  Two different lemmas in huffman-id's staged tree
       carry the name [cl_lens_app]: ClStream's (the length of a cons) and
       SendGoWf's (cl_lens over an append).  A file importing both silently gets
       the later one, and the failure is a no-subterm-matching error pointing at
       a hypothesis that looks correct.  Reported to them. *)
    rewrite ClStream.cl_lens_app in Hneed.
    destruct need as [|n]; [lia|].
    destruct f as [|f]; [lia|].
    destruct it as [l|p k|k|k].
    + (* CLit *)
      cbn [cl_item_lens] in Hneed. cbn [length] in Hneed.
      destruct Hwf as [Hl15 Hwf'].
      cbn [cl_item_bits] in E1.
      destruct (code_for cl 7%nat l) as [cw|] eqn:Ecf; [|discriminate].
      inversion E1; subst b1. clear E1.
      cbn [read_lengths_fuel].
      rewrite (hdecode_code_for cl 7%nat l cw (b2 ++ rest) HV Ecf).
      replace (Nat.leb l 15) with true by (symmetry; apply Nat.leb_le; lia).
      rewrite (IH cl (acc ++ [l]) b2 rest f g (S n - 1)%nat m HV Hwf' E2)
        by lia.
      cbn [cl_lens cl_item_lens]. rewrite <- app_assoc. reflexivity.
    + (* CRep: symbol 16, 2 extra bits *)
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
      rewrite (IH cl (acc ++ repeat p k) b2 rest f g (S n - k)%nat m
                 HV Hwf' E2) by lia.
      cbn [cl_lens cl_item_lens]. rewrite <- app_assoc. reflexivity.
    + (* CZ3: symbol 17, 3 extra bits *)
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
      rewrite (IH cl (acc ++ repeat 0%nat k) b2 rest f g (S n - k)%nat m
                 HV Hwf' E2) by lia.
      cbn [cl_lens cl_item_lens]. rewrite <- app_assoc. reflexivity.
    + (* CZ11: symbol 18, 7 extra bits *)
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
      rewrite (IH cl (acc ++ repeat 0%nat k) b2 rest f g (S n - k)%nat m
                 HV Hwf' E2) by lia.
      cbn [cl_lens cl_item_lens]. rewrite <- app_assoc. reflexivity.
Qed.

(** ** 3. THE SEAM: two item streams, one [read_lengths]

    Both trees' well-formedness is taken at the EMPTY accumulator, which is the
    form huffman-id's [send_tree_items_wf] delivers for each tree
    independently.  The accumulator transfer happens inside, via
    [CLWf_nil_any_acc].

    [rest] is universally quantified for the same reason it is everywhere else
    in this layer: a decoder that swallowed its input would satisfy a statement
    without it, and what follows a dynamic header is the compressed block
    itself, so stopping in the right place IS the property. *)

Theorem read_lengths_spans_two_trees : forall cl items1 items2 bits1 bits2 rest,
  ValidLengths cl 7%nat ->
  CLWf [] items1 -> CLWf [] items2 ->
  cl_bits cl items1 = Some bits1 ->
  cl_bits cl items2 = Some bits2 ->
  read_lengths cl (length (cl_lens items1) + length (cl_lens items2))
    (bits1 ++ bits2 ++ rest)
  = Some (cl_lens items1 ++ cl_lens items2, rest).
Proof.
  intros cl items1 items2 bits1 bits2 rest HV Hwf1 Hwf2 Hb1 Hb2.
  unfold read_lengths.
  rewrite (read_lengths_fuel_cl_residual items1 cl [] bits1 (bits2 ++ rest)
             (length (cl_lens items1) + length (cl_lens items2))
             (length (cl_lens items2))
             (length (cl_lens items1) + length (cl_lens items2))
             (length (cl_lens items2))
             HV Hwf1 Hb1 eq_refl (Nat.le_refl _) (Nat.le_refl _)).
  rewrite app_nil_l.
  exact (read_lengths_fuel_cl items2 cl (cl_lens items1) bits2 rest
           (length (cl_lens items2)) (length (cl_lens items2))
           HV (CLWf_nil_any_acc items2 (cl_lens items1) Hwf2) Hb2
           eq_refl (Nat.le_refl _)).
Qed.

(** ** 4. THE INSTANCE

    A theorem whose hypotheses nothing satisfies is indistinguishable from a
    sound one until someone builds one.  huffman-id's witness stream, read
    TWICE out of one call — 22 lengths, the second eleven decoded with the first
    eleven sitting in the accumulator, which is exactly the configuration the
    boundary paragraph above is about.  Fully concrete on both sides, so a
    reader can see that the second tree's lengths are not perturbed by the
    first tree's. *)

Theorem itemsw_twice_roundtrip : forall rest,
  read_lengths clw 22%nat (bitsw ++ bitsw ++ rest)
  = Some ([3;3;3;3;3;0;0;0;0;0;2;3;3;3;3;3;0;0;0;0;0;2]%nat, rest).
Proof.
  intro rest.
  pose proof (read_lengths_spans_two_trees clw itemsw itemsw bitsw bitsw rest
                clw_valid itemsw_wf itemsw_wf itemsw_bits itemsw_bits) as H.
  rewrite itemsw_lens in H. cbn [length app Nat.add] in H. exact H.
Qed.

Print Assumptions CLWf_nil_any_acc.
Print Assumptions read_lengths_fuel_cl_residual.
Print Assumptions read_lengths_spans_two_trees.
Print Assumptions itemsw_twice_roundtrip.
