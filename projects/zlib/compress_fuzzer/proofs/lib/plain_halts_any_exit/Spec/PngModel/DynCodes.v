(** * DynCodes — the DYNAMIC [tree_codes_upto] instance: a [gen_codes]-built tree
      satisfies L-C's symbol premise.

    OWNER: huffman-id.  TL's assignment after (B)'s plumbing.

    WHAT L-C HAS AND WHAT IT LACKS.  symbol-id's [CbEmit.tree_codes_upto t
    lengths n] is the premise [cb_step_emits_lit] and friends consume: for every
    symbol below [n] that HAS a canonical codeword, the tree's stored (len, code)
    pair is in range and writes exactly that codeword.  They discharge it for the
    STATIC trees by [vm_compute] ([static_ltree_codes], [static_dtree_codes]).
    For a DYNAMIC block there is no table to compute over — the tree is whatever
    [gen_codes] built — so the instance has to come from a theorem about
    [gen_codes], which is this lane.

    THE PRICE WAS LOW, AND ONLY BECAUSE I READ THEIR DEFINITIONS FIRST.
    [BwStream.v:214] defines [zwrite n v := write_bits (Z.to_nat n) v], and
    [HuffGenCodes.gen_codes_emits_code_for] already concludes

        write_bits (Z.to_nat (t_len (gen_codes ...) s)) (t_code (gen_codes ...) s) = cw

    which IS [zwrite (t_len ...) (t_code ...) = cw], up to unfolding a definition
    and flipping the equation.  The third and hardest-looking conjunct was
    already proved months of work ago under a different name.  Pricing this from
    the signature ("they want zwrite, I have write_bits") would have quoted a
    bridge that does not exist.

    CAVEAT RETIRED, and the reason is worth more than the caveat.  The first
    version of this file restated [zwrite] by its definition and named its own
    predicate [TreeCodesUpto], because [BwStream.v] and [CbEmit.v] were scratch
    and outside my [-Q] roots; I said on the board that the literal composition
    needed symbol-id's hand.  **Both files went LIVE at 02:58 while I was
    working**, so [tree_codes_upto] is now directly reachable and this file proves
    THEIR predicate, not a convertible copy of it.  No caveat, no bridge, no
    hand-off.

    I only found that out because I re-checked the live tree before relying on my
    own earlier measurement — the same check that had told me, an hour before, that
    BwStream was NOT live.  **A fact about another lane's tree has a timestamp; the
    tree is not mine and it moves.**  That is the third time in this campaign that
    a "verified" fact about someone else's tree went stale under me, and the only
    defence that has worked is re-measuring at the moment of use rather than
    citing the earlier measurement. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees BwStream CbEmit.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import HuffGenCodes SendItems.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** No restatement: [zwrite] and [tree_codes_upto] are taken from the LIVE
    [BwStream.v] and [CbEmit.v].  See the CAVEAT RETIRED note in the header. *)

(** ** What [code_for] returning [Some] already tells you

    Its own guard rejects length 0 and length above [maxBits], so the range of
    the symbol's length is free — no appeal to [ValidLengths] needed. *)
Lemma hid_code_for_inv : forall L sym cw,
  code_for L 15%nat sym = Some cw ->
  exists len, nth_error L sym = Some len /\ (1 <= len <= 15)%nat.
Proof.
  intros L sym cw H. unfold code_for in H.
  destruct (nth_error L sym) as [len|] eqn:E; [|discriminate].
  destruct ((len =? 0)%nat || (15 <? len)%nat) eqn:Eg; [discriminate|].
  apply orb_false_iff in Eg as [E0 E1].
  apply Nat.eqb_neq in E0. apply Nat.ltb_ge in E1.
  exists len. split; [reflexivity | lia].
Qed.

(** ** THE DYNAMIC INSTANCE

    Same hypotheses [gen_codes] is always used under in this lane: the tree's
    length array agrees with the length vector, the histogram matches it, the
    lengths are Kraft-valid, and nothing lives past [maxc]. *)
Theorem gen_codes_tree_codes_upto : forall L t maxc blc n,
  LensOf t L -> BlcOf blc L -> ValidLengths L 15%nat ->
  AbsentBeyond L maxc -> -1 <= maxc <= 288 ->
  tree_codes_upto (gen_codes t maxc blc) L n.
Proof.
  intros L t maxc blc n Hlens Hblc HV Hab Hmc i cw Hi Hcf.
  unfold tree_codes_upto in *.
  destruct (hid_code_for_inv L i cw Hcf) as [len [He Hlen]].
  (* the length is untouched by [gen_codes] and is the vector's entry *)
  assert (Hlt : (i < length L)%nat)
    by (apply nth_error_Some; rewrite He; discriminate).
  assert (Hnth : nth i L 0%nat = len) by (apply nth_error_nth; exact He).
  assert (Hl : t_len (gen_codes t maxc blc) (Z.of_nat i) = Z.of_nat len).
  { rewrite gen_codes_len. rewrite (Hlens i Hlt). rewrite Hnth. reflexivity. }
  split; [| split].
  - (* in [1, 15], so certainly in (0, 16] *)
    rewrite Hl. lia.
  - (* the stored code fits its own width *)
    rewrite Hl.
    exact (gen_codes_code_lt L t maxc blc i len Hlens Hblc HV Hab Hmc He Hlen).
  - (* and the pair writes exactly the canonical codeword — this is
       [gen_codes_emits_code_for] with [zwrite] unfolded *)
    unfold zwrite. symmetry.
    exact (gen_codes_emits_code_for L t maxc blc i cw Hlens Hblc HV Hab Hmc Hcf).
Qed.

(** The bound [n] is arbitrary: the predicate quantifies over symbols BELOW [n]
    and every one of them is covered, so L-C may instantiate it at whatever
    [n] its own step lemma needs (they use [256 <= n] for literals). *)
Corollary gen_codes_tree_codes_any_n : forall L t maxc blc,
  LensOf t L -> BlcOf blc L -> ValidLengths L 15%nat ->
  AbsentBeyond L maxc -> -1 <= maxc <= 288 ->
  forall n, tree_codes_upto (gen_codes t maxc blc) L n.
Proof. intros. apply gen_codes_tree_codes_upto; assumption. Qed.

(** ** Why the static instance did NOT already cover this

    [static_ltree_codes] is a closed computation over a baked 288-entry table.
    It says nothing about a tree [gen_codes] built at run time from a block's own
    histogram, which is what a DYNAMIC block uses and what [_tr_flush_block]
    selects whenever the dynamic encoding is shorter.  The two instances have the
    same statement and disjoint proofs: theirs is [vm_compute], mine is the
    canonical-code theorem.  That is the good case of a duplicated statement —
    two derivations, genuinely independent in method AND in input, unlike the
    BwBits/BwStream pair where the inputs were shared. *)

Print Assumptions hid_code_for_inv.
Print Assumptions gen_codes_tree_codes_upto.
Print Assumptions gen_codes_tree_codes_any_n.
