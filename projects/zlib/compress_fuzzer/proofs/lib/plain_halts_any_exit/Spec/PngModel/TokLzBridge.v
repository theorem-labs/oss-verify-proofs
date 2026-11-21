(** * Spec.PngModel.TokLzBridge — Tok (Trees.v quarantine contract) to lz_sym
      (Huff.v spec decoder): one vocabulary for the resolved payload.

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-19).  P1 of the Q5 plan
    (PLAN.md §4).

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    WHY THIS FILE EXISTS.  The walk layer (ds_loop invariants) speaks
    [Trees.Tok] and concludes [Trees.resolve] facts — that is the quarantine
    contract [cRes] of Trees.v §19.  The decoder side ([DeflateSpec.dec_blk],
    [EmitSym.emit_decode_resolves]) speaks [Huff.lz_sym] and [Huff.resolve_lz].
    The two resolutions implement the same overlapping LZ77 copy in different
    shapes: [Trees.copy_n] grows the history one byte at a time and re-indexes
    into the GROWN list, [Huff.lz_copy] maps [i mod dist] over the ORIGINAL
    history.  This file proves they agree and gives the token map, so a [cRes]
    fact from the walk is consumable by [emit_decode_resolves] verbatim.

    DIRECTION: one way (resolve -> resolve_lz).  The consumer
    ([emit_decode_resolves]) PREMISES [resolve_lz body acc = Some out]; the walk
    SUPPLIES [resolve acc toks = Some out].  Nobody consumes the converse, so it
    is not stated (a lemma without a consumer is a guess — DeclIface register
    rule). *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Huff DeflateSpec Trees.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** 1. The token map

    [TMatch len dist] carries [len] already UNbiased ([sym_toks] adds
    [MIN_MATCH] back at read time), so the map is a plain constructor
    relabelling plus the Z-to-nat crossing; [cb_sym_of] in CbEmit.v builds
    exactly [tok_to_lz] of the token [sym_toks] reads at the same index. *)
Definition tok_to_lz (t : Tok) : lz_sym :=
  match t with
  | TLit b => LzLit b
  | TMatch len dist => LzRef (Z.to_nat len) (Z.to_nat dist)
  end.

(** No token maps to the end marker — the premise [emit_decode_seq] needs
    about every interior symbol. *)
Lemma tok_to_lz_not_end : forall ts,
  Forall (fun s => lz_is_end s = false) (map tok_to_lz ts).
Proof.
  induction ts as [|[b|len dist] ts IH]; cbn [map tok_to_lz];
    constructor; try exact IH; reflexivity.
Qed.

(** ** 2. The copy agreement

    Byte [k] of [lz_copy acc len dist] is [acc] at index
    [length acc - dist + k mod dist] — straight off the definition. *)
Lemma lz_copy_nth : forall acc len dist k,
  (k < len)%nat ->
  nth k (lz_copy acc len dist) 0
  = nth (length acc - dist + k mod dist)%nat acc 0.
Proof.
  intros acc len dist k Hk. unfold lz_copy.
  set (f := fun i => nth (length acc - dist + i mod dist)%nat acc 0%Z).
  assert (Hlen : (k < length (map f (seq 0 len)))%nat)
    by (rewrite length_map, length_seq; exact Hk).
  rewrite (nth_indep _ _ (f 0%nat) Hlen).
  rewrite map_nth. rewrite seq_nth by exact Hk. reflexivity.
Qed.

(** The generalized induction: [copy_n] continued from a history that already
    ends in [j] copied bytes appends the NEXT copied bytes.  The index
    arithmetic case-splits on whether byte [j] of the copy still reads the
    original history ([j] below [dist]) or reads an earlier copied byte
    ([(j - dist) mod dist = j mod dist]). *)
Lemma copy_n_from : forall n out0 d j,
  1 <= d <= zlen out0 ->
  copy_n n d (out0 ++ lz_copy out0 j (Z.to_nat d))
  = out0 ++ lz_copy out0 (j + n) (Z.to_nat d).
Proof.
  induction n as [|n IH]; intros out0 d j Hd.
  - cbn [copy_n]. now rewrite Nat.add_0_r.
  - cbn [copy_n].
    set (dn := Z.to_nat d).
    assert (Hdn1 : (1 <= dn)%nat) by (unfold dn; lia).
    assert (Hdn2 : (dn <= length out0)%nat)
      by (unfold dn, zlen in *; lia).
    assert (Hlc : length (lz_copy out0 j dn) = j) by apply lz_copy_length.
    assert (Hzl : zlen (out0 ++ lz_copy out0 j dn) = zlen out0 + Z.of_nat j)
      by (unfold zlen; rewrite length_app, Hlc; lia).
    assert (Hix : Z.to_nat (zlen (out0 ++ lz_copy out0 j dn) - d)
                  = (length out0 + j - dn)%nat)
      by (rewrite Hzl; unfold zlen, dn; lia).
    assert (Hbyte :
      nth (Z.to_nat (zlen (out0 ++ lz_copy out0 j dn) - d))
          (out0 ++ lz_copy out0 j dn) 0
      = nth (length out0 - dn + j mod dn)%nat out0 0).
    { rewrite Hix.
      destruct (Nat.lt_ge_cases j dn) as [Hjd|Hjd].
      - rewrite app_nth1 by lia.
        rewrite Nat.mod_small by exact Hjd.
        f_equal. lia.
      - rewrite app_nth2 by lia.
        replace (length out0 + j - dn - length out0)%nat with (j - dn)%nat
          by lia.
        rewrite lz_copy_nth by lia.
        f_equal.
        replace j with (j - dn + 1 * dn)%nat at 2 by lia.
        now rewrite Nat.Div0.mod_add. }
    rewrite Hbyte.
    rewrite <- app_assoc.
    rewrite <- lz_copy_S.
    replace (S j) with (j + 1)%nat by lia.
    unfold dn.
    rewrite (IH out0 d (j + 1)%nat Hd).
    do 2 f_equal. lia.
Qed.

(** The agreement, at the shape [resolve_tok] uses. *)
Lemma copy_n_is_lz_copy : forall n d out,
  1 <= d <= zlen out ->
  copy_n n d out = out ++ lz_copy out n (Z.to_nat d).
Proof.
  intros n d out Hd.
  pose proof (copy_n_from n out d 0 Hd) as H.
  unfold lz_copy in H at 1. cbn [seq map] in H.
  rewrite app_nil_r in H.
  cbn [Nat.add] in H. exact H.
Qed.

(** ** 3. The resolution agreement, walk-to-decoder direction *)

Theorem resolve_lz_of_resolve : forall ts acc r,
  cEnc ts ->
  resolve acc ts = Some r ->
  resolve_lz (map tok_to_lz ts) acc = Some r.
Proof.
  induction ts as [|t ts IH]; intros acc r Henc Hres.
  - cbn [resolve] in Hres. injection Hres as <-. reflexivity.
  - inversion Henc as [|t0 ts0 Ht Hts]; subst t0 ts0.
    cbn [resolve] in Hres.
    destruct (resolve_tok acc t) as [out2|] eqn:Htok; [|discriminate].
    destruct t as [b|len dist].
    + cbn [resolve_tok] in Htok. injection Htok as <-.
      cbn [map tok_to_lz resolve_lz].
      cbn [tok_enc] in Ht. rewrite u8_id in Hres by exact Ht.
      now apply IH.
    + cbn [resolve_tok] in Htok.
      destruct ((1 <=? dist) && (dist <=? zlen acc)) eqn:Hg; [|discriminate].
      injection Htok as <-.
      apply andb_true_iff in Hg. destruct Hg as [Hg1 Hg2].
      apply Z.leb_le in Hg1. apply Z.leb_le in Hg2.
      cbn [map tok_to_lz resolve_lz].
      assert (Hgz : ((Z.to_nat dist =? 0)%nat
                     || (length acc <? Z.to_nat dist)%nat) = false).
      { apply orb_false_iff. split.
        - apply Nat.eqb_neq. lia.
        - apply Nat.ltb_ge. unfold zlen in Hg2. lia. }
      rewrite Hgz.
      rewrite copy_n_is_lz_copy in Hres by lia.
      now apply IH.
Qed.

(** ** 4. Value witness — the three shapes (literal run, in-range match,
    overlapping match with len above dist), against both resolvers. *)
Example bridge_control :
  resolve [] [TLit 65; TLit 66; TMatch 4 2; TLit 67]
    = Some [65; 66; 65; 66; 65; 66; 67]
  /\ resolve_lz (map tok_to_lz [TLit 65; TLit 66; TMatch 4 2; TLit 67]) []
    = Some [65; 66; 65; 66; 65; 66; 67].
Proof. vm_compute. split; reflexivity. Qed.

Print Assumptions resolve_lz_of_resolve.
