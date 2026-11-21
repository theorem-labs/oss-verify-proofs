(** * Spec.PngModel.InflateThy — fuel sufficiency for the inflate drivers.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.  Depends only on
    [Spec.PngModel.{Base, ZBitsIn, Inftrees, InflateFast, Inflate}] and
    Stdlib.  Adds no [Definition] that any model function calls: everything
    here is either a proof or a predicate a proof quantifies over.

    WHY THIS FILE EXISTS.  [InflateFast.v] and [Inflate.v] both name it in
    their "elementary facts" preamble as the home for the substantial
    obligations, and layer LT of the round-trip DAG is one of them: eight
    fuelled drivers in the model return [option] (or an equivalent
    sentinel) and the capstone [codec_ed_id] demands [Some pix], so EVERY
    [None] is a live proof obligation.  [InflateFast.v] ships the measure
    ([if_measure]) and the free half of its decrease
    ([if_measure_pos_on_cont], read off the guard); this file ships the
    other half — [if_body] really does write at least one output byte —
    and closes [if_model] against it.

    Source lines cited below are [materials/zlib-1.3.1/inffast.c] and
    [materials/zlib-1.3.1/inflate.c] (in-container under
    [/harness/problem/materials/]).

    REDUCTION DISCIPLINE, inherited from [InflateFast.v] and not optional.
    A literal fuel is never normalised: [cbn [if_dolen]] on [if_dolen 2]
    does not converge in 180 s.  Every unfolding below is either one of
    the tree's [reflexivity]-proved one-level rewrites ([if_iter_S],
    [if_loop_S], [if_dolen_chain_step], ...) or a [cbn] with a restricted
    delta list applied at a fuel of the form [S k] for a VARIABLE [k].
    The two [_unfold_] lemmas this file adds ([if_dodist_unfold_base],
    [if_dolen_unfold_base]) follow the same pattern: they name the
    post-dispatch body with an ordinary [Definition] so that the analysis
    of the body never has to be duplicated across the branches that reach
    it, and each is proved by [reflexivity] after a single [cbn] with the
    fixpoint's own name as the delta list. *)

From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import ZBitsIn.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import InflateFast.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Checksum.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Inflate.
(* 2026-08-19 (Q4): it_model totality for the TABLE-chain arms *)
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtItTotal.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

(** ** Arithmetic scaffolding *)

Lemma u32_range : forall v, 0 <= u32 v < 4294967296.
Proof. intros v; unfold u32; apply Z.mod_pos_bound; lia. Qed.

(** [hold & ((1U << n) - 1)] delivers exactly [n] bits, so it is bounded
    by the mask.  Used to bound a length/distance code's extra bits by the
    width the table entry advertises. *)
Lemma if_low_range :
  forall n s, 0 <= n -> 0 <= if_low n s <= Z.shiftl 1 n - 1.
Proof.
  intros n s Hn. unfold if_low. rewrite Z.shiftl_1_l.
  pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) Hn) as Hp.
  replace (2 ^ n - 1) with (Z.ones n) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound (f_hold s) (2 ^ n) ltac:(lia)).
  rewrite Z.ones_equiv. lia.
Qed.

Lemma land_15_nonneg : forall v, 0 <= Z.land v 15.
Proof. intros v. apply Z.land_nonneg. right; lia. Qed.

(** ** [f_out] is stable under everything that is not a write

    [if_drop] / [if_load1] rebuild the record with [f_out] copied, so each
    of these is [reflexivity]; [if_refill15] and the two [PULLBYTE]
    conditionals need the branch resolved first. *)

Lemma if_drop_out : forall n s, f_out (if_drop n s) = f_out s.
Proof. reflexivity. Qed.

Lemma if_load1_out : forall c s, f_out (if_load1 c s) = f_out s.
Proof. reflexivity. Qed.

Lemma if_refill15_out : forall c s, f_out (if_refill15 c s) = f_out s.
Proof. intros c s. unfold if_refill15. destruct (Z.ltb (f_bits s) 15); reflexivity. Qed.

(** [inffast.c:143-147]: the distance side's double [PULLBYTE]. *)
Lemma if_pull2_out :
  forall c e s,
    f_out (if Z.ltb (f_bits s) e
           then (let sa := if_load1 c s in
                 if Z.ltb (f_bits sa) e then if_load1 c sa else sa)
           else s) = f_out s.
Proof.
  intros c e s. destruct (Z.ltb (f_bits s) e); [|reflexivity].
  cbv zeta. destruct (Z.ltb (f_bits (if_load1 c s)) e); reflexivity.
Qed.

(** [inffast.c:124-127]: the length side's single [PULLBYTE]. *)
Lemma if_pull1_out :
  forall c e s,
    f_out (if Z.ltb (f_bits s) e then if_load1 c s else s) = f_out s.
Proof. intros c e s. destruct (Z.ltb (f_bits s) e); reflexivity. Qed.

(** ** The copy primitives write exactly [len] bytes

    [inffast.c:225-249].  The three shapes ([if_copy3w] the [while (len >
    2)] unroll, [if_copytail] the [len]/[len > 1] remainder, [if_winphase]
    the window-side prologue) each move [f_out] forward by precisely the
    amount they take off [len], which is what makes "a match writes [len]
    bytes" fall out by composition. *)

Lemma if_copy3w_spec :
  forall f c s r len,
    0 <= len -> len < 3 * Z.of_nat f -> len < 4294967296 ->
    exists s' r' l',
      if_copy3w f c s r len = Some (s', r', l')
      /\ f_out s' = f_out s + (len - l')
      /\ 0 <= l' <= 2.
Proof.
  induction f as [|f IH]; intros c s r len H0 Hf H32; [cbn in Hf; lia|].
  cbn [if_copy3w].
  destruct (Z.ltb 2 len) eqn:E.
  - apply Z.ltb_lt in E.
    destruct (if_copyn 3 c s r) as [s1 r1] eqn:E1.
    assert (Hs1 : f_out s1 = f_out s + 3).
    { pose proof (if_copyn_out 3 c s r) as Hc. rewrite E1 in Hc. cbn [fst] in Hc.
      cbn in Hc. lia. }
    rewrite u32_id by lia.
    destruct (IH c s1 r1 (len - 3) ltac:(lia) ltac:(lia) ltac:(lia))
      as [s' [r' [l' [Heq [Hout Hl]]]]].
    exists s', r', l'. split; [exact Heq|]. split; [lia|exact Hl].
  - exists s, r, len.
    split; [reflexivity|]. split; [lia|].
    destruct (Z.ltb 2 len) eqn:E'; [discriminate E|].
    apply Z.ltb_ge in E'. lia.
Qed.

Lemma if_copytail_out :
  forall c s r len, 0 <= len <= 2 -> f_out (if_copytail c s r len) = f_out s + len.
Proof.
  intros c s r len Hl. unfold if_copytail.
  destruct (Z.eqb len 0) eqn:E0.
  { apply Z.eqb_eq in E0. subst len. lia. }
  apply Z.eqb_neq in E0.
  destruct (if_copyn 1 c s r) as [s1 r1] eqn:E1.
  assert (Hs1 : f_out s1 = f_out s + 1).
  { pose proof (if_copyn_out 1 c s r) as Hc. rewrite E1 in Hc. cbn [fst] in Hc.
    cbn in Hc. lia. }
  destruct (Z.ltb 1 len) eqn:E2.
  - apply Z.ltb_lt in E2.
    pose proof (if_copyn_out 1 c s1 r1) as Hc.
    replace (Z.of_nat 1) with 1 in Hc by reflexivity. lia.
  - apply Z.ltb_ge in E2. lia.
Qed.

Lemma if_winphase_out :
  forall c s dist op len s' r' len',
    0 <= op < 4294967296 -> 0 <= f_wnext c -> 0 <= len < 4294967296 ->
    if_winphase c s dist op len = (s', r', len') ->
    f_out s' = f_out s + (len - len') /\ 0 <= len' <= len.
Proof.
  intros c s dist op len s' r' len' Hop Hwn Hlen H.
  unfold if_winphase in H. cbv zeta in H.
  destruct (Z.eqb (f_wnext c) 0) eqn:Ew0.
  - (* :190-197, wnext == 0 *)
    destruct (Z.ltb op len) eqn:Eol.
    + apply Z.ltb_lt in Eol.
      destruct (if_copyn (Z.to_nat op) c s (SrcWin (f_wsize c - op))) as [s1 x] eqn:E1.
      assert (Hs1 : f_out s1 = f_out s + op).
      { pose proof (if_copyn_out (Z.to_nat op) c s (SrcWin (f_wsize c - op))) as Hc.
        rewrite E1 in Hc. cbn [fst] in Hc. rewrite Z2Nat.id in Hc by lia. lia. }
      injection H as H1 H2 H3. subst s' len'.
      rewrite u32_id by lia. lia.
    + apply Z.ltb_ge in Eol.
      injection H as H1 H2 H3. subst s' len'. lia.
  - destruct (Z.ltb (f_wnext c) op) eqn:Ewo.
    + (* :198-214, wrap *)
      apply Z.ltb_lt in Ewo.
      rewrite (u32_id (op - f_wnext c)) in H by lia.
      destruct (Z.ltb (op - f_wnext c) len) eqn:E1l.
      * apply Z.ltb_lt in E1l.
        rewrite (u32_id (len - (op - f_wnext c))) in H by lia.
        destruct (if_copyn (Z.to_nat (op - f_wnext c)) c s
                    (SrcWin (f_wsize c + f_wnext c - op))) as [s1 x] eqn:E1.
        assert (Hs1 : f_out s1 = f_out s + (op - f_wnext c)).
        { pose proof (if_copyn_out (Z.to_nat (op - f_wnext c)) c s
                        (SrcWin (f_wsize c + f_wnext c - op))) as Hc.
          rewrite E1 in Hc. cbn [fst] in Hc. rewrite Z2Nat.id in Hc by lia. lia. }
        destruct (Z.ltb (f_wnext c) (len - (op - f_wnext c))) eqn:E2l.
        -- apply Z.ltb_lt in E2l.
           destruct (if_copyn (Z.to_nat (f_wnext c)) c s1 (SrcWin 0)) as [s2 y] eqn:E2.
           assert (Hs2 : f_out s2 = f_out s1 + f_wnext c).
           { pose proof (if_copyn_out (Z.to_nat (f_wnext c)) c s1 (SrcWin 0)) as Hc.
             rewrite E2 in Hc. cbn [fst] in Hc. rewrite Z2Nat.id in Hc by lia. lia. }
           injection H as H1 H2 H3. subst s' len'.
           rewrite u32_id by lia. lia.
        -- apply Z.ltb_ge in E2l.
           injection H as H1 H2 H3. subst s' len'. lia.
      * apply Z.ltb_ge in E1l.
        injection H as H1 H2 H3. subst s' len'. lia.
    + (* :215-223, contiguous *)
      apply Z.ltb_ge in Ewo.
      destruct (Z.ltb op len) eqn:Eol.
      * apply Z.ltb_lt in Eol.
        destruct (if_copyn (Z.to_nat op) c s (SrcWin (f_wnext c - op))) as [s1 x] eqn:E1.
        assert (Hs1 : f_out s1 = f_out s + op).
        { pose proof (if_copyn_out (Z.to_nat op) c s (SrcWin (f_wnext c - op))) as Hc.
          rewrite E1 in Hc. cbn [fst] in Hc. rewrite Z2Nat.id in Hc by lia. lia. }
        injection H as H1 H2 H3. subst s' len'.
        rewrite u32_id by lia. lia.
      * apply Z.ltb_ge in Eol.
        injection H as H1 H2 H3. subst s' len'. lia.
Qed.

(** [inffast.c:237-249]: the do-while direct copy.  Three bytes go out
    before [len > 2] is tested, so this is where a [len < 3] would
    [u32]-underflow [len - 3] and exhaust [copy_fuel]; [3 <= len] is
    exactly what rules that out. *)
Lemma if_copydirect_ok :
  forall c s r len,
    3 <= len <= 258 ->
    exists s', if_copydirect c s r len = Some s' /\ f_out s' = f_out s + len.
Proof.
  intros c s r len Hlen. unfold if_copydirect.
  destruct (if_copyn 3 c s r) as [s1 r1] eqn:E1.
  assert (Hs1 : f_out s1 = f_out s + 3).
  { pose proof (if_copyn_out 3 c s r) as Hc. rewrite E1 in Hc. cbn [fst] in Hc.
    cbn in Hc. lia. }
  rewrite u32_id by lia.
  destruct (if_copy3w_spec copy_fuel c s1 r1 (len - 3)
              ltac:(lia) ltac:(unfold copy_fuel; cbn [Z.of_nat]; lia) ltac:(lia))
    as [s2 [r2 [l2 [Heq [Hout Hl]]]]].
  rewrite Heq.
  exists (if_copytail c s2 r2 l2). split; [reflexivity|].
  rewrite (if_copytail_out c s2 r2 l2 Hl). lia.
Qed.

(** ** What one trip of the body does to the write cursor

    Two predicates, both indexed by the OUT VALUE rather than by the state,
    so that the [if_drop]/[if_load1] steps between an entry and its
    sub-table entry can be discharged by [rewrite if_drop_out] instead of
    by a conversion the unifier has to guess.

    [body_out_eq o len b]: [b] came out of the [dodist:] label, which
    either writes exactly [len] bytes or [break]s to BAD.  [BodyEob] is
    [False] because [inffast.c:263-266]'s end-of-block [break] is on the
    LENGTH side only, and [BodyFuel] is [False] because it is exactly what
    this file exists to rule out.

    [body_out_lt o b]: [b] came out of the [dolen:] label, which writes at
    least one byte on the fall-through path — one for a literal
    ([inffast.c:114]) and [len >= 3] for a match. *)

Definition body_out_eq (o len : Z) (b : IfBody) : Prop :=
  match b with
  | BodyOk s' => f_out s' = o + len
  | BodyEob _ => False
  | BodyBad _ _ => True
  | BodyFuel => False
  end.

Definition body_out_lt (o : Z) (b : IfBody) : Prop :=
  match b with
  | BodyOk s' => o < f_out s'
  | BodyEob _ => True
  | BodyBad _ _ => True
  | BodyFuel => False
  end.

Lemma body_out_eq_lt :
  forall o len b, 0 < len -> body_out_eq o len b -> body_out_lt o b.
Proof.
  intros o len b Hl H. destruct b as [s'|s'|s' m|]; cbn [body_out_eq] in H;
    cbn [body_out_lt]; try exact I; [lia | contradiction].
Qed.

(** ** The caller obligation the length table carries

    [inftrees.c:60]'s [lbase] runs [3 .. 258] and [lext] gives each entry
    the extra-bit width that keeps [base + (2^extra - 1)] at or below 258
    (the extreme is [lbase[27] = 227] with [lext[27] & 15 = 5], i.e.
    [227 + 31 = 258]).  The two slots whose [lbase] is 0 carry
    [lext = 77] and [lext = 202], both of which have bit 6 set, so
    [inffast.c:142]'s [op & 16] test never selects them as a length base.

    THIS IS THE FACT [InflateFast.v]'s header already CLAIMED under the
    name [if_wf] — "[if_wf]'s [len >= 3]" at [:250] and "every length code
    carries [len >= 3]" at [:34] — while [if_wf]'s conjuncts said nothing
    about [c_val].  Recommended: fold [lcode_len_bounded (if_ctx a)] into
    [if_wf] as a fifteenth conjunct, exactly as the 2026-08-16 pass folded
    in [lcode_two_level] / [dcode_two_level] for the same reason.  It is
    kept separate here so that this file adds no edit to [InflateFast.v].

    It is load-bearing twice over: [3 <= len] is what stops
    [if_copydirect]'s [u32 (len - 3)] from underflowing (which would
    exhaust [copy_fuel] and hand back [BodyFuel]), and [len <= 258] is
    what makes [copy_fuel = 87] enough. *)

(* [lc_len_ok] / [lcode_len_bounded] were folded into [InflateFast.if_wf]
   on 2026-08-16 and are imported from there; they used to be defined
   here. *)

(** ** [inffast.c:142-249]: the distance-base body, named

    Naming the post-dispatch body keeps the copy analysis in ONE place
    instead of once per branch that reaches it, and keeps every unfolding
    a [reflexivity]. *)

Definition dodist_pull (c : IfCtx) (e : Z) (s1 : IfSt) : IfSt :=
  if Z.ltb (f_bits s1) e
  then (let sa := if_load1 c s1 in
        if Z.ltb (f_bits sa) e then if_load1 c sa else sa)
  else s1.

Lemma dodist_pull_out : forall c e s, f_out (dodist_pull c e s) = f_out s.
Proof. intros c e s. unfold dodist_pull. apply if_pull2_out. Qed.

Definition dodist_body (c : IfCtx) (len : Z) (s3 : IfSt) (dist : Z) : IfBody :=
  let od := u32 (f_out s3 - f_beg c) in
  if Z.ltb od dist then
    let ow := u32 (dist - od) in
    if Z.ltb (f_whave c) ow && negb (Z.eqb (f_sane c) 0) then
      BodyBad s3 MSG_DIST_FAR
    else
      let '(s4, r4, len4) := if_winphase c s3 dist ow len in
      match if_copy3w copy_fuel c s4 r4 len4 with
      | None => BodyFuel
      | Some (s5, r5, l5) => BodyOk (if_copytail c s5 r5 l5)
      end
  else
    match if_copydirect c s3 (SrcOut (f_out s3 - dist)) len with
    | None => BodyFuel
    | Some s5 => BodyOk s5
    end.

Lemma dodist_body_ok :
  forall c len s3 dist,
    0 <= f_wnext c -> 3 <= len <= 258 ->
    body_out_eq (f_out s3) len (dodist_body c len s3 dist).
Proof.
  intros c len s3 dist Hwn Hlen. unfold dodist_body. cbv zeta.
  destruct (Z.ltb (u32 (f_out s3 - f_beg c)) dist) eqn:Eod.
  - destruct (Z.ltb (f_whave c) (u32 (dist - u32 (f_out s3 - f_beg c)))
              && negb (Z.eqb (f_sane c) 0)) eqn:Ebad; [exact I|].
    destruct (if_winphase c s3 dist (u32 (dist - u32 (f_out s3 - f_beg c))) len)
      as [[s4 r4] len4] eqn:EW.
    destruct (if_winphase_out c s3 dist
                (u32 (dist - u32 (f_out s3 - f_beg c))) len s4 r4 len4
                (u32_range _) Hwn ltac:(lia) EW) as [Hout4 Hlen4].
    destruct (if_copy3w_spec copy_fuel c s4 r4 len4 ltac:(lia)
                ltac:(unfold copy_fuel; cbn [Z.of_nat]; lia) ltac:(lia))
      as [s5 [r5 [l5 [Heq [Hout5 Hl5]]]]].
    rewrite Heq. cbn [body_out_eq].
    rewrite (if_copytail_out c s5 r5 l5 Hl5). lia.
  - destruct (if_copydirect_ok c s3 (SrcOut (f_out s3 - dist)) len Hlen)
      as [s5 [Heq Hout5]].
    rewrite Heq. cbn [body_out_eq]. exact Hout5.
Qed.

Lemma if_dodist_unfold_base :
  forall k c len s h,
    Z.eqb (Z.land (c_op h) 16) 0 = false ->
    if_dodist (S k) c len s h
    = dodist_body c len
        (if_drop (Z.land (c_op h) 15)
           (dodist_pull c (Z.land (c_op h) 15) (if_drop (c_bits h) s)))
        (c_val h + if_low (Z.land (c_op h) 15)
           (dodist_pull c (Z.land (c_op h) 15) (if_drop (c_bits h) s))).
Proof. intros k c len s h H. cbn [if_dodist]. rewrite H. reflexivity. Qed.

(** A distance entry that does not chain is decided at this level. *)
Lemma if_dodist_nochain_ok :
  forall k c len s h,
    dc_chains (c_op h) = false ->
    0 <= f_wnext c -> 3 <= len <= 258 ->
    body_out_eq (f_out s) len (if_dodist (S k) c len s h).
Proof.
  intros k c len s h Hnc Hwn Hlen.
  destruct (Z.eqb (Z.land (c_op h) 16) 0) eqn:E16.
  - unfold dc_chains in Hnc. rewrite E16 in Hnc. cbn [andb] in Hnc.
    cbn [if_dodist]. rewrite E16, Hnc. cbn [negb body_out_eq]. exact I.
  - rewrite (if_dodist_unfold_base k c len s h E16).
    assert (Hs3 : f_out (if_drop (Z.land (c_op h) 15)
                    (dodist_pull c (Z.land (c_op h) 15) (if_drop (c_bits h) s)))
                  = f_out s).
    { rewrite if_drop_out, dodist_pull_out, if_drop_out. reflexivity. }
    rewrite <- Hs3. apply dodist_body_ok; assumption.
Qed.

(** …and [inftrees.h:33-47] says a chain is at most two deep, so two
    levels of [tbl_fuel] are all that is ever consumed. *)
Lemma if_dodist_two_ok :
  forall k c len s v,
    dcode_two_level c ->
    (dc_chains (c_op (f_dcode c v)) = true ->
       exists x, v = Z.land x (f_dmask c)) ->
    0 <= f_wnext c -> 3 <= len <= 258 ->
    body_out_eq (f_out s) len (if_dodist (S (S k)) c len s (f_dcode c v)).
Proof.
  intros k c len s v Hdt Hwv Hwn Hlen.
  destruct (dc_chains (c_op (f_dcode c v))) eqn:Hch.
  - rewrite (if_dodist_chain_step (S k) c len s _ Hch).
    destruct (Hwv eq_refl) as (xw & Hxw).
    pose proof (Hdt v xw (if_drop (c_bits (f_dcode c v)) s) Hxw Hch) as Hnext.
    pose proof (if_dodist_nochain_ok k c len
                  (if_drop (c_bits (f_dcode c v)) s) _ Hnext Hwn Hlen) as HH.
    rewrite if_drop_out in HH. exact HH.
  - exact (if_dodist_nochain_ok (S k) c len s _ Hch Hwn Hlen).
Qed.

(** ** [inffast.c:122-135]: the length-base body, named *)

Definition dolen_pull (c : IfCtx) (e : Z) (s1 : IfSt) : IfSt :=
  if Z.ltb (f_bits s1) e then if_load1 c s1 else s1.

Lemma dolen_pull_out : forall c e s, f_out (dolen_pull c e s) = f_out s.
Proof. intros c e s. unfold dolen_pull. apply if_pull1_out. Qed.

Definition dolen_base (c : IfCtx) (h : Code) (s1 : IfSt) : IfBody :=
  let e := Z.land (c_op h) 15 in
  let '(len, s2) :=
    if Z.eqb e 0 then (c_val h, s1)
    else (c_val h + if_low e (dolen_pull c e s1), if_drop e (dolen_pull c e s1)) in
  let s3 := if_refill15 c s2 in
  if_dodist tbl_fuel c len s3 (f_dcode c (Z.land (f_hold s3) (f_dmask c))).

Lemma if_dolen_unfold_base :
  forall k c s h,
    Z.eqb (c_op h) 0 = false ->
    Z.eqb (Z.land (c_op h) 16) 0 = false ->
    if_dolen (S k) c s h = dolen_base c h (if_drop (c_bits h) s).
Proof. intros k c s h E0 E16. cbn [if_dolen]. rewrite E0, E16. reflexivity. Qed.

Lemma dolen_base_ok :
  forall c h s1,
    0 <= f_wnext c -> dcode_two_level c -> lc_len_ok h ->
    Z.eqb (Z.land (c_op h) 16) 0 = false ->
    body_out_lt (f_out s1) (dolen_base c h s1).
Proof.
  intros c h s1 Hwn Hdt Hlc E16.
  apply Z.eqb_neq in E16.
  destruct (Hlc E16) as [Hv3 Hv258].
  pose proof (land_15_nonneg (c_op h)) as He0.
  unfold dolen_base. cbv zeta.
  (* the two shapes of [(len, s2)]; in both, [f_out s2 = f_out s1] and
     [3 <= len <= 258]. *)
  assert (Hpow : 1 <= Z.shiftl 1 (Z.land (c_op h) 15)).
  { rewrite Z.shiftl_1_l. apply Z.pow_le_mono_r with (a := 2) (b := 0) (c := Z.land (c_op h) 15);
      [lia | exact He0]. }
  destruct (Z.eqb (Z.land (c_op h) 15) 0) eqn:Ee.
  - apply (body_out_eq_lt _ (c_val h)); [lia|].
    rewrite <- (if_refill15_out c s1).
    apply if_dodist_two_ok with (k := 14%nat);
      [exact Hdt | intros _; eexists; reflexivity | exact Hwn |].
    apply Z.eqb_eq in Ee. rewrite Ee in Hv258. cbn in Hv258. lia.
  - pose proof (if_low_range (Z.land (c_op h) 15)
                  (dolen_pull c (Z.land (c_op h) 15) s1) He0) as Hlow.
    apply (body_out_eq_lt _ (c_val h
             + if_low (Z.land (c_op h) 15) (dolen_pull c (Z.land (c_op h) 15) s1)));
      [lia|].
    assert (Hs3 : f_out (if_refill15 c (if_drop (Z.land (c_op h) 15)
                           (dolen_pull c (Z.land (c_op h) 15) s1))) = f_out s1).
    { rewrite if_refill15_out, if_drop_out, dolen_pull_out. reflexivity. }
    rewrite <- Hs3.
    apply if_dodist_two_ok with (k := 14%nat);
      [exact Hdt | intros _; eexists; reflexivity | exact Hwn | lia].
Qed.

Lemma if_dolen_nochain_ok :
  forall k c s h,
    lc_chains (c_op h) = false ->
    0 <= f_wnext c -> dcode_two_level c -> lc_len_ok h ->
    body_out_lt (f_out s) (if_dolen (S k) c s h).
Proof.
  intros k c s h Hnc Hwn Hdt Hlc.
  destruct (Z.eqb (c_op h) 0) eqn:E0.
  - (* :117-121 literal: exactly one byte *)
    cbn [if_dolen]. rewrite E0. cbn [body_out_lt if_put if_drop f_out]. lia.
  - destruct (Z.eqb (Z.land (c_op h) 16) 0) eqn:E16.
    + unfold lc_chains in Hnc. rewrite E0, E16 in Hnc. cbn [negb andb] in Hnc.
      cbn [if_dolen]. rewrite E0, E16, Hnc. cbn [negb].
      destruct (Z.eqb (Z.land (c_op h) 32) 0); cbn [negb body_out_lt]; exact I.
    + rewrite (if_dolen_unfold_base k c s h E0 E16).
      pose proof (dolen_base_ok c h (if_drop (c_bits h) s) Hwn Hdt Hlc E16) as HH.
      rewrite if_drop_out in HH. exact HH.
Qed.

(** RELATIVISED 2026-08-19 with the [lcode_len_bounded] repair
    (InflateFast.v; distilled/zlib-port-repairs.md §2): [v] is no longer
    arbitrary — the bound premise [0 <= v < n] is what the repaired
    predicate can honestly supply, and the two [lcode_index_range]
    clauses were read off THIS proof's two application sites.  The only
    consumer ([if_body_ok] below) instantiates [v] at the masked root
    index, which clause 1 bounds. *)
Lemma if_dolen_two_ok :
  forall k c s v n,
    lcode_two_level c -> dcode_two_level c ->
    (lc_chains (c_op (f_lcode c v)) = true ->
       exists x, v = Z.land x (f_lmask c)) ->
    lcode_len_bounded_upto c n -> lcode_index_range n c ->
    0 <= v < n ->
    0 <= f_wnext c ->
    body_out_lt (f_out s) (if_dolen (S (S k)) c s (f_lcode c v)).
Proof.
  intros k c s v n Hlt Hdt Hwv Hup [Hroot Hchain] Hv Hwn.
  destruct (lc_chains (c_op (f_lcode c v))) eqn:Hch.
  - rewrite (if_dolen_chain_step (S k) c s _ Hch).
    destruct (Hwv eq_refl) as (xw & Hxw).
    pose proof (Hlt v xw (if_drop (c_bits (f_lcode c v)) s) Hxw Hch) as Hnext.
    pose proof (if_dolen_nochain_ok k c
                  (if_drop (c_bits (f_lcode c v)) s) _ Hnext Hwn Hdt
                  (Hup _ (Hchain v (if_drop (c_bits (f_lcode c v)) s)
                            Hv Hch))) as HH.
    rewrite if_drop_out in HH. exact HH.
  - exact (if_dolen_nochain_ok (S k) c s _ Hch Hwn Hdt (Hup v Hv)).
Qed.

(** ** THE MISSING HALF OF [if_measure]

    [InflateFast.v] fixes the measure [if_measure c s = f_end c - f_out s]
    and proves the free half ([if_measure_pos_on_cont], read off the
    guard), leaving "[if_body] writes at least one byte" explicitly
    unclaimed.  Here it is. *)

Definition if_ctx_wf (c : IfCtx) : Prop :=
  0 <= f_wnext c
  /\ lcode_two_level c
  /\ dcode_two_level c
  /\ lcode_len_bounded c.

Lemma if_wf_ctx_wf :
  forall a, if_wf a -> lcode_len_bounded (if_ctx a) -> if_ctx_wf (if_ctx a).
Proof.
  intros a H Hlb. unfold if_wf in H. unfold if_ctx_wf.
  split; [cbn [f_wnext if_ctx]; lia|].
  split; [tauto|]. split; [tauto|]. exact Hlb.
Qed.

Lemma if_body_ok :
  forall c s, if_ctx_wf c -> body_out_lt (f_out s) (if_body c s).
Proof.
  intros c s [Hwn [Hlt [Hdt Hlb]]]. unfold if_body.
  destruct Hlb as [n [Hup Hrange]].
  pose proof (if_dolen_two_ok 14 c (if_refill15 c s)
                (Z.land (f_hold (if_refill15 c s)) (f_lmask c)) n
                Hlt Hdt ltac:(intros _; eexists; reflexivity) Hup Hrange
                (proj1 Hrange (if_refill15 c s)) Hwn) as HH.
  rewrite if_refill15_out in HH. exact HH.
Qed.

(** The headline statement layer LT was asked for.  [inffast.c:114] writes
    one byte for a literal and [:225-249] writes [len >= 3] for a match, so
    [f_out] strictly increases on every trip that falls through to the
    bottom of the body — which is what makes [f_end - f_out] a measure. *)
Theorem if_body_out_lt :
  forall c s s', if_ctx_wf c -> if_body c s = BodyOk s' -> f_out s < f_out s'.
Proof.
  intros c s s' Hwf H.
  pose proof (if_body_ok c s Hwf) as HH. rewrite H in HH. exact HH.
Qed.

Theorem if_body_not_fuel :
  forall c s, if_ctx_wf c -> if_body c s <> BodyFuel.
Proof.
  intros c s Hwf H.
  pose proof (if_body_ok c s Hwf) as HH. rewrite H in HH. exact HH.
Qed.

(** ** The loop, and [if_model] never declining *)

Lemma if_step_ok_abs :
  forall c (b : IfBody) o,
    body_out_lt o b ->
    match (match b with
           | BodyOk s1 => if if_guard c s1 then IfCont s1 else IfStop s1
           | BodyEob s1 => IfEob s1
           | BodyBad s1 m => IfBad s1 m
           | BodyFuel => IfFuel
           end) with
    | IfCont s' => o < f_out s' /\ f_out s' < f_end c
    | IfFuel => False
    | _ => True
    end.
Proof.
  intros c b o H. destruct b as [s1|s1|s1 m|]; cbn [body_out_lt] in H.
  - destruct (if_guard c s1) eqn:Hg; [|exact I].
    apply if_guard_true in Hg. split; [exact H | apply Hg].
  - exact I.
  - exact I.
  - contradiction.
Qed.

Lemma if_step_ok :
  forall c s, if_ctx_wf c ->
    match if_step c s with
    | IfCont s' => f_out s < f_out s' /\ f_out s' < f_end c
    | IfFuel => False
    | _ => True
    end.
Proof.
  intros c s Hwf. rewrite if_step_unfold.
  exact (if_step_ok_abs c (if_body c s) (f_out s) (if_body_ok c s Hwf)).
Qed.

Definition loop_done (r : IfStep) : Prop :=
  match r with IfCont _ => False | IfFuel => False | _ => True end.

Lemma if_loop_total :
  forall n c s, if_ctx_wf c -> f_end c - f_out s <= Z.of_nat n ->
    exists r, if_loop (S n) c s = Some r /\ loop_done r.
Proof.
  induction n as [|n IH]; intros c s Hwf Hb; rewrite if_loop_S;
    pose proof (if_step_ok c s Hwf) as HS;
    destruct (if_step c s) as [s1|s1|s1|s1 m|] eqn:E.
  - destruct HS as [H1 H2]. cbn [Z.of_nat] in Hb. lia.
  - exists (IfStop s1). split; [reflexivity | exact I].
  - exists (IfEob s1). split; [reflexivity | exact I].
  - exists (IfBad s1 m). split; [reflexivity | exact I].
  - contradiction.
  - destruct HS as [H1 H2]. apply IH; [exact Hwf | lia].
  - exists (IfStop s1). split; [reflexivity | exact I].
  - exists (IfEob s1). split; [reflexivity | exact I].
  - exists (IfBad s1 m). split; [reflexivity | exact I].
  - contradiction.
Qed.

(** [if_model] picks [S (f_end - f_out)] trips ([InflateFast.v:545-556]),
    which the measure above shows is enough — so the model never declines
    on a well-formed call. *)
Theorem if_model_total :
  forall a, if_wf a -> lcode_len_bounded (if_ctx a) -> exists y, if_model a = Some y.
Proof.
  intros a Hwf Hlb.
  pose proof (if_wf_ctx_wf a Hwf Hlb) as Hc.
  unfold if_model.
  destruct (if_loop_total (Z.to_nat (f_end (if_ctx a) - f_out (if_st0 a)))
              (if_ctx a) (if_st0 a) Hc ltac:(lia)) as [r [Heq Hd]].
  rewrite Heq.
  destruct r as [s1|s1|s1|s1 m|]; cbn [loop_done] in Hd; try contradiction;
    eexists; reflexivity.
Qed.

(** * The mode machine — [inflate.c:585-1241]

    [Inflate.v] ships the arithmetic half of the lexicographic measure
    ([inf_budget], [inf_rank], [m_val_range], [inf_fuel_dominates_rank])
    and leaves the per-arm half — [inf_step c q = InfCont q' ->
    inf_rank q' < inf_rank q] — explicitly unclaimed.  This section
    supplies the accounting the per-arm half is proved with, and reports
    one finding that changes the statement itself: as shipped, [inf_rank]
    is NOT a measure, and the counterexample is reachable. *)

(** ** Budget accounting

    [inf_budget q = 8 * br_have + br_bits + o_left].  [PULLBYTE] moves a
    byte from [have] into [bits] ([inflate.c:473-480]) and so leaves
    [8 * have + bits] EXACTLY invariant; [DROPBITS n] takes [n] off;
    [*put++] takes one off [left].  Every arm's effect on the budget is a
    composition of those three. *)

Lemma inf_nb_go_bud :
  forall f n b b',
    inf_nb_go f n b = NBOk b' ->
    8 * br_have b' + br_bits b' = 8 * br_have b + br_bits b
    /\ br_bits b <= br_bits b'
    /\ (0 <= br_have b -> 0 <= br_have b').
Proof.
  induction f as [|f IH]; intros n b b' H; cbn [inf_nb_go] in H.
  - destruct (Z.ltb (br_bits b) n); [discriminate|].
    injection H as H; subst b'. repeat split; lia.
  - destruct (Z.ltb (br_bits b) n).
    + destruct (br_pullbyte b) as [b1|] eqn:Hp; [|discriminate].
      pose proof Hp as Hp'. apply br_pullbyte_step in Hp' as (H1 & _ & H3 & _).
      assert (Hh1 : 0 <= br_have b -> 0 <= br_have b1).
      { intros Hb. unfold br_pullbyte in Hp.
        destruct (Z.eqb (br_have b) 0) eqn:E; [discriminate|].
        apply Z.eqb_neq in E. lia. }
      apply IH in H as (G1 & G2 & G3). repeat split; lia.
    + injection H as H; subst b'. repeat split; lia.
Qed.

Lemma inf_nb_bud :
  forall n b b',
    inf_nb n b = NBOk b' ->
    8 * br_have b' + br_bits b' = 8 * br_have b + br_bits b
    /\ br_bits b <= br_bits b'
    /\ (0 <= br_have b -> 0 <= br_have b').
Proof. intros n b b'; apply inf_nb_go_bud. Qed.

(** [inflate.c:1036-1047] / [:1085-1096]: the fetch loops only [PULLBYTE],
    so they leave the bit budget alone too. *)
Lemma inf_fetch_go_bud :
  forall f t nb b h b',
    inf_fetch_go f t nb b = FetchOk h b' ->
    8 * br_have b' + br_bits b' = 8 * br_have b + br_bits b
    /\ (0 <= br_have b -> 0 <= br_have b').
Proof.
  induction f as [|f IH]; intros t nb b h b' H; cbn [inf_fetch_go] in H;
    [discriminate|].
  destruct (Z.leb (c_bits (t (br_bits_of nb b))) (br_bits b)) eqn:E.
  - injection H as H1 H2; subst b'. split; [lia|auto].
  - destruct (br_pullbyte b) as [b1|] eqn:Hp; [|discriminate].
    pose proof Hp as Hp'. apply br_pullbyte_step in Hp' as (H1 & _ & H3 & _).
    assert (Hh1 : 0 <= br_have b -> 0 <= br_have b1).
    { intros Hb. unfold br_pullbyte in Hp.
      destruct (Z.eqb (br_have b) 0) eqn:E0; [discriminate|].
      apply Z.eqb_neq in E0. lia. }
    apply IH in H as (G1 & G2). split; [lia | auto].
Qed.

Lemma inf_fetch_bud :
  forall t nb b h b',
    inf_fetch t nb b = FetchOk h b' ->
    8 * br_have b' + br_bits b' = 8 * br_have b + br_bits b
    /\ (0 <= br_have b -> 0 <= br_have b').
Proof. intros t nb b h b'; apply inf_fetch_go_bud. Qed.

Lemma inf_fetch2_go_bud :
  forall f t lst b h b',
    inf_fetch2_go f t lst b = FetchOk h b' ->
    8 * br_have b' + br_bits b' = 8 * br_have b + br_bits b
    /\ (0 <= br_have b -> 0 <= br_have b').
Proof.
  induction f as [|f IH]; intros t lst b h b' H; cbn [inf_fetch2_go] in H;
    [discriminate|].
  destruct (Z.leb (c_bits lst
              + c_bits (t (c_val lst
                  + Z.shiftr (br_bits_of (c_bits lst + c_op lst) b) (c_bits lst))))
              (br_bits b)) eqn:E.
  - injection H as H1 H2; subst b'. split; [lia|auto].
  - destruct (br_pullbyte b) as [b1|] eqn:Hp; [|discriminate].
    pose proof Hp as Hp'. apply br_pullbyte_step in Hp' as (H1 & _ & H3 & _).
    assert (Hh1 : 0 <= br_have b -> 0 <= br_have b1).
    { intros Hb. unfold br_pullbyte in Hp.
      destruct (Z.eqb (br_have b) 0) eqn:E0; [discriminate|].
      apply Z.eqb_neq in E0. lia. }
    apply IH in H as (G1 & G2). split; [lia | auto].
Qed.

Lemma inf_fetch2_bud :
  forall t lst b h b',
    inf_fetch2 t lst b = FetchOk h b' ->
    8 * br_have b' + br_bits b' = 8 * br_have b + br_bits b
    /\ (0 <= br_have b -> 0 <= br_have b').
Proof. intros t lst b h b'; apply inf_fetch2_go_bud. Qed.

(** MATCH's byte loop takes exactly [n] off [left] ([inflate.c:1174-1176]). *)
Lemma ob_copyn_left_eq :
  forall n win o r, o_left (ob_copyn n win o r) = o_left o - Z.of_nat n.
Proof.
  induction n as [|n IH]; intros win o r; cbn [ob_copyn]; [cbn; lia|].
  rewrite IH. cbn [ob_write o_left]. lia.
Qed.

(** ** THE FINDING: [inf_rank] as shipped is not a measure

    [inflate.c:875-887] [case COPY] ends
<<
        Tracev((stderr, "inflate:       stored end\n"));
        state->mode = TYPE;
        break;
>>
    when [state->length] is already 0 — the trip after an exactly-filled
    stored-block copy, and the whole body of an EMPTY stored block.  That
    trip touches neither [avail_in]/[bits] nor [left], so [inf_budget] is
    unchanged, and it moves the mode from COPY ([m_val] 16195) DOWN to
    TYPE ([m_val] 16191).  [inf_rank] therefore strictly INCREASES across
    a reachable [InfCont], which is the exact negation of the per-arm
    obligation [Inflate.v] states.

    The file header's claim — "for the epsilon-transitions ... the mode
    rank [m_val] orders the acyclic chains" — is right in spirit and wrong
    in this one place: the C enum's numeric order is not a topological
    order of the epsilon edges, because [COPY -> TYPE] runs backwards
    along it.  [inf_mrank] below is the minimal repair. *)

Lemma inf_COPY_rank_increases :
  forall c q,
    q_mode q = M_COPY -> u_length (s_cur (q_st q)) = 0 -> 0 <= inf_budget q ->
    exists q', inf_step c q = InfCont q' /\ (inf_rank q < inf_rank q')%nat.
Proof.
  intros c q Hm Hl Hb.
  exists (qmode q M_TYPE).
  assert (Hstep : inf_step c q = inf_COPY q)
    by (unfold inf_step; rewrite Hm; reflexivity).
  split.
  - rewrite Hstep. unfold inf_COPY. rewrite Hl. reflexivity.
  - unfold inf_rank.
    assert (Hb' : inf_budget (qmode q M_TYPE) = inf_budget q) by reflexivity.
    assert (Hm' : q_mode (qmode q M_TYPE) = M_TYPE) by reflexivity.
    rewrite Hb', Hm', Hm. cbn [m_val]. lia.
Qed.

(** …and the hypotheses are jointly satisfiable, so the refutation is not
    vacuous.  [state_copy0] is an [inflate_state] in mode COPY with
    [length = 0]; every other field is irrelevant to the step taken. *)
Definition state_copy0 : IState :=
  {| s_hdr := {| h_mode := M_COPY; h_last := 0; h_wrap := 5; h_havedict := 0;
                 h_flags := 0; h_dmax := 32768; h_check := 1; h_total := 0;
                 h_head := 0 |};
     s_win := {| w_wbits := 15; w_wsize := 0; w_whave := 0; w_wnext := 0;
                 w_alloc := false; w_win := zzero |};
     s_cur := {| u_length := 0; u_offset := 0; u_extra := 0; u_back := 0;
                 u_was := 0 |};
     s_tab := {| t_lencode := TRcodes 0; t_distcode := TRcodes 0;
                 t_lenbits := 9; t_distbits := 6; t_next := 0;
                 t_codes := tnone; t_sane := 1 |};
     s_bld := {| b_ncode := 0; b_nlen := 0; b_ndist := 0; b_have := 0;
                 b_lens := zzero; b_work := zzero |};
     s_hold := 0; s_bits := 0 |}.

Definition q_copy0 : InfSt :=
  {| q_st := state_copy0;
     q_z  := {| z_tin := 0; z_tout := 0; z_adler := 1; z_dtype := 0;
                z_msg := MSG_NONE |};
     q_br := {| br_in := zzero; br_have := 0; br_next := 0;
                br_hold := 0; br_bits := 0 |};
     q_ob := {| o_buf := zzero; o_put := 0; o_left := 0 |};
     q_in := 0; q_out := 0; q_ret := Z_OK |}.

Theorem inf_rank_is_not_a_measure :
  exists c q q', inf_step c q = InfCont q' /\ (inf_rank q < inf_rank q')%nat.
Proof.
  destruct (inf_COPY_rank_increases
              {| n_flush := Z_NO_FLUSH; n_walloc := true; n_wfresh := zzero |}
              q_copy0 eq_refl eq_refl ltac:(cbn; lia)) as [q' [H1 H2]].
  exists {| n_flush := Z_NO_FLUSH; n_walloc := true; n_wfresh := zzero |}.
  exists q_copy0, q'. split; assumption.
Qed.

(** ** The repaired mode rank

    [inf_mrank] is [m_val] with COPY_ and COPY moved BELOW TYPE and
    HEAD..STORED shifted up by two to fill the hole.  It is a permutation
    of the same interval [16180 .. 16211], so [Inflate.v]'s arithmetic
    half ([inf_fuel_dominates_rank], whose only input is that interval)
    transfers unchanged and the 33 in [inf_fuel] still pays for a whole
    chain of mode steps.

    WHY THIS PERMUTATION AND NOT ANOTHER.  The constraint is that every
    epsilon transition — every [break] that changes neither
    [8*avail_in + bits] nor [left] — must raise the rank.  Enumerating
    them from the arms: COPY_/COPY -> TYPE ([:884-886], the only backwards
    one under [m_val]), TYPEDO -> CHECK ([:829-833], whose [BYTEBITS] can
    drop zero bits), DICT -> TYPE, and the fifteen [mode = BAD] sites.
    Nothing epsilon-ENTERS COPY_ or COPY: STORED reaches COPY_ only after
    a [NEEDBITS(32)] + [INITBITS] that spends at least 32 bits, and
    COPY -> COPY spends at least one output byte.  So COPY_ and COPY may
    be sunk to the bottom, and sinking them is the minimal repair. *)

Definition inf_mrank (m : Mode) : Z :=
  match m with
  | M_COPY_ => 16180 | M_COPY    => 16181
  | M_HEAD  => 16182 | M_FLAGS   => 16183 | M_TIME     => 16184
  | M_OS    => 16185 | M_EXLEN   => 16186 | M_EXTRA    => 16187
  | M_NAME  => 16188 | M_COMMENT => 16189 | M_HCRC     => 16190
  | M_DICTID=> 16191 | M_DICT    => 16192
  | M_TYPE  => 16193 | M_TYPEDO  => 16194 | M_STORED   => 16195
  | M_TABLE => 16196 | M_LENLENS => 16197 | M_CODELENS => 16198
  | M_LEN_  => 16199 | M_LEN     => 16200 | M_LENEXT   => 16201
  | M_DIST  => 16202 | M_DISTEXT => 16203 | M_MATCH    => 16204
  | M_LIT   => 16205 | M_CHECK   => 16206 | M_LENGTH   => 16207
  | M_DONE  => 16208 | M_BAD     => 16209 | M_MEM      => 16210
  | M_SYNC  => 16211
  end.

Lemma inf_mrank_range : forall m, 16180 <= inf_mrank m <= 16211.
Proof. intros m; destruct m; cbn [inf_mrank]; lia. Qed.

Definition inf_rank2 (q : InfSt) : nat :=
  Z.to_nat (33 * inf_budget q + (16212 - inf_mrank (q_mode q))).

Lemma inf_fuel_dominates_rank2 :
  forall q, 0 <= inf_budget q -> (inf_rank2 q < inf_fuel q)%nat.
Proof.
  intros q Hb. unfold inf_rank2, inf_fuel.
  pose proof (inf_mrank_range (q_mode q)) as Hm.
  assert (Hq : inf_budget q
               = 8 * br_have (q_br q) + br_bits (q_br q) + o_left (q_ob q))
    by reflexivity.
  lia.
Qed.

Lemma rank2_lt :
  forall q q',
    0 <= inf_budget q ->
    33 * inf_budget q' + (16212 - inf_mrank (q_mode q'))
      < 33 * inf_budget q + (16212 - inf_mrank (q_mode q)) ->
    (inf_rank2 q' < inf_rank2 q)%nat.
Proof.
  intros q q' Hb H. unfold inf_rank2.
  pose proof (inf_mrank_range (q_mode q)) as Hm. lia.
Qed.

Lemma rank2_le :
  forall q q',
    33 * inf_budget q' + (16212 - inf_mrank (q_mode q'))
      <= 33 * inf_budget q + (16212 - inf_mrank (q_mode q)) ->
    (inf_rank2 q' <= inf_rank2 q)%nat.
Proof. intros q q' H. unfold inf_rank2. lia. Qed.

(** ** The per-arm obligation

    [q_pos] is the sign invariant the budget needs ([Z.to_nat] clamps, so
    a negative budget would silently break the order); [arm_ok] is the
    obligation itself, stated per ARM function rather than per [inf_step]
    so that a [case] that falls through to the next one can compose with
    it — which is exactly how the C is written and how [Inflate.v]
    transcribes it. *)

Definition q_pos (q : InfSt) : Prop :=
  0 <= br_have (q_br q) /\ 0 <= br_bits (q_br q) /\ 0 <= o_left (q_ob q).

Lemma q_pos_bud : forall q, q_pos q -> 0 <= inf_budget q.
Proof. intros q (H1 & H2 & H3). unfold inf_budget. lia. Qed.

Definition arm_ok (q : InfSt) (r : InfStep) : Prop :=
  match r with
  | InfCont q'  => q_pos q' /\ (inf_rank2 q' < inf_rank2 q)%nat
  | InfLeave _  => True
  | InfRet _ _  => True
  | InfDead _   => False
  | InfFuel     => False
  end.

Lemma arm_ok_mono :
  forall q1 q2 r, (inf_rank2 q1 <= inf_rank2 q2)%nat -> arm_ok q1 r -> arm_ok q2 r.
Proof.
  intros q1 q2 r Hle H. destruct r as [q'|q'|q' r0|m0|]; cbn [arm_ok] in H |- *.
  - destruct H as [H1 H2]. split; [exact H1 | lia].
  - exact I.
  - exact I.
  - exact H.
  - exact H.
Qed.

Ltac bsimp :=
  cbn [inf_budget q_mode q_br q_ob q_st q_z q_in q_out q_ret
       qset_st qset_z qset_br qset_ob qset_in qset_out qset_ret
       qmode qbad qcheck
       set_mode set_length set_have set_lens set_check set_total
       set_last set_ncode set_nlen set_ndist set_offset set_extra
       set_back set_was set_lencode set_distcode set_lenbits
       set_distbits set_next set_codes set_bits set_hold set_wbits
       set_wsize set_whave set_wnext set_alloc set_win set_flags
       set_dmax set_havedict set_head set_wrap set_work
       h_mode s_hdr s_win s_cur s_tab s_bld s_hold s_bits
       (* The ICur projections.  The list reached [s_cur] but never through
          it, so every read of a cursor field out of a state the arm had
          just built stayed stuck: [inf_LENEXT] forms [set_was st1 (u_length
          (s_cur st1))] ([Inflate.v:1058]) and could not reduce past it.
          One absence, two stuck reductions in wp5-pf's Class B arms. *)
       u_length u_offset u_extra u_back u_was
       br_have br_bits br_in br_next br_hold o_left o_put o_buf
       br_dropbits br_initbits br_bytebits ob_write inf_mrank].

(** ** The arms that terminate the trip: nothing to prove

    [inflate.c:1229-1240].  BAD and DONE [goto inf_leave]; MEM and SYNC
    [return]; the eight gzip arms are [InfDead] and [inf_wf]'s
    [wrap & 2 = 0] makes them unreachable. *)

Lemma arm_BAD  : forall q, arm_ok q (inf_BAD q).   Proof. intros; exact I. Qed.
Lemma arm_DONE : forall q, arm_ok q (inf_DONE q).  Proof. intros; exact I. Qed.
Lemma arm_MEM  : forall q, arm_ok q (inf_MEM q).   Proof. intros; exact I. Qed.
Lemma arm_SYNC : forall q, arm_ok q (inf_SYNC q).  Proof. intros; exact I. Qed.

(** The eight gzip arms are [InfDead], so [arm_ok] is FALSE for them —
    correctly: they are excluded by reachability ([inf_wf]'s
    [wrap & 2 = 0]), not by anything the arm itself does.  They are the
    reason [step_ok_covered] below is a [match] on the mode rather than an
    unconditional statement. *)

(** ** [inflate.c:1206-1228] [case LENGTH] *)

Lemma arm_LENGTH :
  forall q, q_pos q -> q_mode q = M_LENGTH -> arm_ok q (inf_LENGTH q).
Proof.
  intros q Hp Hm. pose proof Hp as (Hh & Hb & Hl).
  unfold inf_LENGTH.
  destruct (negb (Z.eqb (h_wrap (s_hdr (q_st q))) 0)
            && negb (Z.eqb (h_flags (s_hdr (q_st q))) 0)); [|exact I].
  destruct (inf_nb 32 (q_br q)) as [b|b] eqn:Enb; [|exact I].
  apply inf_nb_bud in Enb as (E1 & E2 & E3).
  destruct (negb (Z.eqb (Z.land (h_wrap (s_hdr (q_st q))) 4) 0)
            && negb (Z.eqb (br_hold b)
                       (Z.land (h_total (s_hdr (q_st q))) 4294967295)));
    [|exact I].
  cbn [arm_ok]. split.
  - unfold q_pos. bsimp. repeat split; lia.
  - apply rank2_lt; [apply q_pos_bud, Hp|].
    unfold inf_budget at 1. bsimp. rewrite Hm. cbn [inf_mrank].
    unfold inf_budget. lia.
Qed.

(** Rank helpers that take the two modes as data, so an arm never has to
    fight [cbn] over [q_mode]. *)
Lemma rank2_lt' :
  forall q q' m m',
    q_mode q = m -> q_mode q' = m' -> 0 <= inf_budget q ->
    33 * inf_budget q' + (16212 - inf_mrank m')
      < 33 * inf_budget q + (16212 - inf_mrank m) ->
    (inf_rank2 q' < inf_rank2 q)%nat.
Proof. intros q q' m m' H1 H2 Hb H. apply rank2_lt; [exact Hb|]. now rewrite H1, H2. Qed.

Lemma rank2_le' :
  forall q q' m m',
    q_mode q = m -> q_mode q' = m' ->
    33 * inf_budget q' + (16212 - inf_mrank m')
      <= 33 * inf_budget q + (16212 - inf_mrank m) ->
    (inf_rank2 q' <= inf_rank2 q)%nat.
Proof. intros q q' m m' H1 H2 H. apply rank2_le. now rewrite H1, H2. Qed.

Lemma land_nonneg_r : forall x m, 0 <= m -> 0 <= Z.land x m.
Proof. intros x m H. apply Z.land_nonneg. now right. Qed.

(** [BYTEBITS] takes off [bits & 7], which is [bits mod 8] and so never
    more than [bits] itself. *)
Lemma land7_le : forall x, 0 <= x -> 0 <= Z.land x 7 <= x.
Proof.
  intros x Hx. replace 7 with (Z.ones 3) by reflexivity.
  rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
  pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
  pose proof (Z.mod_le x 8 Hx ltac:(lia)). lia.
Qed.

Lemma inf_nb_ok : forall n b b', inf_nb n b = NBOk b' -> n <= br_bits b'.
Proof. intros n b b' H. apply inf_nb_needbits in H. now apply br_needbits_ok in H. Qed.

Ltac obsimp := cbn [ob_write o_left o_put o_buf].

(** ** [inflate.c:1188-1205] [case CHECK]

    The [ck] the arm compares against is read out of the state AFTER the
    conditional [UPDATE_CHECK] ([:1198]), so the decisive boolean mentions
    the whole post-update state.  Rather than write that term out, the
    tail is proved over an ABSTRACT boolean — the same route-around
    [InflateFast.v] uses for [if_step_body_cont], and for the same reason:
    it keeps the composite term out of the proof term the kernel has to
    convert at [Qed]. *)

Lemma check_tail_ok :
  forall q q5 b (cnd : bool),
    q_pos q -> q_mode q = M_CHECK ->
    q_br q5 = b -> o_left (q_ob q5) = o_left (q_ob q) -> q_mode q5 = M_CHECK ->
    0 <= br_have b -> br_bits (q_br q) <= br_bits b ->
    8 * br_have b + br_bits b = 8 * br_have (q_br q) + br_bits (q_br q) ->
    arm_ok q (if cnd then InfCont (qbad q5 MSG_DATA_CHECK)
              else inf_LENGTH (qmode (qset_br q5 (br_initbits b)) M_LENGTH)).
Proof.
  intros q q5 b cnd Hp Hm Hbr Hob Hm5 Hh Hb Hbud.
  pose proof Hp as (Hh0 & Hb0 & Hl0).
  destruct cnd.
  - cbn [arm_ok]. split.
    + unfold q_pos. bsimp. rewrite Hbr, Hob. repeat split; lia.
    + apply rank2_lt' with (m := M_CHECK) (m' := M_BAD);
        [exact Hm | bsimp; reflexivity | apply q_pos_bud, Hp |].
      cbn [inf_mrank]. unfold inf_budget. bsimp. rewrite Hbr, Hob. lia.
  - apply arm_ok_mono
      with (q1 := qmode (qset_br q5 (br_initbits b)) M_LENGTH).
    + apply rank2_le' with (m := M_CHECK) (m' := M_LENGTH);
        [exact Hm | reflexivity |].
      cbn [inf_mrank]. unfold inf_budget. bsimp. rewrite Hob. lia.
    + apply arm_LENGTH; [|reflexivity].
      unfold q_pos. bsimp. rewrite Hob. repeat split; lia.
Qed.

Lemma arm_CHECK :
  forall q, q_pos q -> q_mode q = M_CHECK -> arm_ok q (inf_CHECK q).
Proof.
  intros q Hp Hm. pose proof Hp as (Hh & Hb & Hl).
  unfold inf_CHECK.
  destruct (Z.eqb (h_wrap (s_hdr (q_st q))) 0).
  { apply arm_ok_mono with (q1 := qmode q M_LENGTH).
    - apply rank2_le' with (m := M_CHECK) (m' := M_LENGTH);
        [exact Hm | reflexivity |].
      cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
    - apply arm_LENGTH; [exact Hp | reflexivity]. }
  destruct (inf_nb 32 (q_br q)) as [b|b] eqn:Enb; [|exact I].
  pose proof Enb as Enb'. apply inf_nb_bud in Enb' as (E1 & E2 & E3).
  cbv zeta.
  destruct (negb (Z.eqb (Z.land (h_wrap (s_hdr (q_st q))) 4) 0)
            && negb (Z.eqb (q_out q - o_left (q_ob q)) 0));
    apply check_tail_ok; try assumption; try (bsimp; reflexivity);
    try (bsimp; exact Hm); try (apply E3, Hh); try lia.
Qed.

(** ** [inflate.c:1181-1187] [case LIT] — one byte, every time *)

Lemma arm_LIT :
  forall q m, q_pos q -> q_mode q = m -> inf_mrank m <= 16205 ->
    arm_ok q (inf_LIT q).
Proof.
  intros q m Hp Hm Hr. pose proof Hp as (Hh & Hb & Hl).
  pose proof (inf_mrank_range m) as Hrr.
  unfold inf_LIT.
  destruct (Z.eqb (o_left (q_ob q)) 0) eqn:E0; [exact I|].
  apply Z.eqb_neq in E0.
  cbn [arm_ok]. split.
  - unfold q_pos. bsimp. obsimp. repeat split; lia.
  - apply rank2_lt' with (m := m) (m' := M_LEN);
        [exact Hm | reflexivity | apply q_pos_bud, Hp |].
    cbn [inf_mrank]. unfold inf_budget. bsimp. obsimp. lia.
Qed.

(** ** [inflate.c:1129-1180] [case MATCH]

    The shared tail of the two [from] branches, parameterised by the byte
    count and the source, so the copy accounting is done once.  [1 <= cw3]
    is what [inf_wf]'s [1 <= state->length] obligation is FOR: without it
    the arm copies nothing, sets [mode = LEN] and the trip is free. *)

Lemma match_tail_ok :
  forall q m cw3 src,
    q_pos q -> q_mode q = m -> inf_mrank m <= 16204 ->
    1 <= cw3 <= o_left (q_ob q) ->
    arm_ok q (InfCont (if Z.eqb (u_length (s_cur (q_st q)) - cw3) 0
                       then qmode (qset_ob (qset_st q
                              (set_length (q_st q)
                                 (u32 (u_length (s_cur (q_st q)) - cw3))))
                              (ob_copyn (Z.to_nat cw3) (w_win (s_win (q_st q)))
                                        (q_ob q) src)) M_LEN
                       else qset_ob (qset_st q
                              (set_length (q_st q)
                                 (u32 (u_length (s_cur (q_st q)) - cw3))))
                              (ob_copyn (Z.to_nat cw3) (w_win (s_win (q_st q)))
                                        (q_ob q) src))).
Proof.
  intros q m cw3 src Hp Hm Hr Hc. pose proof Hp as (Hh & Hb & Hl).
  pose proof (inf_mrank_range m) as Hrr.
  assert (Hleft : o_left (ob_copyn (Z.to_nat cw3) (w_win (s_win (q_st q)))
                            (q_ob q) src) = o_left (q_ob q) - cw3).
  { rewrite ob_copyn_left_eq, Z2Nat.id by lia. reflexivity. }
  destruct (Z.eqb (u_length (s_cur (q_st q)) - cw3) 0);
    cbn [arm_ok]; split.
  - unfold q_pos. bsimp. rewrite Hleft. repeat split; lia.
  - apply rank2_lt' with (m := m) (m' := M_LEN);
      [exact Hm | reflexivity | apply q_pos_bud, Hp |].
    cbn [inf_mrank]. unfold inf_budget. bsimp. rewrite Hleft. lia.
  - unfold q_pos. bsimp. rewrite Hleft. repeat split; lia.
  - apply rank2_lt' with (m := m) (m' := m);
      [exact Hm | bsimp; exact Hm | apply q_pos_bud, Hp |].
    unfold inf_budget. bsimp. rewrite Hleft. lia.
Qed.

Lemma zmin_if : forall x y, 1 <= x -> 1 <= y -> 1 <= (if Z.ltb x y then x else y).
Proof. intros x y Hx Hy. destruct (Z.ltb x y); lia. Qed.

Lemma zmin_if_le_l : forall x y, (if Z.ltb x y then x else y) <= x.
Proof.
  intros x y. destruct (Z.ltb x y) eqn:E; [lia|]. apply Z.ltb_ge in E. lia.
Qed.

Lemma arm_MATCH :
  forall q m, q_pos q -> q_mode q = m -> inf_mrank m <= 16204 ->
    1 <= u_length (s_cur (q_st q)) ->
    0 <= u_offset (s_cur (q_st q)) < 4294967296 ->
    0 <= w_wnext (s_win (q_st q)) ->
    arm_ok q (inf_MATCH q).
Proof.
  intros q m Hp Hm Hr Hlen Hoff Hwn. pose proof Hp as (Hh & Hb & Hl).
  pose proof (inf_mrank_range m) as Hrr.
  unfold inf_MATCH. cbv zeta.
  destruct (Z.eqb (o_left (q_ob q)) 0) eqn:E0; [exact I|].
  apply Z.eqb_neq in E0.
  pose proof (u32_range (q_out q - o_left (q_ob q))) as Hod.
  destruct (Z.ltb (u32 (q_out q - o_left (q_ob q)))
                  (u_offset (s_cur (q_st q)))) eqn:Eod.
  - apply Z.ltb_lt in Eod.
    assert (Hcw : u32 (u_offset (s_cur (q_st q))
                       - u32 (q_out q - o_left (q_ob q)))
                  = u_offset (s_cur (q_st q))
                    - u32 (q_out q - o_left (q_ob q)))
      by (apply u32_id; lia).
    destruct (Z.ltb (w_whave (s_win (q_st q)))
                (u32 (u_offset (s_cur (q_st q))
                      - u32 (q_out q - o_left (q_ob q))))
              && negb (Z.eqb (t_sane (s_tab (q_st q))) 0)).
    + cbn [arm_ok]. split.
      * unfold q_pos. bsimp. repeat split; lia.
      * apply rank2_lt' with (m := m) (m' := M_BAD);
          [exact Hm | reflexivity | apply q_pos_bud, Hp |].
        cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
    + destruct (Z.ltb (w_wnext (s_win (q_st q)))
                  (u32 (u_offset (s_cur (q_st q))
                        - u32 (q_out q - o_left (q_ob q))))) eqn:Ewn.
      * apply Z.ltb_lt in Ewn.
        assert (Hc1 : u32 (u32 (u_offset (s_cur (q_st q))
                                - u32 (q_out q - o_left (q_ob q)))
                           - w_wnext (s_win (q_st q)))
                      = u32 (u_offset (s_cur (q_st q))
                             - u32 (q_out q - o_left (q_ob q)))
                        - w_wnext (s_win (q_st q)))
          by (apply u32_id; lia).
        cbn [fst snd]. apply match_tail_ok with (m := m); try assumption.
        split; [apply zmin_if; [lia | apply zmin_if; lia] | apply zmin_if_le_l].
      * apply Z.ltb_ge in Ewn.
        cbn [fst snd]. apply match_tail_ok with (m := m); try assumption.
        split; [apply zmin_if; [lia | apply zmin_if; lia] | apply zmin_if_le_l].
  - apply match_tail_ok with (m := m); try assumption.
    split; [apply zmin_if; lia | apply zmin_if_le_l].
Qed.

Lemma zmin_if_le_r : forall x y, (if Z.ltb x y then x else y) <= y.
Proof.
  intros x y. destruct (Z.ltb x y) eqn:E; [|lia]. apply Z.ltb_lt in E. lia.
Qed.

Lemma zmin_if_nonneg :
  forall x y, 0 <= x -> 0 <= y -> 0 <= (if Z.ltb x y then x else y).
Proof. intros x y Hx Hy. destruct (Z.ltb x y); lia. Qed.

(** ** [inflate.c:875-887] [case COPY]

    Two InfConts.  The [copy != 0] one moves [c2] bytes straight from
    [next_in] to [put], so it spends [9 * c2] of budget (eight bits of
    input plus one byte of output room) — the largest single-trip spend in
    the machine.  The [copy == 0] one is the epsilon edge this file's
    finding is about; it is the reason [inf_mrank] puts COPY below TYPE. *)

Lemma copy_tail_ok :
  forall q m c2,
    q_pos q -> q_mode q = m ->
    1 <= c2 -> c2 <= o_left (q_ob q) -> c2 <= br_have (q_br q) ->
    arm_ok q (InfCont (qset_ob (qset_br (qset_st q
                 (set_length (q_st q) (u32 (u_length (s_cur (q_st q)) - c2))))
                 {| br_in := br_in (q_br q); br_have := br_have (q_br q) - c2;
                    br_next := br_next (q_br q) + c2;
                    br_hold := br_hold (q_br q); br_bits := br_bits (q_br q) |})
                 {| o_buf := zcopy (Z.to_nat c2) (o_buf (q_ob q)) (o_put (q_ob q))
                                   (br_in (q_br q)) (br_next (q_br q));
                    o_put := o_put (q_ob q) + c2;
                    o_left := o_left (q_ob q) - c2 |})).
Proof.
  intros q m c2 Hp Hm H1 H2 H3. pose proof Hp as (Hh & Hb & Hl).
  pose proof (inf_mrank_range m) as Hrr.
  cbn [arm_ok]. split.
  - unfold q_pos. bsimp. repeat split; lia.
  - apply rank2_lt' with (m := m) (m' := m);
      [exact Hm | bsimp; exact Hm | apply q_pos_bud, Hp |].
    unfold inf_budget. bsimp. lia.
Qed.

Lemma arm_COPY :
  forall q m, q_pos q -> q_mode q = m -> inf_mrank m <= 16181 ->
    0 <= u_length (s_cur (q_st q)) -> arm_ok q (inf_COPY q).
Proof.
  intros q m Hp Hm Hr Hlen. pose proof Hp as (Hh & Hb & Hl).
  pose proof (inf_mrank_range m) as Hrr.
  unfold inf_COPY. cbv zeta.
  destruct (Z.eqb (u_length (s_cur (q_st q))) 0) eqn:Ecp.
  { cbn [arm_ok]. split.
    - unfold q_pos. bsimp. repeat split; lia.
    - apply rank2_lt' with (m := m) (m' := M_TYPE);
        [exact Hm | reflexivity | apply q_pos_bud, Hp |].
      cbn [inf_mrank]. unfold inf_budget. bsimp. lia. }
  apply Z.eqb_neq in Ecp.
  destruct (Z.ltb (br_have (q_br q)) (u_length (s_cur (q_st q)))) eqn:Ea;
    [apply Z.ltb_lt in Ea | apply Z.ltb_ge in Ea].
  - destruct (Z.ltb (o_left (q_ob q)) (br_have (q_br q))) eqn:Eb;
      [apply Z.ltb_lt in Eb | apply Z.ltb_ge in Eb].
    + destruct (Z.eqb (o_left (q_ob q)) 0) eqn:E0; [exact I|].
      apply Z.eqb_neq in E0. apply copy_tail_ok with (m := m); auto; lia.
    + destruct (Z.eqb (br_have (q_br q)) 0) eqn:E0; [exact I|].
      apply Z.eqb_neq in E0. apply copy_tail_ok with (m := m); auto; lia.
  - destruct (Z.ltb (o_left (q_ob q)) (u_length (s_cur (q_st q)))) eqn:Eb;
      [apply Z.ltb_lt in Eb | apply Z.ltb_ge in Eb].
    + destruct (Z.eqb (o_left (q_ob q)) 0) eqn:E0; [exact I|].
      apply Z.eqb_neq in E0. apply copy_tail_ok with (m := m); auto; lia.
    + destruct (Z.eqb (u_length (s_cur (q_st q))) 0) eqn:E0;
        [apply Z.eqb_eq in E0; lia|].
      apply Z.eqb_neq in E0. apply copy_tail_ok with (m := m); auto; lia.
Qed.

(** [inflate.c:873-874] [case COPY_]. *)
Lemma arm_COPY_ :
  forall q, q_pos q -> q_mode q = M_COPY_ ->
    0 <= u_length (s_cur (q_st q)) -> arm_ok q (inf_COPY_ q).
Proof.
  intros q Hp Hm Hlen. unfold inf_COPY_.
  apply arm_ok_mono with (q1 := qmode q M_COPY).
  - apply rank2_le' with (m := M_COPY_) (m' := M_COPY);
      [exact Hm | reflexivity |].
    cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
  - apply arm_COPY with (m := M_COPY);
      [unfold q_pos; bsimp; exact Hp | reflexivity | cbn [inf_mrank]; lia |].
    bsimp. exact Hlen.
Qed.

(** ** [inflate.c:858-872] [case STORED] *)

Lemma arm_STORED :
  forall c q, q_pos q -> q_mode q = M_STORED -> arm_ok q (inf_STORED c q).
Proof.
  intros c q Hp Hm. pose proof Hp as (Hh & Hb & Hl).
  pose proof (land7_le (br_bits (q_br q)) Hb) as H7.
  unfold inf_STORED.
  destruct (inf_nb 32 (br_bytebits (q_br q))) as [b|b] eqn:Enb; [|exact I].
  pose proof Enb as Enb'. apply inf_nb_bud in Enb' as (E1 & E2 & E3).
  pose proof (inf_nb_ok _ _ _ Enb) as E32.
  cbn [br_bytebits br_dropbits br_have br_bits] in E1, E2, E3.
  bsimp.
  destruct (negb (Z.eqb (Z.land (br_hold b) 65535)
                    (Z.lxor (Z.shiftr (br_hold b) 16) 65535))).
  - cbn [arm_ok]. split.
    + unfold q_pos. bsimp. repeat split; lia.
    + apply rank2_lt' with (m := M_STORED) (m' := M_BAD);
        [exact Hm | reflexivity | apply q_pos_bud, Hp |].
      cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
  - destruct (Z.eqb (n_flush c) Z_TREES); [exact I|].
    apply arm_ok_mono
      with (q1 := qmode (qset_br (qset_st q
                    (set_length (q_st q) (Z.land (u32 (br_hold b)) 65535)))
                    (br_initbits b)) M_COPY_).
    + apply rank2_le' with (m := M_STORED) (m' := M_COPY_);
        [exact Hm | reflexivity |].
      cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
    + apply arm_COPY_; [unfold q_pos; bsimp; repeat split; lia | reflexivity |].
      bsimp. apply land_nonneg_r. lia.
Qed.

Ltac dif := match goal with |- arm_ok _ (if ?B then _ else _) => destruct B end.

Ltac contsplit src tgt Hm Hp :=
  cbn [arm_ok]; split;
  [ unfold q_pos; bsimp; repeat split; lia
  | apply rank2_lt' with (m := src) (m' := tgt);
    [exact Hm | reflexivity | apply q_pos_bud, Hp |];
    cbn [inf_mrank]; unfold inf_budget; bsimp; lia ].

(** ** [inflate.c:828-857] [case TYPEDO]

    Four of the five [break]s spend the three bits of the block header.
    The fifth ([:829-833], [last] already set) only does [BYTEBITS], which
    spends [bits & 7] — possibly zero — and is therefore an epsilon edge;
    it is safe because it moves the mode UP, to CHECK. *)

Lemma arm_TYPEDO :
  forall c q m, q_pos q -> q_mode q = m -> inf_mrank m <= 16194 ->
    arm_ok q (inf_TYPEDO c q).
Proof.
  intros c q m Hp Hm Hr. pose proof Hp as (Hh & Hb & Hl).
  pose proof (inf_mrank_range m) as Hrr.
  pose proof (land7_le (br_bits (q_br q)) Hb) as H7.
  unfold inf_TYPEDO. cbv zeta.
  dif; [contsplit m M_CHECK Hm Hp|].
  destruct (inf_nb 3 (q_br q)) as [b|b] eqn:Enb; [|exact I].
  pose proof Enb as Enb'. apply inf_nb_bud in Enb' as (E1 & E2 & E3).
  pose proof (inf_nb_ok _ _ _ Enb) as E3b.
  dif; [contsplit m M_STORED Hm Hp|].
  dif.
  { dif; [exact I|]. contsplit m M_LEN_ Hm Hp. }
  dif; [contsplit m M_TABLE Hm Hp|]. contsplit m M_BAD Hm Hp.
Qed.

(** [inflate.c:825-827] [case TYPE]. *)
Lemma arm_TYPE :
  forall c q m, q_pos q -> q_mode q = m -> inf_mrank m <= 16193 ->
    arm_ok q (inf_TYPE c q).
Proof.
  intros c q m Hp Hm Hr. unfold inf_TYPE.
  destruct (Z.eqb (n_flush c) Z_BLOCK || Z.eqb (n_flush c) Z_TREES); [exact I|].
  apply arm_TYPEDO with (m := m); [exact Hp | exact Hm | lia].
Qed.

(** [inflate.c:815-823] [case DICT]. *)
Lemma arm_DICT :
  forall c q, q_pos q -> q_mode q = M_DICT -> arm_ok q (inf_DICT c q).
Proof.
  intros c q Hp Hm. unfold inf_DICT.
  destruct (Z.eqb (h_havedict (s_hdr (q_st q))) 0); [exact I|].
  apply arm_ok_mono with (q1 := qmode (qcheck q (adler32_z 0 true [])) M_TYPE).
  - apply rank2_le' with (m := M_DICT) (m' := M_TYPE); [exact Hm | reflexivity |].
    cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
  - apply arm_TYPE with (m := M_TYPE);
      [unfold q_pos; bsimp; exact Hp | reflexivity | cbn [inf_mrank]; lia].
Qed.

(** [inflate.c:809-814] [case DICTID]. *)
Lemma arm_DICTID :
  forall c q, q_pos q -> q_mode q = M_DICTID -> arm_ok q (inf_DICTID c q).
Proof.
  intros c q Hp Hm. pose proof Hp as (Hh & Hb & Hl).
  unfold inf_DICTID.
  destruct (inf_nb 32 (q_br q)) as [b|b] eqn:Enb; [|exact I].
  pose proof Enb as Enb'. apply inf_nb_bud in Enb' as (E1 & E2 & E3).
  apply arm_ok_mono
    with (q1 := qmode (qset_br (qcheck q (zswap32 (br_hold b)))
                               (br_initbits b)) M_DICT).
  - apply rank2_le' with (m := M_DICTID) (m' := M_DICT); [exact Hm | reflexivity |].
    cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
  - apply arm_DICT; [unfold q_pos; bsimp; repeat split; lia | reflexivity].
Qed.

(** ** [inflate.c:588-649] [case HEAD] *)

Lemma arm_HEAD :
  forall c q, q_pos q -> q_mode q = M_HEAD -> arm_ok q (inf_HEAD c q).
Proof.
  intros c q Hp Hm. pose proof Hp as (Hh & Hb & Hl).
  unfold inf_HEAD. cbv zeta.
  dif.
  { apply arm_ok_mono with (q1 := qmode q M_TYPEDO).
    - apply rank2_le' with (m := M_HEAD) (m' := M_TYPEDO);
        [exact Hm | reflexivity |].
      cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
    - apply arm_TYPEDO with (m := M_TYPEDO);
        [unfold q_pos; bsimp; exact Hp | reflexivity | cbn [inf_mrank]; lia]. }
  destruct (inf_nb 16 (q_br q)) as [b|b] eqn:Enb; [|exact I].
  pose proof Enb as Enb'. apply inf_nb_bud in Enb' as (E1 & E2 & E3).
  pose proof (inf_nb_ok _ _ _ Enb) as E16.
  dif; [contsplit M_HEAD M_FLAGS Hm Hp|].
  dif; [contsplit M_HEAD M_BAD Hm Hp|].
  dif; [contsplit M_HEAD M_BAD Hm Hp|].
  dif; [contsplit M_HEAD M_BAD Hm Hp|].
  match goal with
  | |- context[if ?B then M_TYPE else M_DICTID] => destruct B
  end.
  - contsplit M_HEAD M_TYPE Hm Hp.
  - contsplit M_HEAD M_DICTID Hm Hp.
Qed.

(** ** From the per-arm obligation to "[inflate_model] never declines"

    The reduction, stated so that the per-arm work above plugs straight
    into it.  [step_ok] bundles the three things a trip must not do: raise
    the rank, land in one of the eight unmodelled gzip arms, or exhaust a
    fuel.  The section [Variable] is the intended mechanism for a
    dependency this layer does not own — discharging the section turns it
    into honest universal quantification, and the theorem below is what
    the DAG's capstone consumes once every arm is in. *)

Definition step_ok (c : InfCtx) (q : InfSt) : Prop :=
  match inf_step c q with
  | InfCont q'  => q_pos q' /\ (inf_rank2 q' < inf_rank2 q)%nat
  | InfLeave _  => True
  | InfRet _ _  => True
  | InfDead _   => False
  | InfFuel     => False
  end.

Definition exit_step (r : InfStep) : Prop :=
  match r with InfLeave _ => True | InfRet _ _ => True | _ => False end.

Section InflateTermination.

  Variable c : InfCtx.
  Variable Hstep : forall q, q_pos q -> step_ok c q.

  Lemma inf_loop_reaches_exit :
    forall n q, q_pos q -> (inf_rank2 q <= n)%nat ->
      exists r, inf_loop (S n) c q = Some r /\ exit_step r.
  Proof.
    induction n as [|n IH]; intros q Hp Hr;
      rewrite inf_loop_S;
      pose proof (Hstep q Hp) as HS; unfold step_ok in HS;
      destruct (inf_step c q) as [q'|q'|q' r0|m0|] eqn:E.
    - destruct HS as [Hp' Hlt]. lia.
    - exists (InfLeave q'). split; [reflexivity | exact I].
    - exists (InfRet q' r0). split; [reflexivity | exact I].
    - contradiction.
    - contradiction.
    - destruct HS as [Hp' Hlt]. apply IH; [exact Hp' | lia].
    - exists (InfLeave q'). split; [reflexivity | exact I].
    - exists (InfRet q' r0). split; [reflexivity | exact I].
    - contradiction.
    - contradiction.
  Qed.

  Theorem inflate_model_total :
    forall a, inf_ctx a = c ->
      0 <= g_avail_in a -> 0 <= g_avail_out a -> 0 <= s_bits (g_st a) ->
      exists r, inflate_model a = Some r.
  Proof.
    intros a Hc Hin Hout Hbits. unfold inflate_model.
    destruct (g_state_null a || g_out_null a
              || (g_in_null a && negb (Z.eqb (g_avail_in a) 0)));
      [eexists; reflexivity|].
    rewrite Hc.
    assert (Hb0 : br_bits (q_br (inf_st0 a)) = s_bits (g_st a)).
    { unfold inf_st0. destruct (h_mode (s_hdr (g_st a))); reflexivity. }
    assert (Hp0 : q_pos (inf_st0 a)).
    { unfold q_pos. rewrite Hb0. cbn [inf_st0 q_br q_ob br_have o_left].
      repeat split; lia. }
    set (n := Z.to_nat (33 * (8 * br_have (q_br (inf_st0 a))
                              + br_bits (q_br (inf_st0 a))
                              + o_left (q_ob (inf_st0 a)) + 1))).
    assert (Hfuel : inf_fuel (inf_st0 a) = S n) by reflexivity.
    assert (Hle : (inf_rank2 (inf_st0 a) <= n)%nat).
    { pose proof (inf_fuel_dominates_rank2 (inf_st0 a) (q_pos_bud _ Hp0)) as HD.
      rewrite Hfuel in HD. lia. }
    destruct (inf_loop_reaches_exit n (inf_st0 a) Hp0 Hle) as [r [Heq Hr]].
    rewrite Hfuel, Heq.
    destruct r as [q'|q'|q' r0|m0|]; cbn [exit_step] in Hr; try contradiction.
    - destruct (inf_leave c q') as [q'' rr]. eexists; reflexivity.
    - eexists; reflexivity.
  Qed.

End InflateTermination.

(** ** Eliminating the fetch-loop and code-length-loop [None]s

    Three more of the model's fuel sentinels are unreachable outright,
    with no invariant beyond "[avail_in] is not negative".  [inflate.c:
    1036-1047] / [:1092-1096]'s [for (;;) { ...; PULLBYTE(); }] can only
    go round while there is a byte left, and [inf_fetch] gives it
    [S avail_in] trips. *)

Lemma inf_fetch_go_no_fuel :
  forall f t nb b,
    0 <= br_have b -> (Z.to_nat (br_have b) < f)%nat ->
    inf_fetch_go f t nb b <> FetchFuel.
Proof.
  induction f as [|f IH]; intros t nb b Hh Hf; [lia|].
  cbn [inf_fetch_go].
  destruct (Z.leb (c_bits (t (br_bits_of nb b))) (br_bits b)); [discriminate|].
  destruct (br_pullbyte b) as [b1|] eqn:Hp; [|discriminate].
  assert (Hne : br_have b <> 0).
  { unfold br_pullbyte in Hp. destruct (Z.eqb (br_have b) 0) eqn:E;
      [discriminate|]. now apply Z.eqb_neq in E. }
  apply br_pullbyte_step in Hp as (H1 & _ & _ & _).
  apply IH; lia.
Qed.

Lemma inf_fetch_no_fuel :
  forall t nb b, 0 <= br_have b -> inf_fetch t nb b <> FetchFuel.
Proof. intros t nb b Hh. apply inf_fetch_go_no_fuel; [exact Hh | lia]. Qed.

Lemma inf_fetch2_go_no_fuel :
  forall f t lst b,
    0 <= br_have b -> (Z.to_nat (br_have b) < f)%nat ->
    inf_fetch2_go f t lst b <> FetchFuel.
Proof.
  induction f as [|f IH]; intros t lst b Hh Hf; [lia|].
  cbn [inf_fetch2_go].
  destruct (Z.leb (c_bits lst
              + c_bits (t (c_val lst
                  + Z.shiftr (br_bits_of (c_bits lst + c_op lst) b) (c_bits lst))))
              (br_bits b)); [discriminate|].
  destruct (br_pullbyte b) as [b1|] eqn:Hp; [|discriminate].
  assert (Hne : br_have b <> 0).
  { unfold br_pullbyte in Hp. destruct (Z.eqb (br_have b) 0) eqn:E;
      [discriminate|]. now apply Z.eqb_neq in E. }
  apply br_pullbyte_step in Hp as (H1 & _ & _ & _).
  apply IH; lia.
Qed.

Lemma inf_fetch2_no_fuel :
  forall t lst b, 0 <= br_have b -> inf_fetch2 t lst b <> FetchFuel.
Proof. intros t lst b Hh. apply inf_fetch2_go_no_fuel; [exact Hh | lia]. Qed.

(** …so the two-level decode LEN and DIST share never answers [DecFuel]. *)
Lemma inf_decode_no_fuel :
  forall sub t rb b, 0 <= br_have b -> inf_decode sub t rb b <> DecFuel.
Proof.
  intros sub t rb b Hh. unfold inf_decode.
  destruct (inf_fetch t rb b) as [h0 b0|b0|] eqn:Ef;
    [|discriminate|now apply inf_fetch_no_fuel in Ef].
  apply inf_fetch_bud in Ef as (_ & Eh).
  destruct (sub h0); [|discriminate].
  destruct (inf_fetch2 t h0 b0) as [h1 b1|b1|] eqn:Ef2;
    [discriminate|discriminate|].
  now apply inf_fetch2_no_fuel in Ef2; [|apply Eh].
Qed.

(** ** The budget and positivity facts for [inf_decode]

    These were split out while a batch was in flight and folded back here,
    which is their home: they are [inf_decode] facts and they sit beside
    [inf_decode_no_fuel], the third of the three.  All three surfaced at
    once because [inf_LEN] and [inf_DIST] are [inf_decode]'s first
    arm-level consumers — an untouched function accumulates exactly the
    facts nobody needed, and the first real consumer pays for all of them.

    The two [br_dropbits] projections first, named so the reader can see
    that [br_have] is untouched and only [br_bits] moves. *)
Lemma dropbits_have : forall n b, br_have (br_dropbits n b) = br_have b.
Proof. reflexivity. Qed.

Lemma dropbits_bits : forall n b, br_bits (br_dropbits n b) = br_bits b - n.
Proof. reflexivity. Qed.

(** The budget accounting: EXACT, and hypothesis-free.

    The inequality shape one would reach for first,

      8 * br_have b2 + br_bits b2 <= 8 * br_have b + br_bits b

    is NOT unconditionally true.  [br_dropbits n b] sets [br_bits :=
    br_bits b - n] ([ZBitsIn.v:103-105]), so a NEGATIVE [c_bits] on a
    decoded entry makes the drop ADD bits and the budget RISE.  Stated as
    an inequality the lemma silently imports a table-value obligation
    ([0 <= c_bits] on the fetched entries), which for dynamic tables is
    node T5.  Under this layer's standing rule — keep the statement
    general, put the table obligation at the instantiation site — that is
    the wrong place for it.  [nb] IS the total number of bits dropped
    ([Inflate.v:1019-1022]), so the equation needs nothing, and a consumer
    holding [0 <= nb] recovers the inequality in one [lia].

    Mirrors [inf_fetch_bud] / [inf_fetch2_bud] above, which use [=] because
    fetch only PULLBYTEs and conserves the total.  Decode spends, so the
    equation carries the [- nb]. *)
Lemma inf_decode_bud :
  forall sub t rb b h b2 nb,
    inf_decode sub t rb b = DecOk h b2 nb ->
    8 * br_have b2 + br_bits b2 = 8 * br_have b + br_bits b - nb
    /\ (0 <= br_have b -> 0 <= br_have b2).
Proof.
  intros sub t rb b h b2 nb H. unfold inf_decode in H.
  destruct (inf_fetch t rb b) as [h0 b0|b0|] eqn:Ef; [|discriminate|discriminate].
  apply inf_fetch_bud in Ef as (E0 & P0).
  destruct (sub h0) eqn:Es.
  - destruct (inf_fetch2 t h0 b0) as [h1 b1|b1|] eqn:Ef2;
      [|discriminate|discriminate].
    apply inf_fetch2_bud in Ef2 as (E1 & P1).
    inversion H. subst. cbn [br_dropbits br_have br_bits].
    split; [lia | intro Hh; auto].
  - inversion H. subst. cbn [br_dropbits br_have br_bits].
    split; [lia | intro Hh; auto].
Qed.

(** The inequality as a corollary, with its side condition explicit so that
    it is discharged AT THE CALL SITE. *)
Corollary inf_decode_bud_le :
  forall sub t rb b h b2 nb,
    inf_decode sub t rb b = DecOk h b2 nb -> 0 <= nb ->
    8 * br_have b2 + br_bits b2 <= 8 * br_have b + br_bits b
    /\ (0 <= br_have b -> 0 <= br_have b2).
Proof.
  intros sub t rb b h b2 nb H Hnb.
  destruct (inf_decode_bud sub t rb b h b2 nb H) as (E & P).
  split; [lia | exact P].
Qed.

(** ** [0 <= br_bits] on [inf_decode]'s output reader — UNCONDITIONAL

    The guarded shape ([0 <= br_bits b -> 0 <= br_bits b2]) is not needed,
    and the reason is in the fetch recursion rather than in any table
    property.  [inf_fetch_go] ([Inflate.v:458-468]) returns [FetchOk h b]
    ONLY under the guard [Z.leb (c_bits h) (br_bits b) = true] — success and
    bits-are-available are the SAME test.  A successful fetch therefore
    carries [c_bits h <= br_bits b] by construction, and since
    [br_bits (br_dropbits n b) = br_bits b - n] the dropped reader's bit
    count is non-negative with no hypothesis at all.  Two-level likewise:
    [inf_fetch2_go]'s guard is [c_bits lst + c_bits h <= br_bits b], which
    covers both drops.  Stating it unconditionally keeps the hypothesis out
    of all four arms that delegate through [inf_LEN]. *)
Lemma inf_fetch_go_ok_bits :
  forall f t nb b h b', inf_fetch_go f t nb b = FetchOk h b' ->
    c_bits h <= br_bits b'.
Proof.
  induction f as [|k IH]; intros t nb b h b' H; [discriminate|].
  cbn [inf_fetch_go] in H.
  destruct (Z.leb (c_bits (t (br_bits_of nb b))) (br_bits b)) eqn:Eg.
  - inversion H; subst. now apply Z.leb_le in Eg.
  - destruct (br_pullbyte b) as [b1|] eqn:Ep; [|discriminate].
    exact (IH t nb b1 h b' H).
Qed.

Lemma inf_fetch_ok_bits :
  forall t nb b h b', inf_fetch t nb b = FetchOk h b' -> c_bits h <= br_bits b'.
Proof. intros t nb b h b'; apply inf_fetch_go_ok_bits. Qed.

Lemma inf_fetch2_go_ok_bits :
  forall f t lst b h b', inf_fetch2_go f t lst b = FetchOk h b' ->
    c_bits lst + c_bits h <= br_bits b'.
Proof.
  induction f as [|k IH]; intros t lst b h b' H; [discriminate|].
  cbn [inf_fetch2_go] in H.
  match type of H with
  | context[Z.leb ?a ?bb] => destruct (Z.leb a bb) eqn:Eg
  end.
  - inversion H; subst. now apply Z.leb_le in Eg.
  - destruct (br_pullbyte b) as [b1|] eqn:Ep; [|discriminate].
    exact (IH t lst b1 h b' H).
Qed.

Lemma inf_fetch2_ok_bits :
  forall t lst b h b', inf_fetch2 t lst b = FetchOk h b' ->
    c_bits lst + c_bits h <= br_bits b'.
Proof. intros t lst b h b'; apply inf_fetch2_go_ok_bits. Qed.

Lemma inf_decode_bits_nonneg :
  forall sub t rb b h b2 nb,
    inf_decode sub t rb b = DecOk h b2 nb -> 0 <= br_bits b2.
Proof.
  intros sub t rb b h b2 nb H. unfold inf_decode in H.
  destruct (inf_fetch t rb b) as [h0 b0|b0|] eqn:Ef; [|discriminate|discriminate].
  apply inf_fetch_ok_bits in Ef as G0.
  destruct (sub h0) eqn:Es.
  - destruct (inf_fetch2 t h0 b0) as [h1 b1|b1|] eqn:Ef2;
      [|discriminate|discriminate].
    apply inf_fetch2_ok_bits in Ef2 as G1.
    inversion H. subst. cbn [br_dropbits br_bits]. lia.
  - inversion H. subst. cbn [br_dropbits br_bits]. lia.
Qed.

(** ** [inflate.c:935-985]: CODELENS's inner [while] always reaches an exit

    Every [ClCont] writes at least one entry ([:941-944] writes one,
    [:948-979]'s three repeat arms write [cp >= 3]), so [cl_have] strictly
    increases and the [have < nlen + ndist] guard bounds the trip count by
    [tot - have].  [inf_CODELENS] gives the loop [S tot] trips. *)

Definition cl_cont_ok (s : ClSt) (r : ClStep) : Prop :=
  match r with
  | ClCont s' => cl_have s < cl_have s' /\ 0 <= br_have (cl_br s')
  | ClFuel => False
  | _ => True
  end.

Lemma cl_step_ok :
  forall t nb tot s, 0 <= br_have (cl_br s) -> cl_cont_ok s (cl_step t nb tot s).
Proof.
  intros t nb tot s Hh. unfold cl_step.
  destruct (Z.leb tot (cl_have s)); [exact I|].
  destruct (inf_fetch t nb (cl_br s)) as [h b|b|] eqn:Ef;
    [|exact I|now apply inf_fetch_no_fuel in Ef].
  pose proof Ef as Ef'. apply inf_fetch_bud in Ef' as (_ & Eh).
  specialize (Eh Hh).
  destruct (Z.ltb (c_val h) 16);
    [cbn [cl_cont_ok cl_have cl_br]; split; [lia | exact Eh]|].
  destruct (inf_nb (if Z.eqb (c_val h) 16 then c_bits h + 2
                    else if Z.eqb (c_val h) 17 then c_bits h + 3
                    else c_bits h + 7) b) as [b'|b'] eqn:Enb; [|exact I].
  apply inf_nb_bud in Enb as (_ & _ & Eh').
  specialize (Eh' Eh).
  assert (Hb2 : forall k, 0 <= k -> 0 <= br_bits_of k (br_dropbits (c_bits h) b')).
  { intros k Hk. unfold br_bits_of. apply Z.land_nonneg. right.
    rewrite Z.shiftl_1_l.
    pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk). lia. }
  cbv zeta.
  destruct (Z.eqb (c_val h) 16).
  - destruct (Z.eqb (cl_have s) 0); [exact I|].
    destruct (Z.ltb tot (cl_have s + (3 + br_bits_of 2
                (br_dropbits (c_bits h) b')))); [exact I|].
    cbn [cl_cont_ok cl_have cl_br]. pose proof (Hb2 2 ltac:(lia)).
    split; [lia | exact Eh'].
  - destruct (Z.eqb (c_val h) 17).
    + destruct (Z.ltb tot (cl_have s + (3 + br_bits_of 3
                  (br_dropbits (c_bits h) b')))); [exact I|].
      cbn [cl_cont_ok cl_have cl_br]. pose proof (Hb2 3 ltac:(lia)).
    split; [lia | exact Eh'].
    + destruct (Z.ltb tot (cl_have s + (11 + br_bits_of 7
                  (br_dropbits (c_bits h) b')))); [exact I|].
      cbn [cl_cont_ok cl_have cl_br]. pose proof (Hb2 7 ltac:(lia)).
    split; [lia | exact Eh'].
Qed.

Definition cl_exit (r : ClStep) : Prop :=
  match r with ClCont _ => False | ClFuel => False | _ => True end.

Lemma cl_loop_reaches_exit :
  forall n t nb tot s,
    0 <= br_have (cl_br s) -> tot - cl_have s <= Z.of_nat n ->
    exists r, cl_loop (S n) t nb tot s = Some r /\ cl_exit r.
Proof.
  induction n as [|n IH]; intros t nb tot s Hh Hn; rewrite cl_loop_S;
    pose proof (cl_step_ok t nb tot s Hh) as HS;
    destruct (cl_step t nb tot s) as [s'|s'|s' m|s'|] eqn:E.
  - destruct HS as [H1 H2].
    (* [tot <= cl_have s] would have given [ClDone]; the guard is the only
       way to [ClCont], so this case is arithmetically impossible. *)
    exfalso. unfold cl_step in E.
    destruct (Z.leb tot (cl_have s)) eqn:Eg; [discriminate|].
    apply Z.leb_gt in Eg. cbn [Z.of_nat] in Hn. lia.
  - exists (ClDone s'). split; [reflexivity | exact I].
  - exists (ClBad s' m). split; [reflexivity | exact I].
  - exists (ClLeave s'). split; [reflexivity | exact I].
  - contradiction.
  - destruct HS as [H1 H2]. apply IH; [exact H2 | lia].
  - exists (ClDone s'). split; [reflexivity | exact I].
  - exists (ClBad s' m). split; [reflexivity | exact I].
  - exists (ClLeave s'). split; [reflexivity | exact I].
  - contradiction.
Qed.

(** The form [inf_CODELENS] needs: at the fuel it actually passes. *)
Corollary cl_loop_at_codelens_fuel :
  forall t nb tot s,
    0 <= br_have (cl_br s) -> 0 <= cl_have s ->
    exists r, cl_loop (S (Z.to_nat tot)) t nb tot s = Some r /\ cl_exit r.
Proof.
  intros t nb tot s Hh Hc. apply cl_loop_reaches_exit; [exact Hh | lia].
Qed.

(** ** Which modes of [inf_step] are discharged

    [arm_ok q (inf_step c q)] IS [step_ok c q], so the arms above compose
    into the dispatch directly.  The [match] below is the honest statement
    of coverage: sixteen of the thirty-two [case]s are closed, and the
    ones that are not are named by their [True] clause.

    STILL OPEN, and why (see this file's report):
    - LEN_ / LEN / LENEXT / DIST / DISTEXT.  The whole chain hangs on
      [inflate.c:1026-1033]'s [inflate_fast] call: [InflateThy]'s
      [if_model_total] shows the call ANSWERS, but not that it makes
      progress, and an [inflate_fast] that returns on an end-of-block code
      of zero width would move LEN -> TYPE for free.
    - TABLE / LENLENS / CODELENS.  Their own accounting is routine (and
      [cl_loop_reaches_exit] above removes CODELENS's loop-fuel [None]),
      but each falls through to LEN_ and so inherits the above.  Their
      remaining [InfFuel]s are [inf_table]'s, i.e. [it_model] — node T5,
      which is the fill-loop-invariant node of L3.  (That node was
      labelled [it_inv] in an earlier plan revision and is UNOWNED; the
      name denotes nothing in this tree -- do not route to it.)

    LANDED SINCE (2026-08-19, kept as the record of what the gap was):
    LENEXT / DIST / DISTEXT closed above; LEN_ / LEN closed by the Q4
    continuation (the budget walk [if_dolen_bud], the consumed-cursor
    walk [if_dolen_cw], [if_body_bud]/[if_loop_bud], and
    [if_model_bud]'s epilogue unwrap — the zero-width end-of-block hole
    named above is exactly what the strict-width premise closes); TABLE /
    LENLENS / CODELENS closed with their own accounting + it_model
    totality ([GtItTotal.it_model_total]), the LEN_ tail carried as a
    named callee obligation.  [step_ok_covered] below is 32/32. *)

(** ** The eight gzip header arms (2026-08-19, Q4 — live since the zlib-rt
    transcription)

    Each arm either LEAVES (input starved: [True]), consumes raw input
    (NEEDBITS preserves the budget and the [INITBITS] on the success path
    only lowers it; the string/extra scans consume whole bytes), or makes an
    epsilon transition whose target mode sits strictly ABOVE it in
    [inf_mrank] ([M_BAD] = 16209 and [M_TYPE] = 16193 vs 16183..16190, and
    the chain FLAGS < TIME < ... < HCRC is ascending) — so [arm_ok] closes
    by [rank2_lt']/[arm_ok_mono] with no rank surgery.  The fallthrough
    arms are proved bottom-up (HCRC first), each caller lifting its
    callee's [arm_ok] through [arm_ok_mono]. *)

(** [gz_strz] consumes at least one and at most [have] bytes... *)
Lemma gz_strz_spec :
  forall f a i have copy cp ln,
    0 <= copy < have ->
    gz_strz f a i have copy = Some (cp, ln) ->
    copy < cp <= have.
Proof.
  induction f as [|f IH]; intros a i have copy cp ln Hc H;
    cbn [gz_strz] in H; [discriminate|].
  destruct (negb (Z.eqb (a i) 0) && Z.ltb (copy + 1) have) eqn:Eg.
  - apply andb_prop in Eg as [_ Elt]. apply Z.ltb_lt in Elt.
    specialize (IH a (i + 1) have (copy + 1) cp ln ltac:(lia) H). lia.
  - injection H as <- _. split; [lia|].
    destruct (Z.leb_spec (copy + 1) have) as [Hle|Hgt]; lia.
Qed.

(** ...and with fuel [Z.to_nat have] it always answers. *)
Lemma gz_strz_some :
  forall f a i have copy,
    0 <= copy < have -> have <= copy + Z.of_nat f ->
    exists cp ln, gz_strz f a i have copy = Some (cp, ln).
Proof.
  induction f as [|f IH]; intros a i have copy Hc Hf; [cbn in Hf; lia|].
  cbn [gz_strz].
  destruct (negb (Z.eqb (a i) 0) && Z.ltb (copy + 1) have) eqn:Eg.
  - apply andb_prop in Eg as [_ Elt]. apply Z.ltb_lt in Elt.
    apply IH; lia.
  - do 2 eexists. reflexivity.
Qed.

Lemma arm_HCRC :
  forall q, q_pos q -> q_mode q = M_HCRC -> arm_ok q (inf_HCRC q).
Proof.
  intros q Hp Hm. pose proof Hp as (Hh & Hb & Hl).
  unfold inf_HCRC.
  destruct (negb (Z.eqb (Z.land (h_flags (s_hdr (q_st q))) 512) 0)).
  - destruct (inf_nb 16 (q_br q)) as [b|b] eqn:Enb; [|exact I].
    apply inf_nb_bud in Enb as (E1 & E2 & E3).
    destruct (negb (Z.eqb (Z.land (h_wrap (s_hdr (q_st q))) 4) 0)
              && negb (Z.eqb (br_hold b)
                         (Z.land (h_check (s_hdr (q_st q))) 65535))).
    + (* :791-794 header crc mismatch -> BAD *)
      cbn [arm_ok]. split.
      * unfold q_pos. bsimp. repeat split; lia.
      * apply rank2_lt; [apply q_pos_bud, Hp|].
        unfold inf_budget at 1. bsimp. rewrite Hm. cbn [inf_mrank].
        unfold inf_budget. lia.
    + (* success -> TYPE, INITBITS *)
      cbn [arm_ok]. split.
      * unfold q_pos. bsimp. repeat split; lia.
      * apply rank2_lt; [apply q_pos_bud, Hp|].
        unfold inf_budget at 1. bsimp. rewrite Hm. cbn [inf_mrank].
        unfold inf_budget. lia.
  - (* flag clear: epsilon to TYPE *)
    cbn [arm_ok]. split.
    + unfold q_pos. bsimp. repeat split; lia.
    + apply rank2_lt; [apply q_pos_bud, Hp|].
      unfold inf_budget at 1. bsimp. rewrite Hm. cbn [inf_mrank].
      unfold inf_budget. lia.
Qed.

(** The string arms share one skeleton; [mk] is the state the arm hands to
    its callee, differing only in the trailing [set_length]. *)
Lemma arm_COMMENT :
  forall q, q_pos q -> q_mode q = M_COMMENT -> arm_ok q (inf_COMMENT q).
Proof.
  intros q Hp Hm. pose proof Hp as (Hh & Hb & Hl).
  unfold inf_COMMENT.
  destruct (negb (Z.eqb (Z.land (h_flags (s_hdr (q_st q))) 4096) 0)).
  - destruct (Z.eqb (br_have (q_br q)) 0) eqn:Ehz; [exact I|].
    apply Z.eqb_neq in Ehz.
    destruct (gz_strz (Z.to_nat (br_have (q_br q))) (br_in (q_br q))
                (br_next (q_br q)) (br_have (q_br q)) 0)
      as [[cp ln]|] eqn:Egz.
    2:{ exfalso.
        destruct (gz_strz_some (Z.to_nat (br_have (q_br q))) (br_in (q_br q))
                    (br_next (q_br q)) (br_have (q_br q)) 0
                    ltac:(lia) ltac:(rewrite Z2Nat.id; lia))
          as (cp & ln & Heq).
        congruence. }
    pose proof (gz_strz_spec (Z.to_nat (br_have (q_br q))) (br_in (q_br q))
                  (br_next (q_br q)) (br_have (q_br q)) 0 cp ln
                  ltac:(lia) Egz) as Hcp.
    (* the crc conditional changes only [set_check]: budget-neutral *)
    destruct (negb (Z.eqb (Z.land (h_flags (s_hdr (q_st q))) 512) 0)
              && negb (Z.eqb (Z.land (h_wrap (s_hdr (q_st q))) 4) 0));
      destruct (negb (Z.eqb ln 0)) eqn:Eln;
      try (cbn [arm_ok]; exact I).
    + (* len = 0, crc arm taken: fall into HCRC *)
      apply (arm_ok_mono (qmode (qset_br
               (qset_st q (set_check (q_st q)
                  (crc32_z (h_check (s_hdr (q_st q))) false 0
                     (br_slice (q_br q) cp))))
               (br_consume (q_br q) cp)) M_HCRC) q).
      * apply rank2_le'
          with (m := M_COMMENT) (m' := M_HCRC); [exact Hm | reflexivity |].
        cbn [inf_mrank].
        unfold inf_budget. bsimp. cbn [br_consume br_have br_bits]. lia.
      * apply arm_HCRC; [|reflexivity].
        unfold q_pos. bsimp. cbn [br_consume br_have br_bits].
        repeat split; lia.
    + (* len = 0, crc arm skipped *)
      apply (arm_ok_mono (qmode (qset_br q (br_consume (q_br q) cp)) M_HCRC) q).
      * apply rank2_le'
          with (m := M_COMMENT) (m' := M_HCRC); [exact Hm | reflexivity |].
        cbn [inf_mrank].
        unfold inf_budget. bsimp. cbn [br_consume br_have br_bits]. lia.
      * apply arm_HCRC; [|reflexivity].
        unfold q_pos. bsimp. cbn [br_consume br_have br_bits].
        repeat split; lia.
  - (* flag clear: epsilon into HCRC *)
    apply (arm_ok_mono (qmode q M_HCRC) q).
    + apply rank2_le'
        with (m := M_COMMENT) (m' := M_HCRC); [exact Hm | reflexivity |].
      cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
    + apply arm_HCRC; [|reflexivity].
      unfold q_pos. bsimp. repeat split; lia.
Qed.

(** [PULLBYTE] adds a RAW input byte ([br_in] is a total array, not
    [u8]-clamped), so the accumulator's sign survives [NEEDBITS] only on a
    byte-valued input window — the premise [EXLEN]'s
    [state->length = (unsigned)(hold)] write needs. *)
Lemma inf_nb_go_hold :
  forall f n b b',
    0 <= br_hold b -> 0 <= br_bits b -> (forall j, 0 <= br_in b j) ->
    inf_nb_go f n b = NBOk b' -> 0 <= br_hold b'.
Proof.
  induction f as [|f IH]; intros n b b' Hh Hb Hin H; cbn [inf_nb_go] in H.
  - destruct (Z.ltb (br_bits b) n); [discriminate|]. injection H as <-. exact Hh.
  - destruct (Z.ltb (br_bits b) n); [|injection H as <-; exact Hh].
    unfold br_pullbyte in H.
    destruct (Z.eqb (br_have b) 0); [discriminate|].
    apply IH in H; [exact H| | |].
    + cbn [br_hold]. pose proof (Hin (br_next b)).
      pose proof (Z.shiftl_nonneg (br_in b (br_next b)) (br_bits b)). lia.
    + cbn [br_bits]. lia.
    + cbn [br_in]. exact Hin.
Qed.

Lemma inf_nb_hold :
  forall n b b',
    0 <= br_hold b -> 0 <= br_bits b -> (forall j, 0 <= br_in b j) ->
    inf_nb n b = NBOk b' -> 0 <= br_hold b'.
Proof. intros n b b'; apply inf_nb_go_hold. Qed.

Lemma inf_nb_in :
  forall n b b', inf_nb n b = NBOk b' -> br_in b' = br_in b.
Proof.
  intros n b b'. unfold inf_nb. generalize (Z.to_nat n) as f. intro f.
  revert b. induction f as [|f IH]; intros b H; cbn [inf_nb_go] in H.
  - destruct (Z.ltb (br_bits b) n); [discriminate|]. now injection H as <-.
  - destruct (Z.ltb (br_bits b) n); [|now injection H as <-].
    unfold br_pullbyte in H.
    destruct (Z.eqb (br_have b) 0); [discriminate|].
    apply IH in H. rewrite H. reflexivity.
Qed.

Lemma arm_NAME :
  forall q, q_pos q -> q_mode q = M_NAME -> arm_ok q (inf_NAME q).
Proof.
  intros q Hp Hm. pose proof Hp as (Hh & Hb & Hl).
  unfold inf_NAME.
  destruct (negb (Z.eqb (Z.land (h_flags (s_hdr (q_st q))) 2048) 0)).
  - destruct (Z.eqb (br_have (q_br q)) 0) eqn:Ehz; [exact I|].
    apply Z.eqb_neq in Ehz.
    destruct (gz_strz (Z.to_nat (br_have (q_br q))) (br_in (q_br q))
                (br_next (q_br q)) (br_have (q_br q)) 0)
      as [[cp ln]|] eqn:Egz.
    2:{ exfalso.
        destruct (gz_strz_some (Z.to_nat (br_have (q_br q))) (br_in (q_br q))
                    (br_next (q_br q)) (br_have (q_br q)) 0
                    ltac:(lia) ltac:(rewrite Z2Nat.id; lia))
          as (cp & ln & Heq).
        congruence. }
    pose proof (gz_strz_spec (Z.to_nat (br_have (q_br q))) (br_in (q_br q))
                  (br_next (q_br q)) (br_have (q_br q)) 0 cp ln
                  ltac:(lia) Egz) as Hcp.
    destruct (negb (Z.eqb (Z.land (h_flags (s_hdr (q_st q))) 512) 0)
              && negb (Z.eqb (Z.land (h_wrap (s_hdr (q_st q))) 4) 0));
      destruct (negb (Z.eqb ln 0)) eqn:Eln;
      try (cbn [arm_ok]; exact I).
    + apply (arm_ok_mono (qmode (qset_st (qset_br
               (qset_st q (set_check (q_st q)
                  (crc32_z (h_check (s_hdr (q_st q))) false 0
                     (br_slice (q_br q) cp))))
               (br_consume (q_br q) cp))
               (set_length (q_st (qset_br
                 (qset_st q (set_check (q_st q)
                    (crc32_z (h_check (s_hdr (q_st q))) false 0
                       (br_slice (q_br q) cp))))
                 (br_consume (q_br q) cp))) 0)) M_COMMENT) q).
      * apply rank2_le'
          with (m := M_NAME) (m' := M_COMMENT); [exact Hm | reflexivity |].
        cbn [inf_mrank].
        unfold inf_budget. bsimp. cbn [br_consume br_have br_bits]. lia.
      * apply arm_COMMENT; [|reflexivity].
        unfold q_pos. bsimp. cbn [br_consume br_have br_bits].
        repeat split; lia.
    + apply (arm_ok_mono (qmode (qset_st (qset_br q (br_consume (q_br q) cp))
               (set_length (q_st (qset_br q (br_consume (q_br q) cp))) 0))
               M_COMMENT) q).
      * apply rank2_le'
          with (m := M_NAME) (m' := M_COMMENT); [exact Hm | reflexivity |].
        cbn [inf_mrank].
        unfold inf_budget. bsimp. cbn [br_consume br_have br_bits]. lia.
      * apply arm_COMMENT; [|reflexivity].
        unfold q_pos. bsimp. cbn [br_consume br_have br_bits].
        repeat split; lia.
  - apply (arm_ok_mono (qmode (qset_st q (set_length (q_st q) 0)) M_COMMENT) q).
    + apply rank2_le'
        with (m := M_NAME) (m' := M_COMMENT); [exact Hm | reflexivity |].
      cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
    + apply arm_COMMENT; [|reflexivity].
      unfold q_pos. bsimp. repeat split; lia.
Qed.

(** [EXTRA]'s length premise is conditional on its own flag, so [EXLEN]'s
    flag-clear fallthrough can supply it vacuously. *)
Lemma arm_EXTRA :
  forall q, q_pos q -> q_mode q = M_EXTRA ->
    (Z.land (h_flags (s_hdr (q_st q))) 1024 <> 0 ->
       0 <= u_length (s_cur (q_st q))) ->
    arm_ok q (inf_EXTRA q).
Proof.
  intros q Hp Hm Hul. pose proof Hp as (Hh & Hb & Hl).
  unfold inf_EXTRA. cbv zeta.
  destruct (negb (Z.eqb (Z.land (h_flags (s_hdr (q_st q))) 1024) 0)) eqn:Efl.
  - apply Bool.negb_true_iff, Z.eqb_neq in Efl.
    specialize (Hul Efl).
    set (copy := if Z.ltb (br_have (q_br q)) (u_length (s_cur (q_st q)))
                 then br_have (q_br q) else u_length (s_cur (q_st q))).
    assert (Hcp : 0 <= copy <= br_have (q_br q)).
    { unfold copy. destruct (Z.ltb_spec (br_have (q_br q))
                               (u_length (s_cur (q_st q)))); lia. }
    destruct (negb (Z.eqb copy 0)) eqn:Ecz.
    + (* bytes consumed (and maybe crc'd) *)
      destruct (negb (Z.eqb (Z.land (h_flags (s_hdr (q_st q))) 512) 0)
                && negb (Z.eqb (Z.land (h_wrap (s_hdr (q_st q))) 4) 0));
        (destruct (negb (Z.eqb (u_length (s_cur (q_st _))) 0)) eqn:Eul;
         [cbn [arm_ok]; exact I|]).
      * eapply (arm_ok_mono _ q).
        2:{ apply arm_NAME; [|reflexivity].
            unfold q_pos. bsimp. cbn [br_consume br_have br_bits].
            repeat split; lia. }
        apply rank2_le'
          with (m := M_EXTRA) (m' := M_NAME); [exact Hm | reflexivity |].
        cbn [inf_mrank].
        unfold inf_budget. bsimp. cbn [br_consume br_have br_bits]. lia.
      * eapply (arm_ok_mono _ q).
        2:{ apply arm_NAME; [|reflexivity].
            unfold q_pos. bsimp. cbn [br_consume br_have br_bits].
            repeat split; lia. }
        apply rank2_le'
          with (m := M_EXTRA) (m' := M_NAME); [exact Hm | reflexivity |].
        cbn [inf_mrank].
        unfold inf_budget. bsimp. cbn [br_consume br_have br_bits]. lia.
    + (* copy = 0: nothing moves *)
      destruct (negb (Z.eqb (u_length (s_cur (q_st q))) 0)) eqn:Eul;
        [cbn [arm_ok]; exact I|].
      apply (arm_ok_mono (qmode (qset_st q (set_length (q_st q) 0)) M_NAME) q).
      * apply rank2_le'
          with (m := M_EXTRA) (m' := M_NAME); [exact Hm | reflexivity |].
        cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
      * apply arm_NAME; [|reflexivity].
        unfold q_pos. bsimp. repeat split; lia.
  - apply Bool.negb_false_iff, Z.eqb_eq in Efl.
    apply (arm_ok_mono (qmode (qset_st q (set_length (q_st q) 0)) M_NAME) q).
    + apply rank2_le'
        with (m := M_EXTRA) (m' := M_NAME); [exact Hm | reflexivity |].
      cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
    + apply arm_NAME; [|reflexivity].
      unfold q_pos. bsimp. repeat split; lia.
Qed.

Lemma arm_EXLEN :
  forall q, q_pos q -> q_mode q = M_EXLEN ->
    0 <= br_hold (q_br q) -> (forall j, 0 <= br_in (q_br q) j) ->
    arm_ok q (inf_EXLEN q).
Proof.
  intros q Hp Hm Hh0 Hin. pose proof Hp as (Hh & Hb & Hl).
  unfold inf_EXLEN.
  destruct (negb (Z.eqb (Z.land (h_flags (s_hdr (q_st q))) 1024) 0)) eqn:Efl.
  - destruct (inf_nb 16 (q_br q)) as [b|b] eqn:Enb; [|exact I].
    pose proof (inf_nb_hold 16 (q_br q) b Hh0 Hb Hin Enb) as Hhb.
    apply inf_nb_bud in Enb as (E1 & E2 & E3).
    (* both crc arms hand EXTRA the same three-field state shape *)
    destruct (negb (Z.eqb (Z.land (h_flags (s_hdr (q_st q))) 512) 0)
              && negb (Z.eqb (Z.land (h_wrap (s_hdr (q_st q))) 4) 0)).
    + eapply (arm_ok_mono _ q).
      2:{ apply arm_EXTRA; [|reflexivity|].
          - unfold q_pos. bsimp. repeat split; lia.
          - intros _. bsimp. lia. }
      apply rank2_le'
        with (m := M_EXLEN) (m' := M_EXTRA); [exact Hm | reflexivity |].
      cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
    + eapply (arm_ok_mono _ q).
      2:{ apply arm_EXTRA; [|reflexivity|].
          - unfold q_pos. bsimp. repeat split; lia.
          - intros _. bsimp. lia. }
      apply rank2_le'
        with (m := M_EXLEN) (m' := M_EXTRA); [exact Hm | reflexivity |].
      cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
  - apply Bool.negb_false_iff, Z.eqb_eq in Efl.
    apply (arm_ok_mono (qmode q M_EXTRA) q).
    + apply rank2_le'
        with (m := M_EXLEN) (m' := M_EXTRA); [exact Hm | reflexivity |].
      cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
    + apply arm_EXTRA; [|reflexivity|].
      * unfold q_pos. bsimp. repeat split; lia.
      * intros Habs. exfalso. apply Habs. bsimp. exact Efl.
Qed.

Lemma arm_OS :
  forall q, q_pos q -> q_mode q = M_OS ->
    (forall j, 0 <= br_in (q_br q) j) ->
    arm_ok q (inf_OS q).
Proof.
  intros q Hp Hm Hin. pose proof Hp as (Hh & Hb & Hl).
  unfold inf_OS.
  destruct (inf_nb 16 (q_br q)) as [b|b] eqn:Enb; [|exact I].
  pose proof (inf_nb_in 16 (q_br q) b Enb) as Ein.
  apply inf_nb_bud in Enb as (E1 & E2 & E3).
  destruct (negb (Z.eqb (Z.land (h_flags (s_hdr (q_st q))) 512) 0)
            && negb (Z.eqb (Z.land (h_wrap (s_hdr (q_st q))) 4) 0)).
  all: eapply (arm_ok_mono _ q);
    [ | apply arm_EXLEN;
        [ unfold q_pos; bsimp; repeat split; lia
        | reflexivity
        | bsimp; lia
        | bsimp; rewrite Ein; exact Hin ] ];
    apply rank2_le' with (m := M_OS) (m' := M_EXLEN);
    [ exact Hm | reflexivity
    | cbn [inf_mrank]; unfold inf_budget; bsimp; lia ].
Qed.

Lemma arm_TIME :
  forall q, q_pos q -> q_mode q = M_TIME ->
    (forall j, 0 <= br_in (q_br q) j) ->
    arm_ok q (inf_TIME q).
Proof.
  intros q Hp Hm Hin. pose proof Hp as (Hh & Hb & Hl).
  unfold inf_TIME. cbv zeta.
  destruct (inf_nb 32 (q_br q)) as [b|b] eqn:Enb; [|exact I].
  pose proof (inf_nb_in 32 (q_br q) b Enb) as Ein.
  apply inf_nb_bud in Enb as (E1 & E2 & E3).
  destruct (negb (Z.eqb (Z.land (h_flags (s_hdr (q_st q))) 512) 0)
            && negb (Z.eqb (Z.land (h_wrap (s_hdr (q_st q))) 4) 0)).
  all: eapply (arm_ok_mono _ q);
    [ | apply arm_OS;
        [ unfold q_pos; bsimp; repeat split; lia
        | reflexivity
        | bsimp; rewrite Ein; exact Hin ] ];
    apply rank2_le' with (m := M_TIME) (m' := M_OS);
    [ exact Hm | reflexivity
    | cbn [inf_mrank]; unfold inf_budget; bsimp; lia ].
Qed.

Lemma arm_FLAGS :
  forall q, q_pos q -> q_mode q = M_FLAGS ->
    (forall j, 0 <= br_in (q_br q) j) ->
    arm_ok q (inf_FLAGS q).
Proof.
  intros q Hp Hm Hin. pose proof Hp as (Hh & Hb & Hl).
  unfold inf_FLAGS. cbv zeta.
  destruct (inf_nb 16 (q_br q)) as [b|b] eqn:Enb; [|exact I].
  pose proof (inf_nb_in 16 (q_br q) b Enb) as Ein.
  apply inf_nb_bud in Enb as (E1 & E2 & E3).
  destruct (negb (Z.eqb (Z.land (h_flags _) 255) Z_DEFLATED)).
  { (* :674-677 unknown compression method -> BAD *)
    cbn [arm_ok]. split.
    - unfold q_pos. bsimp. repeat split; lia.
    - apply rank2_lt; [apply q_pos_bud, Hp|].
      unfold inf_budget at 1. bsimp. rewrite Hm. cbn [inf_mrank].
      unfold inf_budget. lia. }
  destruct (negb (Z.eqb (Z.land (h_flags _) 57344) 0)).
  { (* :679-682 reserved flag bits -> BAD *)
    cbn [arm_ok]. split.
    - unfold q_pos. bsimp. repeat split; lia.
    - apply rank2_lt; [apply q_pos_bud, Hp|].
      unfold inf_budget at 1. bsimp. rewrite Hm. cbn [inf_mrank].
      unfold inf_budget. lia. }
  destruct (negb (Z.eqb (Z.land (h_flags _) 512) 0)
            && negb (Z.eqb (Z.land (h_wrap _) 4) 0)).
  all: eapply (arm_ok_mono _ q);
    [ | apply arm_TIME;
        [ unfold q_pos; bsimp; repeat split; lia
        | reflexivity
        | bsimp; rewrite Ein; exact Hin ] ];
    apply rank2_le' with (m := M_FLAGS) (m' := M_TIME);
    [ exact Hm | reflexivity
    | cbn [inf_mrank]; unfold inf_budget; bsimp; lia ].
Qed.

(** ** LENEXT / DIST / DISTEXT (2026-08-19, Q4)

    The chain below LEN, minus LEN itself (which waits on the
    [inflate_fast] progress walk).  Every epsilon exit ASCENDS in
    [inf_mrank] (LENEXT 16201 -> DIST 16202 -> DISTEXT 16203 -> MATCH
    16204; BAD 16209), so no consumption is owed there; what the arms DO
    owe is that DROPBITS spends a NONNEGATIVE count — [u_extra] at the two
    ext arms (written as [Z.land _ 15] by LEN/DIST, arbitrary at a trip
    re-entry, hence a premise) and the fetched entry's [c_bits] at DIST
    (a property of the LIVE table: [TblSide]) — plus [arm_MATCH]'s entry
    contract threaded through.  [br_bits_of] is a masked read, so its
    range needs NO accumulator-sign premise ([Z.land_ones] + mod bounds
    hold for any argument). *)

(** The live-table contract: bit widths in [0,15], values 16-bit.  Real
    tables satisfy it by construction ([it_fill] writes [len - drop] with
    the [u16] value truncation; the fixed tables by computation). *)
Definition TblSide (t : ztbl) : Prop :=
  forall i, 0 <= c_bits (t i) <= 15 /\ 0 <= c_val (t i) < 65536.

(** The pointwise AMBIENT invariant of a codes array (2026-08-19, chain
    repair; spelling an earlier development run's): exactly the union of the ambient-facing
    per-entry conclusions ([TblSide] = conjuncts 1-2, [LcSide] = 1+3+4,
    the dext bound = 5).  [tnone] and every entry any build writes satisfy
    it; it is what the record-level contracts may assume of the slots a
    build did NOT write. *)
Definition amb_ok (t : ztbl) : Prop :=
  forall i,
    0 <= c_bits (t i) <= 15
    /\ 0 <= c_val (t i) < 65536
    /\ (Z.land (c_op (t i)) 32 <> 0 -> 1 <= c_bits (t i))
    /\ (c_op (t i) <> 0 -> Z.land (c_op (t i)) 32 = 0 ->
        Z.land (c_op (t i)) 64 = 0 -> 1 <= c_val (t i))
    /\ (Z.land (c_op (t i)) 16 <> 0 -> Z.land (c_op (t i)) 15 <= 13).

Lemma land_ones_range : forall a n, 0 <= n ->
  0 <= Z.land a (Z.shiftl 1 n - 1) < 2 ^ n.
Proof.
  intros a n Hn. rewrite Z.shiftl_1_l.
  replace (2 ^ n - 1) with (Z.ones n) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by exact Hn.
  apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.

Lemma bits_of_range : forall n b, 0 <= n ->
  0 <= br_bits_of n b < 2 ^ n.
Proof. intros n b Hn. unfold br_bits_of. now apply land_ones_range. Qed.

Lemma land15_range : forall x, 0 <= Z.land x 15 <= 15.
Proof.
  intros x.
  pose proof (land_ones_range x 4 ltac:(lia)) as H.
  cbn in H. lia.
Qed.

(** A successful fetch hands back an ENTRY OF ITS TABLE — what lets a
    caller's [TblSide] premise speak about the fetched code. *)
Lemma inf_fetch_go_entry :
  forall f t nb b h b', inf_fetch_go f t nb b = FetchOk h b' ->
    exists i, h = t i.
Proof.
  induction f as [|f IH]; intros t nb b h b' H; cbn [inf_fetch_go] in H;
    [discriminate|].
  destruct (Z.leb (c_bits (t (br_bits_of nb b))) (br_bits b)).
  - injection H as <- _. eexists. reflexivity.
  - destruct (br_pullbyte b) as [b1|]; [exact (IH _ _ _ _ _ H) | discriminate].
Qed.

Lemma inf_fetch2_go_entry :
  forall f t lst b h b', inf_fetch2_go f t lst b = FetchOk h b' ->
    exists i, h = t i.
Proof.
  induction f as [|f IH]; intros t lst b h b' H; cbn [inf_fetch2_go] in H;
    [discriminate|].
  match type of H with
  | context[Z.leb ?a ?bb] => destruct (Z.leb a bb)
  end.
  - injection H as <- _. eexists. reflexivity.
  - destruct (br_pullbyte b) as [b1|]; [exact (IH _ _ _ _ _ H) | discriminate].
Qed.

Lemma inf_decode_ok_facts :
  forall sub t rb b h b2 nb,
    (forall i, 0 <= c_bits (t i)) ->
    inf_decode sub t rb b = DecOk h b2 nb ->
    (exists i, h = t i) /\ 0 <= nb.
Proof.
  intros sub t rb b h b2 nb Hbits H. unfold inf_decode in H.
  destruct (inf_fetch t rb b) as [h0 b0|b0|] eqn:Ef; [|discriminate|discriminate].
  destruct (inf_fetch_go_entry _ _ _ _ _ _ Ef) as (i0 & ->).
  destruct (sub (t i0)).
  - destruct (inf_fetch2 t (t i0) b0) as [h1 b1|b1|] eqn:Ef2;
      [|discriminate|discriminate].
    destruct (inf_fetch2_go_entry _ _ _ _ _ _ Ef2) as (i1 & ->).
    inversion H; subst. split; [now eexists|].
    pose proof (Hbits i0). pose proof (Hbits i1). lia.
  - inversion H; subst. split; [now eexists|]. pose proof (Hbits i0). lia.
Qed.

Lemma arm_DISTEXT :
  forall q, q_pos q -> q_mode q = M_DISTEXT ->
    0 <= u_extra (s_cur (q_st q)) <= 15 ->
    1 <= u_length (s_cur (q_st q)) ->
    0 <= u_offset (s_cur (q_st q)) ->
    u_offset (s_cur (q_st q)) + Z.shiftl 1 (u_extra (s_cur (q_st q)))
      <= 4294967296 ->
    0 <= w_wnext (s_win (q_st q)) ->
    arm_ok q (inf_DISTEXT q).
Proof.
  intros q Hp Hm Hex Hul Hof Hob Hwn. pose proof Hp as (Hh & Hb & Hl).
  rewrite Z.shiftl_1_l in Hob.
  assert (Hp2 : 0 < 2 ^ (u_extra (s_cur (q_st q))))
    by (apply Z.pow_pos_nonneg; lia).
  assert (Hof32 : u_offset (s_cur (q_st q)) < 4294967296) by lia.
  unfold inf_DISTEXT. cbv zeta.
  destruct (Z.eqb (u_extra (s_cur (q_st q))) 0) eqn:Eez.
  - (* no extra bits: straight into MATCH *)
    apply Z.eqb_eq in Eez.
    eapply (arm_ok_mono _ q).
    2:{ apply arm_MATCH with (m := M_MATCH);
        [ unfold q_pos; bsimp; repeat split; lia
        | reflexivity
        | cbn [inf_mrank]; lia
        | bsimp; lia
        | bsimp; lia
        | bsimp; lia ]. }
    apply rank2_le' with (m := M_DISTEXT) (m' := M_MATCH);
      [ exact Hm | reflexivity
      | cbn [inf_mrank]; unfold inf_budget; bsimp; lia ].
  - destruct (inf_nb (u_extra (s_cur (q_st q))) (q_br q)) as [b|b] eqn:Enb;
      [|exact I].
    pose proof (inf_nb_ok _ _ _ Enb) as Enbge.
    pose proof (bits_of_range (u_extra (s_cur (q_st q))) b ltac:(lia)) as Ebo.
    apply inf_nb_bud in Enb as (E1 & E2 & E3).
    eapply (arm_ok_mono _ q).
    2:{ apply arm_MATCH with (m := M_MATCH);
        [ unfold q_pos; bsimp; repeat split; lia
        | reflexivity
        | cbn [inf_mrank]; lia
        | bsimp; lia
        | bsimp; lia
        | bsimp; lia ]. }
    apply rank2_le' with (m := M_DISTEXT) (m' := M_MATCH);
      [ exact Hm | reflexivity
      | cbn [inf_mrank]; unfold inf_budget; bsimp; lia ].
Qed.

Lemma arm_DIST :
  forall q, q_pos q -> q_mode q = M_DIST ->
    1 <= u_length (s_cur (q_st q)) ->
    0 <= w_wnext (s_win (q_st q)) ->
    TblSide (tbl_of (q_st q) (t_distcode (s_tab (q_st q)))) ->
    arm_ok q (inf_DIST q).
Proof.
  intros q Hp Hm Hul Hwn Htbl. pose proof Hp as (Hh & Hb & Hl).
  unfold inf_DIST. cbv zeta.
  destruct (inf_decode sub_dist (tbl_of (q_st q) (t_distcode (s_tab (q_st q))))
              (t_distbits (s_tab (q_st q))) (q_br q)) as [h b nb|b|] eqn:Edec.
  2: exact I.
  2:{ exfalso. exact (inf_decode_no_fuel _ _ _ _ Hh Edec). }
  destruct (inf_decode_ok_facts _ _ _ _ _ _ _
              (fun i => proj1 (proj1 (Htbl i)) ) Edec) as ((i0 & Hhe) & Hnb).
  pose proof (inf_decode_bud _ _ _ _ _ _ _ Edec) as (Ebud & Ehave).
  specialize (Ehave Hh).
  pose proof (inf_decode_bits_nonneg _ _ _ _ _ _ _ Edec) as Ebits.
  destruct (negb (Z.eqb (Z.land (c_op h) 64) 0)).
  - (* :1103-1106 invalid distance code -> BAD *)
    cbn [arm_ok]. split.
    + unfold q_pos. bsimp. repeat split; lia.
    + apply rank2_lt; [apply q_pos_bud, Hp|].
      unfold inf_budget at 1. bsimp. rewrite Hm. cbn [inf_mrank].
      unfold inf_budget. lia.
  - (* into DISTEXT *)
    pose proof (land15_range (c_op h)) as Hl15.
    assert (Hval : 0 <= c_val h < 65536)
      by (rewrite Hhe; exact (proj2 (Htbl i0))).
    assert (Hsh : Z.shiftl 1 (Z.land (c_op h) 15) <= 32768).
    { rewrite Z.shiftl_1_l.
      transitivity (2 ^ 15); [apply Z.pow_le_mono_r; lia | lia]. }
    eapply (arm_ok_mono _ q).
    2:{ apply arm_DISTEXT;
        [ unfold q_pos; bsimp; repeat split; lia
        | reflexivity
        | bsimp; lia
        | bsimp; lia
        | bsimp; lia
        | bsimp; lia
        | bsimp; lia ]. }
    apply rank2_le' with (m := M_DIST) (m' := M_DISTEXT);
      [ exact Hm | reflexivity
      | cbn [inf_mrank]; unfold inf_budget; bsimp; lia ].
Qed.

Lemma arm_LENEXT :
  forall q, q_pos q -> q_mode q = M_LENEXT ->
    0 <= u_extra (s_cur (q_st q)) <= 15 ->
    1 <= u_length (s_cur (q_st q)) ->
    0 <= w_wnext (s_win (q_st q)) ->
    TblSide (tbl_of (q_st q) (t_distcode (s_tab (q_st q)))) ->
    arm_ok q (inf_LENEXT q).
Proof.
  intros q Hp Hm Hex Hul Hwn Htbl. pose proof Hp as (Hh & Hb & Hl).
  unfold inf_LENEXT. cbv zeta.
  destruct (Z.eqb (u_extra (s_cur (q_st q))) 0) eqn:Eez.
  - (* no extra bits *)
    apply Z.eqb_eq in Eez.
    eapply (arm_ok_mono _ q).
    2:{ apply arm_DIST;
        [ unfold q_pos; bsimp; repeat split; lia
        | reflexivity
        | bsimp; lia
        | bsimp; lia
        | bsimp; exact Htbl ]. }
    apply rank2_le' with (m := M_LENEXT) (m' := M_DIST);
      [ exact Hm | reflexivity
      | cbn [inf_mrank]; unfold inf_budget; bsimp; lia ].
  - destruct (inf_nb (u_extra (s_cur (q_st q))) (q_br q)) as [b|b] eqn:Enb;
      [|exact I].
    pose proof (inf_nb_ok _ _ _ Enb) as Enbge.
    pose proof (bits_of_range (u_extra (s_cur (q_st q))) b ltac:(lia)) as Ebo.
    apply inf_nb_bud in Enb as (E1 & E2 & E3).
    eapply (arm_ok_mono _ q).
    2:{ apply arm_DIST;
        [ unfold q_pos; bsimp; repeat split; lia
        | reflexivity
        | bsimp; lia
        | bsimp; lia
        | bsimp; exact Htbl ]. }
    apply rank2_le' with (m := M_LENEXT) (m' := M_DIST);
      [ exact Hm | reflexivity
      | cbn [inf_mrank]; unfold inf_budget; bsimp; lia ].
Qed.

(** ** The inflate_fast BUDGET walk (2026-08-19, Q4 — towards [arm_LEN])

    The out-measure walk above gives output progress per fall-through
    trip; [arm_LEN] additionally needs the BIT-SIDE accounting, because
    the ExType exit can fire on the FIRST body (no output written) and
    [M_LEN -> M_TYPE] descends in [inf_mrank] — the exit must have
    consumed.  The budget mirrors the mode machine's:

        if_bud c s = 8 * (f_last c - f_in s) + f_bits s + (f_end c - f_out s)

    loads CONSERVE it (a byte moves from the input side to the
    accumulator), drops and puts SPEND it.  TRAP, and the reason every
    drop lemma below carries a range premise: [if_drop] stores
    [u32 (f_bits - n)] — an UNDER-DROP WRAPS the bit count to ~2^32 and
    the budget explodes, so each drop site must know [n <= f_bits], which
    the refill discipline supplies path-by-path. *)

Definition if_bud (c : IfCtx) (s : IfSt) : Z :=
  8 * (f_last c - f_in s) + f_bits s + (f_end c - f_out s).

Lemma if_load1_bud : forall c s,
  if_bud c (if_load1 c s) = if_bud c s
  /\ f_bits (if_load1 c s) = f_bits s + 8.
Proof. intros c s. unfold if_bud, if_load1. cbn [f_in f_out f_bits f_hold f_buf]. split; lia. Qed.

Lemma if_refill15_bud : forall c s,
  0 <= f_bits s <= 40 ->
  if_bud c (if_refill15 c s) = if_bud c s
  /\ 15 <= Z.max 15 (f_bits s) /\ f_bits (if_refill15 c s) <= f_bits s + 16
  /\ (f_bits s <= f_bits (if_refill15 c s))
  /\ (15 <= f_bits (if_refill15 c s) \/ 15 <= f_bits s)
  /\ 0 <= f_bits (if_refill15 c s) <= 40.
Proof.
  intros c s Hb. unfold if_refill15.
  destruct (Z.ltb_spec (f_bits s) 15) as [Hlt|Hge].
  - destruct (if_load1_bud c (if_load1 c s)) as (E2 & B2).
    destruct (if_load1_bud c s) as (E1 & B1).
    rewrite E2, E1, B2, B1. repeat split; lia.
  - repeat split; lia.
Qed.

(** The refilled reader has at least 15 bits — the form the drop sites
    consume. *)
Lemma if_refill15_ge15 : forall c s,
  0 <= f_bits s -> 15 <= f_bits (if_refill15 c s).
Proof.
  intros c s Hb. unfold if_refill15.
  destruct (Z.ltb_spec (f_bits s) 15) as [Hlt|Hge]; [|lia].
  cbn [if_load1 f_bits]. lia.
Qed.

Lemma if_drop_bud : forall c s n,
  0 <= n <= f_bits s -> f_bits s <= 40 ->
  if_bud c (if_drop n s) = if_bud c s - n
  /\ f_bits (if_drop n s) = f_bits s - n.
Proof.
  intros c s n Hn Hb. unfold if_bud, if_drop. cbn [f_in f_out f_bits f_hold f_buf].
  unfold u32. rewrite Z.mod_small by lia. split; lia.
Qed.

Lemma if_put_bud : forall c s v,
  if_bud c (if_put v s) = if_bud c s - 1
  /\ f_bits (if_put v s) = f_bits s.
Proof. intros c s v. unfold if_bud, if_put. cbn [f_in f_out f_bits f_hold f_buf]. split; lia. Qed.

Lemma if_copyn_bud : forall n c s r,
  if_bud c (fst (if_copyn n c s r)) = if_bud c s - Z.of_nat n
  /\ f_bits (fst (if_copyn n c s r)) = f_bits s.
Proof.
  induction n as [|n IH]; intros c s r; cbn [if_copyn fst].
  - split; lia.
  - destruct (IH c (if_put (if_read c s r) s) (if_bump r)) as (E & B).
    rewrite E, B.
    destruct (if_put_bud c s (if_read c s r)) as (E1 & B1).
    rewrite E1, B1. split; lia.
Qed.

Lemma if_copy3w_bud : forall f c s r len s2 r2 l2,
  if_copy3w f c s r len = Some (s2, r2, l2) ->
  if_bud c s2 <= if_bud c s /\ f_bits s2 = f_bits s.
Proof.
  induction f as [|f IH]; intros c s r len s2 r2 l2 H; cbn [if_copy3w] in H;
    [discriminate|].
  destruct (Z.ltb 2 len).
  - destruct (if_copyn 3 c s r) as [s1 r1] eqn:Ec.
    apply IH in H as (E & B).
    pose proof (if_copyn_bud 3 c s r) as (E1 & B1). rewrite Ec in E1, B1.
    cbn [fst] in E1, B1. split; lia.
  - injection H as <- <- <-. split; lia.
Qed.

Lemma if_copytail_bud : forall c s r len,
  if_bud c (if_copytail c s r len) <= if_bud c s
  /\ f_bits (if_copytail c s r len) = f_bits s.
Proof.
  intros c s r len. unfold if_copytail.
  destruct (Z.eqb len 0); [split; lia|].
  destruct (if_copyn 1 c s r) as [s1 r1] eqn:E1.
  pose proof (if_copyn_bud 1 c s r) as (Eb1 & Bb1). rewrite E1 in Eb1, Bb1.
  cbn [fst] in Eb1, Bb1.
  destruct (Z.ltb 1 len).
  - pose proof (if_copyn_bud 1 c s1 r1) as (Eb2 & Bb2). split; lia.
  - split; lia.
Qed.

Lemma if_copydirect_bud : forall c s r len s5,
  if_copydirect c s r len = Some s5 ->
  if_bud c s5 <= if_bud c s /\ f_bits s5 = f_bits s.
Proof.
  intros c s r len s5 H. unfold if_copydirect in H.
  destruct (if_copyn 3 c s r) as [s1 r1] eqn:E1.
  pose proof (if_copyn_bud 3 c s r) as (Eb1 & Bb1). rewrite E1 in Eb1, Bb1.
  cbn [fst] in Eb1, Bb1.
  destruct (if_copy3w copy_fuel c s1 r1 (u32 (len - 3)))
    as [[[s2 r2] l2]|] eqn:E2; [|discriminate].
  injection H as <-.
  apply if_copy3w_bud in E2 as (Eb2 & Bb2).
  pose proof (if_copytail_bud c s2 r2 l2) as (Eb3 & Bb3).
  split; lia.
Qed.

Lemma if_winphase_bud : forall c s dist op len s4 r4 len4,
  if_winphase c s dist op len = (s4, r4, len4) ->
  if_bud c s4 <= if_bud c s /\ f_bits s4 = f_bits s.
Proof.
  intros c s dist op len s4 r4 len4 H. unfold if_winphase in H.
  destruct (Z.eqb (f_wnext c) 0).
  - destruct (Z.ltb op len).
    + destruct (if_copyn (Z.to_nat op) c s (SrcWin (f_wsize c - op)))
        as [s1 r1] eqn:E1.
      pose proof (if_copyn_bud (Z.to_nat op) c s (SrcWin (f_wsize c - op)))
        as (Eb & Bb). rewrite E1 in Eb, Bb. cbn [fst] in Eb, Bb.
      injection H as <- <- <-. split; lia.
    + injection H as <- <- <-. split; lia.
  - destruct (Z.ltb (f_wnext c) op).
    + destruct (Z.ltb (u32 (op - f_wnext c)) len).
      * destruct (if_copyn (Z.to_nat (u32 (op - f_wnext c))) c s
                    (SrcWin (f_wsize c + f_wnext c - op))) as [s1 r1] eqn:E1.
        pose proof (if_copyn_bud (Z.to_nat (u32 (op - f_wnext c))) c s
                      (SrcWin (f_wsize c + f_wnext c - op))) as (Eb1 & Bb1).
        rewrite E1 in Eb1, Bb1. cbn [fst] in Eb1, Bb1.
        destruct (Z.ltb (f_wnext c) (u32 (len - u32 (op - f_wnext c)))) eqn:Eg2.
        { destruct (if_copyn (Z.to_nat (f_wnext c)) c s1 (SrcWin 0))
            as [s2 r2] eqn:E2.
          pose proof (if_copyn_bud (Z.to_nat (f_wnext c)) c s1 (SrcWin 0))
            as (Eb2 & Bb2). rewrite E2 in Eb2, Bb2. cbn [fst] in Eb2, Bb2.
          injection H as <- <- <-. split; lia. }
        { injection H as <- <- <-. split; lia. }
      * injection H as <- <- <-. split; lia.
    + destruct (Z.ltb op len).
      * destruct (if_copyn (Z.to_nat op) c s (SrcWin (f_wnext c - op)))
          as [s1 r1] eqn:E1.
        pose proof (if_copyn_bud (Z.to_nat op) c s (SrcWin (f_wnext c - op)))
          as (Eb & Bb). rewrite E1 in Eb, Bb. cbn [fst] in Eb, Bb.
        injection H as <- <- <-. split; lia.
      * injection H as <- <- <-. split; lia.
Qed.

(** Two-level FIT: a chain parent's and its child's widths fit in the
    15-bit refill together — [inflate_table] guarantees it by construction
    ([root + curr <= MAXBITS]); here it is the premise that keeps the
    second-level drop from underflowing. *)
(** RETIRED 2026-08-19 (chain repair; retention convention): the original
    table-wide spelling, kept as the named target for farm-ported
    consumers/refutations.  FALSE at reachable states.  Consumed by
    NOTHING in this tree. *)
Definition chain_fit_all (ch : Z -> bool) (t : ztbl) : Prop :=
  forall v s, ch (c_op (t v)) = true ->
    c_bits (t v) + c_bits (t (c_val (t v) + if_low (c_op (t v)) s)) <= 15.

(** RELATIVIZED 2026-08-19 (chain repair, an earlier development run/an earlier development run): guarded
    by the masked-image equation, like [lcode_two_level] — the table-wide
    form above is FALSE at reachable states (stale entries above a shrunk
    table; the installed LEN view reads the DIST table beyond [used1]).
    [m] is the site's mask ([f_lmask]/[f_dmask]; 511/31 fixed).
    MEASUREMENT-BIAS WARNING: see [lcode_two_level]'s definition-site
    note — the 560-entry census could not see these falsifiers (fresh
    single-block tables only); do not re-widen on census evidence. *)
Definition chain_fit (ch : Z -> bool) (t : ztbl) (m : Z) : Prop :=
  forall v x s, v = Z.land x m -> ch (c_op (t v)) = true ->
    c_bits (t v) + c_bits (t (c_val (t v) + if_low (c_op (t v)) s)) <= 15.

(** The budget through [if_dodist], entered at any dcode entry whose width
    the reader can cover: every non-fuel exit costs at least the entry's
    own width (and never refunds).  [BodyEob] does not occur in dodist. *)
Lemma if_dodist_bud :
  forall f c len s v,
    (forall i, 0 <= c_bits (f_dcode c i) <= 15) ->
    chain_fit dc_chains (f_dcode c) (f_dmask c) ->
    dcode_two_level c ->
    (dc_chains (c_op (f_dcode c v)) = true ->
       exists x, v = Z.land x (f_dmask c)) ->
    c_bits (f_dcode c v) <= f_bits s -> 0 <= f_bits s <= 40 ->
    (15 <= f_bits s \/ dc_chains (c_op (f_dcode c v)) = false) ->
    match if_dodist f c len s (f_dcode c v) with
    | BodyOk s' | BodyEob s' | BodyBad s' _ =>
        if_bud c s' <= if_bud c s - c_bits (f_dcode c v)
    | BodyFuel => True
    end.
Proof.
  induction f as [|f IH]; intros c len s v Hbits Hfit Htwo Hwv Hcov Hrange Hdisj;
    cbn [if_dodist]; [exact I|].
  pose proof (Hbits v) as Hv.
  (* the head drop *)
  pose proof (if_drop_bud c s (c_bits (f_dcode c v))
                ltac:(lia) ltac:(lia)) as (Ehd & Bhd).
  set (s1 := if_drop (c_bits (f_dcode c v)) s) in *.
  destruct (negb (Z.eqb (Z.land (c_op (f_dcode c v)) 16) 0)) eqn:E16.
  - (* distance base *)
    set (e := Z.land (c_op (f_dcode c v)) 15).
    assert (He : 0 <= e <= 15) by (unfold e; apply land15_range).
    (* the conditional double load: budget conserved, bits >= e after *)
    set (s2 := if Z.ltb (f_bits s1) e
               then let sa := if_load1 c s1 in
                    if Z.ltb (f_bits sa) e then if_load1 c sa else sa
               else s1).
    assert (Hs2 : if_bud c s2 = if_bud c s1
                  /\ e <= f_bits s2 /\ f_bits s2 <= 40).
    { unfold s2. destruct (Z.ltb_spec (f_bits s1) e) as [Hlt|Hge].
      - destruct (if_load1_bud c s1) as (E1 & B1).
        destruct (Z.ltb_spec (f_bits (if_load1 c s1)) e) as [Hlt2|Hge2].
        + destruct (if_load1_bud c (if_load1 c s1)) as (E2 & B2).
          rewrite E2, E1, B2, B1. repeat split; lia.
        + rewrite E1, B1 in *. repeat split; lia.
      - repeat split; lia. }
    destruct Hs2 as (Ebud2 & Hge2 & Hb2).
    pose proof (if_drop_bud c s2 e ltac:(lia) ltac:(lia)) as (Ehd3 & Bhd3).
    set (s3 := if_drop e s2) in *.
    destruct (Z.ltb (u32 (f_out s3 - f_beg c))
                (c_val (f_dcode c v) + if_low e s2)).
    + (* window side *)
      destruct (Z.ltb (f_whave c)
                  (u32 (c_val (f_dcode c v) + if_low e s2
                        - u32 (f_out s3 - f_beg c)))
                && negb (Z.eqb (f_sane c) 0)).
      * (* BodyBad DIST_FAR at s3 *)
        cbv iota. lia.
      * destruct (if_winphase c s3 (c_val (f_dcode c v) + if_low e s2)
                    (u32 (c_val (f_dcode c v) + if_low e s2
                          - u32 (f_out s3 - f_beg c))) len)
          as [[s4 r4] len4] eqn:Ewp.
        apply if_winphase_bud in Ewp as (Ewp & _).
        destruct (if_copy3w copy_fuel c s4 r4 len4)
          as [[[s5 r5] l5]|] eqn:E3w; [|exact I].
        apply if_copy3w_bud in E3w as (E3w & _).
        pose proof (if_copytail_bud c s5 r5 l5) as (Etl & _).
        cbv iota. lia.
    + (* direct side *)
      destruct (if_copydirect c s3
                  (SrcOut (f_out s3 - (c_val (f_dcode c v) + if_low e s2)))
                  len) as [s5|] eqn:Edir; [|exact I].
      apply if_copydirect_bud in Edir as (Edir & _).
      cbv iota. lia.
  - destruct (Z.eqb (Z.land (c_op (f_dcode c v)) 64) 0) eqn:E64.
    + (* second-level chain *)
      assert (Hch : dc_chains (c_op (f_dcode c v)) = true).
      { unfold dc_chains.
        apply Bool.negb_false_iff in E16. rewrite E16, E64. reflexivity. }
      destruct (Hwv Hch) as (xw & Hxw).
      pose proof (Hfit v xw s1 Hxw Hch) as Hf.
      assert (H15 : 15 <= f_bits s)
        by (destruct Hdisj as [H|H]; [exact H | congruence]).
      pose proof (Htwo v xw s1 Hxw Hch) as Hnc.
      pose proof (Hbits (c_val (f_dcode c v)
                         + if_low (c_op (f_dcode c v)) s1)) as Hcb.
      pose proof (IH c len s1
                    (c_val (f_dcode c v) + if_low (c_op (f_dcode c v)) s1)
                    Hbits Hfit Htwo ltac:(intros Hc; congruence)
                    ltac:(lia) ltac:(lia)
                    (or_intror Hnc)) as HR.
      destruct (if_dodist f c len s1
                  (f_dcode c (c_val (f_dcode c v)
                              + if_low (c_op (f_dcode c v)) s1)))
        as [s'|s'|s' m|]; cbv iota in HR |- *; try exact I;
        pose proof (Hbits (c_val (f_dcode c v)
                           + if_low (c_op (f_dcode c v)) s1)); lia.
    + (* BodyBad DIST_CODE at s1 *)
      cbv iota. lia.
Qed.

(** The budget through [if_dolen], entered (as its callers enter it) at a
    root lcode entry with a refilled reader.  Premise set mirrors
    [if_dolen_two_ok]'s relativised package, plus the WIDTH facts: the
    lcode's widths are STRICTLY positive (which is what pays the [-1] on
    every exit, end-of-block included — the zero-width-EOB epsilon), the
    dcode's nonnegative, and both tables' chain pairs fit in the refill.
    The single extra-bits load suffices because [lc_len_ok] bounds a
    length base's extra count by 8 ([c_val >= 3] and
    [c_val + 2^e - 1 <= 258] force [2^e <= 256]). *)
Lemma if_dolen_bud :
  forall f c s v n,
    (forall i, 0 <= i < n -> 1 <= c_bits (f_lcode c i) <= 15) ->
    (forall i, 0 <= c_bits (f_dcode c i) <= 15) ->
    chain_fit lc_chains (f_lcode c) (f_lmask c) ->
    chain_fit dc_chains (f_dcode c) (f_dmask c) ->
    lcode_two_level c -> dcode_two_level c ->
    (lc_chains (c_op (f_lcode c v)) = true ->
       exists x, v = Z.land x (f_lmask c)) ->
    lcode_len_bounded_upto c n -> lcode_index_range n c ->
    0 <= v < n ->
    c_bits (f_lcode c v) <= f_bits s ->
    0 <= f_bits s <= 40 ->
    (15 <= f_bits s \/ lc_chains (c_op (f_lcode c v)) = false) ->
    match if_dolen f c s (f_lcode c v) with
    | BodyOk s' | BodyEob s' | BodyBad s' _ =>
        if_bud c s' <= if_bud c s - 1
    | BodyFuel => True
    end.
Proof.
  induction f as [|f IH]; intros c s v n Hlb Hdb Hlf Hdf Hlt Hdt Hwv Hup Hir Hv
    Hcov Hrange Hdisj; cbn [if_dolen]; [exact I|].
  pose proof (Hlb v Hv) as Hvb.
  pose proof (if_drop_bud c s (c_bits (f_lcode c v))
                ltac:(lia) ltac:(lia)) as (Ehd & Bhd).
  set (s1 := if_drop (c_bits (f_lcode c v)) s) in *.
  destruct (Z.eqb (c_op (f_lcode c v)) 0) eqn:E0.
  - (* literal *)
    cbv iota.
    destruct (if_put_bud c s1 (u8 (c_val (f_lcode c v)))) as (Ep & _). lia.
  - destruct (negb (Z.eqb (Z.land (c_op (f_lcode c v)) 16) 0)) eqn:E16.
    + (* length base *)
      set (e := Z.land (c_op (f_lcode c v)) 15).
      assert (He : 0 <= e <= 15) by (unfold e; apply land15_range).
      assert (He8 : e <= 8).
      { pose proof (Hup v Hv) as Hok. unfold lc_len_ok in Hok.
        apply Bool.negb_true_iff, Z.eqb_neq in E16.
        destruct (Hok E16) as (H3 & H258). fold e in H258.
        destruct (Z.le_gt_cases e 8) as [H|H]; [exact H|]. exfalso.
        assert (H29 : 2 ^ 9 <= 2 ^ e) by (apply Z.pow_le_mono_r; lia).
        rewrite Z.shiftl_1_l in H258. cbn in H29. lia. }
      (* the pair (len, s2) *)
      destruct (Z.eqb e 0) eqn:Ee0.
      * (* e = 0: no extra bits *)
        apply Z.eqb_eq in Ee0. cbv iota.
        pose proof (if_refill15_bud c s1 ltac:(lia)) as (Erf & _ & Hle16 & Hmono & _ & Hrng).
        pose proof (if_refill15_ge15 c s1 ltac:(lia)) as Hge15.
        set (s3 := if_refill15 c s1) in *. clearbody s3.
        pose proof (Hdb (Z.land (f_hold s3) (f_dmask c))) as Hdc.
        assert (Hd15 : 15 <= f_bits s3
                       \/ dc_chains (c_op (f_dcode c
                            (Z.land (f_hold s3) (f_dmask c)))) = false)
          by (left; lia).
        pose proof (if_dodist_bud tbl_fuel c (c_val (f_lcode c v)) s3
                      (Z.land (f_hold s3) (f_dmask c))
                      Hdb Hdf Hdt ltac:(intros _; eexists; reflexivity)
                      ltac:(lia) ltac:(lia) Hd15) as HD.
        destruct (if_dodist tbl_fuel c (c_val (f_lcode c v)) s3
                    (f_dcode c (Z.land (f_hold s3) (f_dmask c))))
          as [s'|s'|s' m|]; cbv iota in HD |- *; try exact I; lia.
      * (* e > 0: one conditional load, then drop e *)
        apply Z.eqb_neq in Ee0. cbv iota.
        set (sa := if Z.ltb (f_bits s1) e then if_load1 c s1 else s1).
        assert (Hsa : if_bud c sa = if_bud c s1
                      /\ e <= f_bits sa /\ f_bits sa <= 40).
        { unfold sa. destruct (Z.ltb_spec (f_bits s1) e) as [Hltb|Hgeb].
          - destruct (if_load1_bud c s1) as (E1 & B1). rewrite E1, B1.
            repeat split; lia.
          - repeat split; lia. }
        destruct Hsa as (Esa & Hgea & Hba).
        pose proof (if_drop_bud c sa e ltac:(lia) ltac:(lia)) as (Ee & Be).
        set (s2 := if_drop e sa) in *.
        pose proof (if_refill15_bud c s2 ltac:(lia)) as (Erf & _ & _ & _ & _ & Hrng).
        pose proof (if_refill15_ge15 c s2 ltac:(lia)) as Hge15.
        set (s3 := if_refill15 c s2) in *. clearbody s3.
        pose proof (Hdb (Z.land (f_hold s3) (f_dmask c))) as Hdc.
        assert (Hd15 : 15 <= f_bits s3
                       \/ dc_chains (c_op (f_dcode c
                            (Z.land (f_hold s3) (f_dmask c)))) = false)
          by (left; lia).
        pose proof (if_dodist_bud tbl_fuel c
                      (c_val (f_lcode c v) + if_low e sa) s3
                      (Z.land (f_hold s3) (f_dmask c))
                      Hdb Hdf Hdt ltac:(intros _; eexists; reflexivity)
                      ltac:(lia) ltac:(lia) Hd15) as HD.
        destruct (if_dodist tbl_fuel c
                    (c_val (f_lcode c v) + if_low e sa) s3
                    (f_dcode c (Z.land (f_hold s3) (f_dmask c))))
          as [s'|s'|s' m|]; cbv iota in HD |- *; try exact I; lia.
    + destruct (Z.eqb (Z.land (c_op (f_lcode c v)) 64) 0) eqn:E64.
      * (* second-level length code *)
        assert (Hch : lc_chains (c_op (f_lcode c v)) = true).
        { unfold lc_chains.
          apply Bool.negb_true_iff in E0.
          apply Bool.negb_false_iff in E16.
          rewrite E0, E16, E64. reflexivity. }
        assert (H15 : 15 <= f_bits s)
          by (destruct Hdisj as [H|H]; [exact H | congruence]).
        destruct (Hwv Hch) as (xw & Hxw).
        pose proof (Hlf v xw s1 Hxw Hch) as Hf.
        pose proof (Hlt v xw s1 Hxw Hch) as Hnc.
        destruct Hir as (Hroot & Hchain).
        pose proof (Hchain v s1 Hv Hch) as Hvin.
        pose proof (Hlb _ Hvin) as Hcb.
        pose proof (IH c s1
                      (c_val (f_lcode c v) + if_low (c_op (f_lcode c v)) s1)
                      n Hlb Hdb Hlf Hdf Hlt Hdt ltac:(intros Hc; congruence) Hup
                      (conj Hroot Hchain) Hvin ltac:(lia) ltac:(lia)
                      (or_intror Hnc)) as HR.
        destruct (if_dolen f c s1
                    (f_lcode c (c_val (f_lcode c v)
                                + if_low (c_op (f_lcode c v)) s1)))
          as [s'|s'|s' m|]; cbv iota in HR |- *; try exact I; lia.
      * destruct (negb (Z.eqb (Z.land (c_op (f_lcode c v)) 32) 0)).
        { (* end of block *) cbv iota. lia. }
        { (* invalid *) cbv iota. lia. }
Qed.

(** The IN/BITS side of the same walks — what [if_finish]'s [u32]s need
    to unwrap: the exit reader's bit count stays in range and the input
    cursor overshoots its trip entry by at most the loads taken (2 in
    dodist, +1 in dolen, +2 in the caller's refill = the C's 5-byte
    read-ahead margin). *)

Lemma if_copyn_fin : forall n c s r,
  f_in (fst (if_copyn n c s r)) = f_in s.
Proof.
  induction n as [|n IH]; intros c s r; cbn [if_copyn fst]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma if_copy3w_fin : forall f c s r len s2 r2 l2,
  if_copy3w f c s r len = Some (s2, r2, l2) -> f_in s2 = f_in s.
Proof.
  induction f as [|f IH]; intros c s r len s2 r2 l2 H; cbn [if_copy3w] in H;
    [discriminate|].
  destruct (Z.ltb 2 len).
  - destruct (if_copyn 3 c s r) as [s1 r1] eqn:Ec.
    apply IH in H. pose proof (if_copyn_fin 3 c s r) as E1.
    rewrite Ec in E1. cbn [fst] in E1. lia.
  - injection H as <- <- <-. reflexivity.
Qed.

Lemma if_copytail_fin : forall c s r len,
  f_in (if_copytail c s r len) = f_in s.
Proof.
  intros c s r len. unfold if_copytail.
  destruct (Z.eqb len 0); [reflexivity|].
  destruct (if_copyn 1 c s r) as [s1 r1] eqn:E1.
  pose proof (if_copyn_fin 1 c s r) as F1. rewrite E1 in F1. cbn [fst] in F1.
  destruct (Z.ltb 1 len).
  - pose proof (if_copyn_fin 1 c s1 r1) as F2. lia.
  - lia.
Qed.

Lemma if_copydirect_fin : forall c s r len s5,
  if_copydirect c s r len = Some s5 -> f_in s5 = f_in s.
Proof.
  intros c s r len s5 H. unfold if_copydirect in H.
  destruct (if_copyn 3 c s r) as [s1 r1] eqn:E1.
  pose proof (if_copyn_fin 3 c s r) as F1. rewrite E1 in F1. cbn [fst] in F1.
  destruct (if_copy3w copy_fuel c s1 r1 (u32 (len - 3)))
    as [[[s2 r2] l2]|] eqn:E2; [|discriminate].
  injection H as <-.
  apply if_copy3w_fin in E2.
  pose proof (if_copytail_fin c s2 r2 l2). lia.
Qed.

Lemma if_winphase_fin : forall c s dist op len s4 r4 len4,
  if_winphase c s dist op len = (s4, r4, len4) -> f_in s4 = f_in s.
Proof.
  intros c s dist op len s4 r4 len4 H. unfold if_winphase in H.
  destruct (Z.eqb (f_wnext c) 0).
  - destruct (Z.ltb op len).
    + destruct (if_copyn (Z.to_nat op) c s (SrcWin (f_wsize c - op)))
        as [s1 r1] eqn:E1.
      pose proof (if_copyn_fin (Z.to_nat op) c s (SrcWin (f_wsize c - op)))
        as F1. rewrite E1 in F1. cbn [fst] in F1.
      injection H as <- <- <-. lia.
    + injection H as <- <- <-. reflexivity.
  - destruct (Z.ltb (f_wnext c) op).
    + destruct (Z.ltb (u32 (op - f_wnext c)) len).
      * destruct (if_copyn (Z.to_nat (u32 (op - f_wnext c))) c s
                    (SrcWin (f_wsize c + f_wnext c - op))) as [s1 r1] eqn:E1.
        pose proof (if_copyn_fin (Z.to_nat (u32 (op - f_wnext c))) c s
                      (SrcWin (f_wsize c + f_wnext c - op))) as F1.
        rewrite E1 in F1. cbn [fst] in F1.
        destruct (Z.ltb (f_wnext c) (u32 (len - u32 (op - f_wnext c)))).
        { destruct (if_copyn (Z.to_nat (f_wnext c)) c s1 (SrcWin 0))
            as [s2 r2] eqn:E2.
          pose proof (if_copyn_fin (Z.to_nat (f_wnext c)) c s1 (SrcWin 0))
            as F2. rewrite E2 in F2. cbn [fst] in F2.
          injection H as <- <- <-. lia. }
        { injection H as <- <- <-. lia. }
      * injection H as <- <- <-. reflexivity.
    + destruct (Z.ltb op len).
      * destruct (if_copyn (Z.to_nat op) c s (SrcWin (f_wnext c - op)))
          as [s1 r1] eqn:E1.
        pose proof (if_copyn_fin (Z.to_nat op) c s (SrcWin (f_wnext c - op)))
          as F1. rewrite E1 in F1. cbn [fst] in F1.
        injection H as <- <- <-. lia.
      * injection H as <- <- <-. reflexivity.
Qed.

Lemma if_dodist_fin :
  forall f c len s v,
    (forall i, 0 <= c_bits (f_dcode c i) <= 15) ->
    chain_fit dc_chains (f_dcode c) (f_dmask c) ->
    dcode_two_level c ->
    (dc_chains (c_op (f_dcode c v)) = true ->
       exists x, v = Z.land x (f_dmask c)) ->
    c_bits (f_dcode c v) <= f_bits s -> 0 <= f_bits s <= 40 ->
    (15 <= f_bits s \/ dc_chains (c_op (f_dcode c v)) = false) ->
    match if_dodist f c len s (f_dcode c v) with
    | BodyOk s' | BodyEob s' | BodyBad s' _ =>
        0 <= f_bits s' <= 40 /\ f_in s' <= f_in s + 2
    | BodyFuel => True
    end.
Proof.
  induction f as [|f IH]; intros c len s v Hbits Hfit Htwo Hwv Hcov Hrange Hdisj;
    cbn [if_dodist]; [exact I|].
  pose proof (Hbits v) as Hv.
  pose proof (if_drop_bud c s (c_bits (f_dcode c v))
                ltac:(lia) ltac:(lia)) as (Ehd & Bhd).
  assert (Fhd : f_in (if_drop (c_bits (f_dcode c v)) s) = f_in s)
    by reflexivity.
  set (s1 := if_drop (c_bits (f_dcode c v)) s) in *.
  destruct (negb (Z.eqb (Z.land (c_op (f_dcode c v)) 16) 0)) eqn:E16.
  - set (e := Z.land (c_op (f_dcode c v)) 15).
    assert (He : 0 <= e <= 15) by (unfold e; apply land15_range).
    set (s2 := if Z.ltb (f_bits s1) e
               then let sa := if_load1 c s1 in
                    if Z.ltb (f_bits sa) e then if_load1 c sa else sa
               else s1).
    assert (Hs2 : e <= f_bits s2 /\ f_bits s2 <= 40 /\ f_in s2 <= f_in s1 + 2).
    { unfold s2. destruct (Z.ltb_spec (f_bits s1) e) as [Hlt|Hge].
      - destruct (if_load1_bud c s1) as (_ & B1).
        destruct (Z.ltb_spec (f_bits (if_load1 c s1)) e) as [Hlt2|Hge2].
        + destruct (if_load1_bud c (if_load1 c s1)) as (_ & B2).
          cbn [if_load1 f_in] in *. repeat split; try lia.
        + cbn [if_load1 f_in] in *. repeat split; lia.
      - repeat split; lia. }
    destruct Hs2 as (Hge2 & Hb2 & Hf2).
    pose proof (if_drop_bud c s2 e ltac:(lia) ltac:(lia)) as (_ & Bhd3).
    assert (Fhd3 : f_in (if_drop e s2) = f_in s2) by reflexivity.
    set (s3 := if_drop e s2) in *.
    destruct (Z.ltb (u32 (f_out s3 - f_beg c))
                (c_val (f_dcode c v) + if_low e s2)).
    + destruct (Z.ltb (f_whave c)
                  (u32 (c_val (f_dcode c v) + if_low e s2
                        - u32 (f_out s3 - f_beg c)))
                && negb (Z.eqb (f_sane c) 0)).
      * cbv iota. repeat split; lia.
      * destruct (if_winphase c s3 (c_val (f_dcode c v) + if_low e s2)
                    (u32 (c_val (f_dcode c v) + if_low e s2
                          - u32 (f_out s3 - f_beg c))) len)
          as [[s4 r4] len4] eqn:Ewp.
        pose proof (if_winphase_fin _ _ _ _ _ _ _ _ Ewp) as Fwp.
        apply if_winphase_bud in Ewp as (_ & Bwp).
        destruct (if_copy3w copy_fuel c s4 r4 len4)
          as [[[s5 r5] l5]|] eqn:E3w; [|exact I].
        pose proof (if_copy3w_fin _ _ _ _ _ _ _ _ E3w) as F3w.
        apply if_copy3w_bud in E3w as (_ & B3w).
        pose proof (if_copytail_fin c s5 r5 l5) as Ftl.
        pose proof (if_copytail_bud c s5 r5 l5) as (_ & Btl).
        cbv iota. repeat split; lia.
    + destruct (if_copydirect c s3
                  (SrcOut (f_out s3 - (c_val (f_dcode c v) + if_low e s2)))
                  len) as [s5|] eqn:Edir; [|exact I].
      pose proof (if_copydirect_fin _ _ _ _ _ Edir) as Fdir.
      apply if_copydirect_bud in Edir as (_ & Bdir).
      cbv iota. repeat split; lia.
  - destruct (Z.eqb (Z.land (c_op (f_dcode c v)) 64) 0) eqn:E64.
    + assert (Hch : dc_chains (c_op (f_dcode c v)) = true).
      { unfold dc_chains.
        apply Bool.negb_false_iff in E16. rewrite E16, E64. reflexivity. }
      assert (H15 : 15 <= f_bits s)
        by (destruct Hdisj as [H|H]; [exact H | congruence]).
      destruct (Hwv Hch) as (xw & Hxw).
      pose proof (Hfit v xw s1 Hxw Hch) as Hf.
      pose proof (Htwo v xw s1 Hxw Hch) as Hnc.
      pose proof (Hbits (c_val (f_dcode c v)
                         + if_low (c_op (f_dcode c v)) s1)) as Hcb.
      pose proof (IH c len s1
                    (c_val (f_dcode c v) + if_low (c_op (f_dcode c v)) s1)
                    Hbits Hfit Htwo ltac:(intros Hc; congruence)
                    ltac:(lia) ltac:(lia)
                    (or_intror Hnc)) as HR.
      destruct (if_dodist f c len s1
                  (f_dcode c (c_val (f_dcode c v)
                              + if_low (c_op (f_dcode c v)) s1)))
        as [s'|s'|s' m|]; cbv iota in HR |- *; try exact I;
        destruct HR; split; lia.
    + cbv iota. repeat split; lia.
Qed.

Lemma if_dolen_fin :
  forall f c s v n,
    (forall i, 0 <= i < n -> 1 <= c_bits (f_lcode c i) <= 15) ->
    (forall i, 0 <= c_bits (f_dcode c i) <= 15) ->
    chain_fit lc_chains (f_lcode c) (f_lmask c) ->
    chain_fit dc_chains (f_dcode c) (f_dmask c) ->
    lcode_two_level c -> dcode_two_level c ->
    (lc_chains (c_op (f_lcode c v)) = true ->
       exists x, v = Z.land x (f_lmask c)) ->
    lcode_len_bounded_upto c n -> lcode_index_range n c ->
    0 <= v < n ->
    c_bits (f_lcode c v) <= f_bits s ->
    0 <= f_bits s <= 40 ->
    (15 <= f_bits s \/ lc_chains (c_op (f_lcode c v)) = false) ->
    match if_dolen f c s (f_lcode c v) with
    | BodyOk s' | BodyEob s' | BodyBad s' _ =>
        0 <= f_bits s' <= 40 /\ f_in s' <= f_in s + 5
    | BodyFuel => True
    end.
Proof.
  induction f as [|f IH]; intros c s v n Hlb Hdb Hlf Hdf Hlt Hdt Hwv Hup Hir Hv
    Hcov Hrange Hdisj; cbn [if_dolen]; [exact I|].
  pose proof (Hlb v Hv) as Hvb.
  pose proof (if_drop_bud c s (c_bits (f_lcode c v))
                ltac:(lia) ltac:(lia)) as (Ehd & Bhd).
  assert (Fhd : f_in (if_drop (c_bits (f_lcode c v)) s) = f_in s)
    by reflexivity.
  set (s1 := if_drop (c_bits (f_lcode c v)) s) in *.
  destruct (Z.eqb (c_op (f_lcode c v)) 0) eqn:E0.
  - cbv iota. cbn [if_put f_bits f_in]. repeat split; lia.
  - destruct (negb (Z.eqb (Z.land (c_op (f_lcode c v)) 16) 0)) eqn:E16.
    + set (e := Z.land (c_op (f_lcode c v)) 15).
      assert (He : 0 <= e <= 15) by (unfold e; apply land15_range).
      assert (He8 : e <= 8).
      { pose proof (Hup v Hv) as Hok. unfold lc_len_ok in Hok.
        apply Bool.negb_true_iff, Z.eqb_neq in E16.
        destruct (Hok E16) as (H3 & H258). fold e in H258.
        destruct (Z.le_gt_cases e 8) as [H|H]; [exact H|]. exfalso.
        assert (H29 : 2 ^ 9 <= 2 ^ e) by (apply Z.pow_le_mono_r; lia).
        rewrite Z.shiftl_1_l in H258. cbn in H29. lia. }
      destruct (Z.eqb e 0) eqn:Ee0.
      * apply Z.eqb_eq in Ee0. cbv iota.
        pose proof (if_refill15_bud c s1 ltac:(lia)) as (_ & _ & _ & _ & _ & Hrng).
        pose proof (if_refill15_ge15 c s1 ltac:(lia)) as Hge15.
        assert (Frf : f_in (if_refill15 c s1) <= f_in s1 + 2).
        { unfold if_refill15. destruct (Z.ltb (f_bits s1) 15);
            cbn [if_load1 f_in]; lia. }
        set (s3 := if_refill15 c s1) in *. clearbody s3.
        pose proof (Hdb (Z.land (f_hold s3) (f_dmask c))) as Hdc.
        assert (Hd15 : 15 <= f_bits s3
                       \/ dc_chains (c_op (f_dcode c
                            (Z.land (f_hold s3) (f_dmask c)))) = false)
          by (left; lia).
        pose proof (if_dodist_fin tbl_fuel c (c_val (f_lcode c v)) s3
                      (Z.land (f_hold s3) (f_dmask c))
                      Hdb Hdf Hdt ltac:(intros _; eexists; reflexivity)
                      ltac:(lia) ltac:(lia) Hd15) as HD.
        destruct (if_dodist tbl_fuel c (c_val (f_lcode c v)) s3
                    (f_dcode c (Z.land (f_hold s3) (f_dmask c))))
          as [s'|s'|s' m|]; cbv iota in HD |- *; try exact I;
          destruct HD; split; lia.
      * apply Z.eqb_neq in Ee0. cbv iota.
        set (sa := if Z.ltb (f_bits s1) e then if_load1 c s1 else s1).
        assert (Hsa : e <= f_bits sa /\ f_bits sa <= 40
                      /\ f_in sa <= f_in s1 + 1).
        { unfold sa. destruct (Z.ltb_spec (f_bits s1) e) as [Hltb|Hgeb].
          - destruct (if_load1_bud c s1) as (_ & B1).
            cbn [if_load1 f_in] in *. repeat split; lia.
          - repeat split; lia. }
        destruct Hsa as (Hgea & Hba & Hfa).
        pose proof (if_drop_bud c sa e ltac:(lia) ltac:(lia)) as (_ & Be).
        assert (Fe : f_in (if_drop e sa) = f_in sa) by reflexivity.
        set (s2 := if_drop e sa) in *.
        pose proof (if_refill15_bud c s2 ltac:(lia)) as (_ & _ & _ & _ & _ & Hrng).
        pose proof (if_refill15_ge15 c s2 ltac:(lia)) as Hge15.
        assert (Frf : f_in (if_refill15 c s2) <= f_in s2 + 2).
        { unfold if_refill15. destruct (Z.ltb (f_bits s2) 15);
            cbn [if_load1 f_in]; lia. }
        set (s3 := if_refill15 c s2) in *. clearbody s3.
        pose proof (Hdb (Z.land (f_hold s3) (f_dmask c))) as Hdc.
        assert (Hd15 : 15 <= f_bits s3
                       \/ dc_chains (c_op (f_dcode c
                            (Z.land (f_hold s3) (f_dmask c)))) = false)
          by (left; lia).
        pose proof (if_dodist_fin tbl_fuel c
                      (c_val (f_lcode c v) + if_low e sa) s3
                      (Z.land (f_hold s3) (f_dmask c))
                      Hdb Hdf Hdt ltac:(intros _; eexists; reflexivity)
                      ltac:(lia) ltac:(lia) Hd15) as HD.
        destruct (if_dodist tbl_fuel c
                    (c_val (f_lcode c v) + if_low e sa) s3
                    (f_dcode c (Z.land (f_hold s3) (f_dmask c))))
          as [s'|s'|s' m|]; cbv iota in HD |- *; try exact I;
          destruct HD; split; lia.
    + destruct (Z.eqb (Z.land (c_op (f_lcode c v)) 64) 0) eqn:E64.
      * assert (Hch : lc_chains (c_op (f_lcode c v)) = true).
        { unfold lc_chains.
          apply Bool.negb_true_iff in E0.
          apply Bool.negb_false_iff in E16.
          rewrite E0, E16, E64. reflexivity. }
        assert (H15 : 15 <= f_bits s)
          by (destruct Hdisj as [H|H]; [exact H | congruence]).
        destruct (Hwv Hch) as (xw & Hxw).
        pose proof (Hlf v xw s1 Hxw Hch) as Hf.
        pose proof (Hlt v xw s1 Hxw Hch) as Hnc.
        destruct Hir as (Hroot & Hchain).
        pose proof (Hchain v s1 Hv Hch) as Hvin.
        pose proof (Hlb _ Hvin) as Hcb.
        pose proof (IH c s1
                      (c_val (f_lcode c v) + if_low (c_op (f_lcode c v)) s1)
                      n Hlb Hdb Hlf Hdf Hlt Hdt ltac:(intros Hc; congruence) Hup
                      (conj Hroot Hchain) Hvin ltac:(lia) ltac:(lia)
                      (or_intror Hnc)) as HR.
        destruct (if_dolen f c s1
                    (f_lcode c (c_val (f_lcode c v)
                                + if_low (c_op (f_lcode c v)) s1)))
          as [s'|s'|s' m|]; cbv iota in HR |- *; try exact I;
          destruct HR; split; lia.
      * destruct (negb (Z.eqb (Z.land (c_op (f_lcode c v)) 32) 0));
          cbv iota; repeat split; lia.
Qed.


(** ** The inflate_fast CONSUMED-CURSOR walk (2026-08-19, Q4 continuation)

    The budget walk pays the rank; [if_finish]'s [u32]s need the OTHER
    direction: how far past [last] the input cursor can be pushed.  The
    consumed cursor is [C s = 8 * f_in s - f_bits s] (bits taken off the
    stream): loads CONSERVE it ([f_in] +1 against [f_bits] +8) and a drop
    of [n] adds exactly [n].  Per trip the drops are: the length code's
    width, its extras, the distance code's width, its extras — bounded by
    15 + 5 + 15 + 13 = 48 under the two NEW table premises ([lext]/[dext]
    literals; [lc_len_ok]'s derived [extra <= 8] is NOT tight enough:
    15+8+15+15 = 53 would put the consumed cursor one byte past the C's
    5-byte read-ahead margin and [if_finish]'s [u32 (5 + last - i)] would
    wrap).  A chained pair collapses to one 15 via [chain_fit].

    The same walk carries the OUT upper bound (a trip writes at most 258
    bytes: one literal, or a match of [len <= 258] by [lc_len_ok]), which
    is what keeps [if_finish]'s [u32 (257 + (end - out))] from wrapping
    below zero, and [f_in]'s monotonicity (loads only), which bounds the
    epilogue give-back. *)

Lemma if_refill15_cur : forall c s,
  8 * f_in (if_refill15 c s) - f_bits (if_refill15 c s) = 8 * f_in s - f_bits s
  /\ f_in s <= f_in (if_refill15 c s)
  /\ f_out (if_refill15 c s) = f_out s.
Proof.
  intros c s. unfold if_refill15.
  destruct (Z.ltb (f_bits s) 15); [|repeat split; lia].
  cbn [if_load1 f_in f_bits f_out]. repeat split; lia.
Qed.

(** [dodist_body] (everything after the distance is decoded) only copies:
    it conserves the input side exactly, and on [BodyOk] writes exactly
    [len].  The [BodyBad] state is the input state itself. *)
Lemma dodist_body_walk :
  forall c len s3 dist,
    0 <= f_wnext c -> 3 <= len <= 258 ->
    match dodist_body c len s3 dist with
    | BodyOk s' => f_in s' = f_in s3 /\ f_bits s' = f_bits s3
                   /\ f_out s' = f_out s3 + len
    | BodyEob _ => False
    | BodyBad s' _ => s' = s3
    | BodyFuel => False
    end.
Proof.
  intros c len s3 dist Hwn Hlen. unfold dodist_body. cbv zeta.
  destruct (Z.ltb (u32 (f_out s3 - f_beg c)) dist) eqn:Eod.
  - destruct (Z.ltb (f_whave c) (u32 (dist - u32 (f_out s3 - f_beg c)))
              && negb (Z.eqb (f_sane c) 0)) eqn:Ebad; [reflexivity|].
    destruct (if_winphase c s3 dist (u32 (dist - u32 (f_out s3 - f_beg c))) len)
      as [[s4 r4] len4] eqn:EW.
    pose proof EW as EWfin. apply if_winphase_fin in EWfin.
    pose proof EW as EWbud. apply if_winphase_bud in EWbud as (_ & EWbits).
    destruct (if_winphase_out c s3 dist
                (u32 (dist - u32 (f_out s3 - f_beg c))) len s4 r4 len4
                (u32_range _) Hwn ltac:(lia) EW) as [Hout4 Hlen4].
    destruct (if_copy3w_spec copy_fuel c s4 r4 len4 ltac:(lia)
                ltac:(unfold copy_fuel; cbn [Z.of_nat]; lia) ltac:(lia))
      as [s5 [r5 [l5 [Heq [Hout5 Hl5]]]]].
    rewrite Heq. cbv beta iota.
    pose proof Heq as Hfin5. apply if_copy3w_fin in Hfin5.
    pose proof Heq as Hbud5. apply if_copy3w_bud in Hbud5 as (_ & Hbits5).
    pose proof (if_copytail_fin c s5 r5 l5) as Ftl.
    pose proof (if_copytail_bud c s5 r5 l5) as (_ & Btl).
    rewrite (if_copytail_out c s5 r5 l5 Hl5).
    repeat split; lia.
  - destruct (if_copydirect_ok c s3 (SrcOut (f_out s3 - dist)) len Hlen)
      as [s5 [Heq Hout5]].
    rewrite Heq. cbv beta iota.
    pose proof Heq as Hfin. apply if_copydirect_fin in Hfin.
    pose proof Heq as Hbud. apply if_copydirect_bud in Hbud as (_ & Hbits).
    repeat split; lia.
Qed.

(** One [dodist] level that does not chain: the drops are the entry's own
    width plus its extras, and the extras are bounded by the [dext]
    literal premise (13, codes 28-29), NOT by anything derivable here. *)
Lemma if_dodist_nochain_cw :
  forall k c len s h,
    dc_chains (c_op h) = false ->
    (Z.land (c_op h) 16 <> 0 -> Z.land (c_op h) 15 <= 13) ->
    0 <= c_bits h <= f_bits s -> f_bits s <= 40 ->
    0 <= f_wnext c -> 3 <= len <= 258 ->
    match if_dodist (S k) c len s h with
    | BodyOk s' | BodyEob s' | BodyBad s' _ =>
        8 * f_in s' - f_bits s' <= 8 * f_in s - f_bits s + c_bits h + 13
        /\ f_out s <= f_out s' <= f_out s + len
        /\ f_in s <= f_in s'
    | BodyFuel => True
    end.
Proof.
  intros k c len s h Hnc Hde Hcb Hb40 Hwn Hlen.
  destruct (Z.eqb (Z.land (c_op h) 16) 0) eqn:E16.
  - (* not a distance base; [dc_chains] false forces the [op & 64] exit *)
    unfold dc_chains in Hnc. rewrite E16 in Hnc. cbn [andb] in Hnc.
    cbn [if_dodist]. rewrite E16, Hnc. cbn [negb].
    cbn [if_drop f_in f_bits f_out].
    unfold u32. rewrite Z.mod_small by lia.
    repeat split; lia.
  - (* distance base *)
    rewrite (if_dodist_unfold_base k c len s h E16).
    assert (He13 : Z.land (c_op h) 15 <= 13)
      by (apply Hde; apply Z.eqb_neq in E16; exact E16).
    pose proof (land15_range (c_op h)) as He.
    set (e := Z.land (c_op h) 15) in *.
    pose proof (if_drop_bud c s (c_bits h) ltac:(lia) ltac:(lia)) as (_ & B1).
    assert (F1 : f_in (if_drop (c_bits h) s) = f_in s) by reflexivity.
    assert (O1 : f_out (if_drop (c_bits h) s) = f_out s) by reflexivity.
    set (s1 := if_drop (c_bits h) s) in *.
    assert (Hs2 : e <= f_bits (dodist_pull c e s1)
                  /\ f_bits (dodist_pull c e s1) <= 40
                  /\ 8 * f_in (dodist_pull c e s1) - f_bits (dodist_pull c e s1)
                     = 8 * f_in s1 - f_bits s1
                  /\ f_in s1 <= f_in (dodist_pull c e s1)
                  /\ f_out (dodist_pull c e s1) = f_out s1).
    { unfold dodist_pull. destruct (Z.ltb_spec (f_bits s1) e) as [Hlt|Hge].
      - cbv zeta. destruct (if_load1_bud c s1) as (_ & Ba).
        destruct (Z.ltb_spec (f_bits (if_load1 c s1)) e) as [Hlt2|Hge2].
        + destruct (if_load1_bud c (if_load1 c s1)) as (_ & Bb).
          cbn [if_load1 f_in f_out f_bits] in *. repeat split; lia.
        + cbn [if_load1 f_in f_out f_bits] in *. repeat split; lia.
      - repeat split; lia. }
    destruct Hs2 as (Hge2 & Hb2 & C2 & I2 & O2).
    set (s2 := dodist_pull c e s1) in *.
    pose proof (if_drop_bud c s2 e ltac:(lia) ltac:(lia)) as (_ & B3).
    assert (F3 : f_in (if_drop e s2) = f_in s2) by reflexivity.
    assert (O3 : f_out (if_drop e s2) = f_out s2) by reflexivity.
    set (s3 := if_drop e s2) in *.
    pose proof (dodist_body_walk c len s3 (c_val h + if_low e s2) Hwn Hlen) as W.
    destruct (dodist_body c len s3 (c_val h + if_low e s2))
      as [s'|s'|s' m0|].
    + destruct W as (Wi & Wb & Wo). repeat split; lia.
    + contradiction.
    + rewrite W. repeat split; lia.
    + exact I.
Qed.

(** Two levels ARE all levels ([dcode_two_level]); a chained pair's widths
    collapse to one 15 via [chain_fit], so the level-uniform bound is
    15 + 13 = 28. *)
Lemma if_dodist_cw :
  forall k c len s v,
    (forall i, 0 <= c_bits (f_dcode c i) <= 15) ->
    (forall i, Z.land (c_op (f_dcode c i)) 16 <> 0 ->
       Z.land (c_op (f_dcode c i)) 15 <= 13) ->
    chain_fit dc_chains (f_dcode c) (f_dmask c) ->
    dcode_two_level c ->
    (dc_chains (c_op (f_dcode c v)) = true ->
       exists x, v = Z.land x (f_dmask c)) ->
    c_bits (f_dcode c v) <= f_bits s -> 0 <= f_bits s <= 40 ->
    (15 <= f_bits s \/ dc_chains (c_op (f_dcode c v)) = false) ->
    0 <= f_wnext c -> 3 <= len <= 258 ->
    match if_dodist (S (S k)) c len s (f_dcode c v) with
    | BodyOk s' | BodyEob s' | BodyBad s' _ =>
        8 * f_in s' - f_bits s' <= 8 * f_in s - f_bits s + 28
        /\ f_out s <= f_out s' <= f_out s + len
        /\ f_in s <= f_in s'
    | BodyFuel => True
    end.
Proof.
  intros k c len s v Hdb Hde Hfit Htwo Hwv Hcov Hrange Hdisj Hwn Hlen.
  destruct (dc_chains (c_op (f_dcode c v))) eqn:Hch.
  - (* chain: one step, then the child does not chain *)
    assert (H15 : 15 <= f_bits s)
      by (destruct Hdisj as [H|H]; [exact H | congruence]).
    rewrite (if_dodist_chain_step (S k) c len s _ Hch).
    destruct (Hwv eq_refl) as (xw & Hxw).
    pose proof (Hfit v xw (if_drop (c_bits (f_dcode c v)) s) Hxw Hch) as Hf.
    pose proof (Htwo v xw (if_drop (c_bits (f_dcode c v)) s) Hxw Hch) as Hnc.
    pose proof (Hdb v) as Hv.
    pose proof (Hdb (c_val (f_dcode c v)
                     + if_low (c_op (f_dcode c v))
                         (if_drop (c_bits (f_dcode c v)) s))) as Hcbc.
    pose proof (if_drop_bud c s (c_bits (f_dcode c v))
                  ltac:(lia) ltac:(lia)) as (_ & B1).
    assert (F1 : f_in (if_drop (c_bits (f_dcode c v)) s) = f_in s)
      by reflexivity.
    assert (O1 : f_out (if_drop (c_bits (f_dcode c v)) s) = f_out s)
      by reflexivity.
    pose proof (if_dodist_nochain_cw k c len (if_drop (c_bits (f_dcode c v)) s)
                  (f_dcode c (c_val (f_dcode c v)
                              + if_low (c_op (f_dcode c v))
                                  (if_drop (c_bits (f_dcode c v)) s)))
                  Hnc (Hde _) ltac:(lia) ltac:(lia) Hwn Hlen) as W.
    destruct (if_dodist (S k) c len (if_drop (c_bits (f_dcode c v)) s)
                (f_dcode c (c_val (f_dcode c v)
                            + if_low (c_op (f_dcode c v))
                                (if_drop (c_bits (f_dcode c v)) s))))
      as [s'|s'|s' m0|]; [ | | | exact I];
      destruct W as (W1 & W2 & W3); repeat split; lia.
  - pose proof (Hdb v) as Hv.
    pose proof (if_dodist_nochain_cw (S k) c len s (f_dcode c v)
                  Hch (Hde v) ltac:(lia) ltac:(lia) Hwn Hlen) as W.
    destruct (if_dodist (S (S k)) c len s (f_dcode c v))
      as [s'|s'|s' m0|]; [ | | | exact I];
      destruct W as (W1 & W2 & W3); repeat split; lia.
Qed.

Corollary if_dodist_cw_tbl :
  forall c len s v,
    (forall i, 0 <= c_bits (f_dcode c i) <= 15) ->
    (forall i, Z.land (c_op (f_dcode c i)) 16 <> 0 ->
       Z.land (c_op (f_dcode c i)) 15 <= 13) ->
    chain_fit dc_chains (f_dcode c) (f_dmask c) ->
    dcode_two_level c ->
    (dc_chains (c_op (f_dcode c v)) = true ->
       exists x, v = Z.land x (f_dmask c)) ->
    c_bits (f_dcode c v) <= f_bits s -> 0 <= f_bits s <= 40 ->
    (15 <= f_bits s \/ dc_chains (c_op (f_dcode c v)) = false) ->
    0 <= f_wnext c -> 3 <= len <= 258 ->
    match if_dodist tbl_fuel c len s (f_dcode c v) with
    | BodyOk s' | BodyEob s' | BodyBad s' _ =>
        8 * f_in s' - f_bits s' <= 8 * f_in s - f_bits s + 28
        /\ f_out s <= f_out s' <= f_out s + len
        /\ f_in s <= f_in s'
    | BodyFuel => True
    end.
Proof.
  intros c len s v H1 H2 H3 H4 H4a H5 H6 H7 H8 H9.
  exact (if_dodist_cw 14 c len s v H1 H2 H3 H4 H4a H5 H6 H7 H8 H9).
Qed.

(** One [dolen] level that does not chain: width + length extras (<= 5,
    the [lext] literal premise) + the whole distance side (<= 28). *)
Lemma if_dolen_nochain_cw :
  forall k c s h,
    lc_chains (c_op h) = false ->
    (forall i, 0 <= c_bits (f_dcode c i) <= 15) ->
    (forall i, Z.land (c_op (f_dcode c i)) 16 <> 0 ->
       Z.land (c_op (f_dcode c i)) 15 <= 13) ->
    chain_fit dc_chains (f_dcode c) (f_dmask c) ->
    dcode_two_level c ->
    lc_len_ok h ->
    (Z.land (c_op h) 16 <> 0 -> Z.land (c_op h) 15 <= 5) ->
    0 <= c_bits h <= f_bits s -> f_bits s <= 40 ->
    0 <= f_wnext c ->
    match if_dolen (S k) c s h with
    | BodyOk s' | BodyEob s' | BodyBad s' _ =>
        8 * f_in s' - f_bits s' <= 8 * f_in s - f_bits s + c_bits h + 33
        /\ f_out s <= f_out s' <= f_out s + 258
        /\ f_in s <= f_in s'
    | BodyFuel => True
    end.
Proof.
  intros k c s h Hnc Hdb Hde Hdf Hdt Hlc Hle Hcb Hb40 Hwn.
  cbn [if_dolen].
  pose proof (if_drop_bud c s (c_bits h) ltac:(lia) ltac:(lia)) as (_ & B1).
  assert (F1 : f_in (if_drop (c_bits h) s) = f_in s) by reflexivity.
  assert (O1 : f_out (if_drop (c_bits h) s) = f_out s) by reflexivity.
  set (s1 := if_drop (c_bits h) s) in *.
  destruct (Z.eqb (c_op h) 0) eqn:E0.
  - (* literal: one byte out, nothing more consumed *)
    cbv iota. cbn [if_put f_in f_bits f_out]. repeat split; lia.
  - destruct (negb (Z.eqb (Z.land (c_op h) 16) 0)) eqn:E16.
    + (* length base *)
      assert (He5 : Z.land (c_op h) 15 <= 5)
        by (apply Hle; apply Bool.negb_true_iff, Z.eqb_neq in E16; exact E16).
      pose proof (land15_range (c_op h)) as He.
      apply Bool.negb_true_iff, Z.eqb_neq in E16.
      destruct (Hlc E16) as (Hv3 & Hv258).
      set (e := Z.land (c_op h) 15) in *.
      destruct (Z.eqb e 0) eqn:Ee0.
      * (* no extra bits *)
        apply Z.eqb_eq in Ee0. cbv iota.
        assert (Hlen : 3 <= c_val h <= 258).
        { rewrite Ee0 in Hv258. cbn in Hv258. lia. }
        pose proof (if_refill15_bud c s1 ltac:(lia))
          as (_ & _ & _ & _ & _ & Hrng).
        pose proof (if_refill15_ge15 c s1 ltac:(lia)) as Hge15.
        pose proof (if_refill15_cur c s1) as (Crf & Irf & Orf).
        set (s3 := if_refill15 c s1) in *. clearbody s3.
        pose proof (Hdb (Z.land (f_hold s3) (f_dmask c))) as Hdc.
        assert (Hd15 : 15 <= f_bits s3
                       \/ dc_chains (c_op (f_dcode c
                            (Z.land (f_hold s3) (f_dmask c)))) = false)
          by (left; lia).
        pose proof (if_dodist_cw_tbl c (c_val h) s3
                      (Z.land (f_hold s3) (f_dmask c))
                      Hdb Hde Hdf Hdt ltac:(intros _; eexists; reflexivity)
                      ltac:(lia) ltac:(lia)
                      Hd15 Hwn Hlen) as HD.
        destruct (if_dodist tbl_fuel c (c_val h) s3
                    (f_dcode c (Z.land (f_hold s3) (f_dmask c))))
          as [s'|s'|s' m0|]; [ | | | exact I];
          destruct HD as (HD1 & HD2 & HD3); repeat split; lia.
      * (* one conditional load, then drop e *)
        apply Z.eqb_neq in Ee0. cbv iota.
        set (sa := if Z.ltb (f_bits s1) e then if_load1 c s1 else s1).
        assert (Hsa : e <= f_bits sa /\ f_bits sa <= 40
                      /\ 8 * f_in sa - f_bits sa = 8 * f_in s1 - f_bits s1
                      /\ f_in s1 <= f_in sa /\ f_out sa = f_out s1).
        { unfold sa. destruct (Z.ltb_spec (f_bits s1) e) as [Hltb|Hgeb].
          - destruct (if_load1_bud c s1) as (_ & Ba).
            cbn [if_load1 f_in f_out f_bits] in *. repeat split; lia.
          - repeat split; lia. }
        destruct Hsa as (Hgea & Hba & Ca & Ia & Oa).
        pose proof (if_low_range e sa ltac:(lia)) as Hlow.
        assert (Hlen : 3 <= c_val h + if_low e sa <= 258) by lia.
        pose proof (if_drop_bud c sa e ltac:(lia) ltac:(lia)) as (_ & Be).
        assert (Fe : f_in (if_drop e sa) = f_in sa) by reflexivity.
        assert (Oe : f_out (if_drop e sa) = f_out sa) by reflexivity.
        set (s2 := if_drop e sa) in *.
        pose proof (if_refill15_bud c s2 ltac:(lia))
          as (_ & _ & _ & _ & _ & Hrng).
        pose proof (if_refill15_ge15 c s2 ltac:(lia)) as Hge15.
        pose proof (if_refill15_cur c s2) as (Crf & Irf & Orf).
        set (s3 := if_refill15 c s2) in *. clearbody s3.
        pose proof (Hdb (Z.land (f_hold s3) (f_dmask c))) as Hdc.
        assert (Hd15 : 15 <= f_bits s3
                       \/ dc_chains (c_op (f_dcode c
                            (Z.land (f_hold s3) (f_dmask c)))) = false)
          by (left; lia).
        pose proof (if_dodist_cw_tbl c (c_val h + if_low e sa) s3
                      (Z.land (f_hold s3) (f_dmask c))
                      Hdb Hde Hdf Hdt ltac:(intros _; eexists; reflexivity)
                      ltac:(lia) ltac:(lia)
                      Hd15 Hwn Hlen) as HD.
        destruct (if_dodist tbl_fuel c (c_val h + if_low e sa) s3
                    (f_dcode c (Z.land (f_hold s3) (f_dmask c))))
          as [s'|s'|s' m0|]; [ | | | exact I];
          destruct HD as (HD1 & HD2 & HD3); repeat split; lia.
    + destruct (Z.eqb (Z.land (c_op h) 64) 0) eqn:E64.
      * (* would chain, contradicting [lc_chains = false] *)
        exfalso. unfold lc_chains in Hnc.
        rewrite E0 in Hnc. apply Bool.negb_false_iff in E16.
        rewrite E16, E64 in Hnc. cbn in Hnc. discriminate.
      * (* end of block, or invalid *)
        destruct (negb (Z.eqb (Z.land (c_op h) 32) 0));
          cbv iota; repeat split; lia.
Qed.

(** The two-level closure: root width (or chained pair, <= 15 by
    [chain_fit]) + 5 + 28 = 48 — the per-trip consumed-cursor bound. *)
Lemma if_dolen_cw :
  forall k c s v n,
    (forall i, 0 <= i < n -> 1 <= c_bits (f_lcode c i) <= 15) ->
    (forall i, 0 <= c_bits (f_dcode c i) <= 15) ->
    chain_fit lc_chains (f_lcode c) (f_lmask c) ->
    chain_fit dc_chains (f_dcode c) (f_dmask c) ->
    lcode_two_level c -> dcode_two_level c ->
    (lc_chains (c_op (f_lcode c v)) = true ->
       exists x, v = Z.land x (f_lmask c)) ->
    lcode_len_bounded_upto c n -> lcode_index_range n c -> 0 <= v < n ->
    (forall i, 0 <= i < n -> Z.land (c_op (f_lcode c i)) 16 <> 0 ->
       Z.land (c_op (f_lcode c i)) 15 <= 5) ->
    (forall i, Z.land (c_op (f_dcode c i)) 16 <> 0 ->
       Z.land (c_op (f_dcode c i)) 15 <= 13) ->
    c_bits (f_lcode c v) <= f_bits s -> 0 <= f_bits s <= 40 ->
    (15 <= f_bits s \/ lc_chains (c_op (f_lcode c v)) = false) ->
    0 <= f_wnext c ->
    match if_dolen (S (S k)) c s (f_lcode c v) with
    | BodyOk s' | BodyEob s' | BodyBad s' _ =>
        8 * f_in s' - f_bits s' <= 8 * f_in s - f_bits s + 48
        /\ f_out s <= f_out s' <= f_out s + 258
        /\ f_in s <= f_in s'
    | BodyFuel => True
    end.
Proof.
  intros k c s v n Hlb Hdb Hlf Hdf Hlt Hdt Hwv Hup Hir Hv Hlee Hdee Hcov Hrange
    Hdisj Hwn.
  destruct (lc_chains (c_op (f_lcode c v))) eqn:Hch.
  - assert (H15 : 15 <= f_bits s)
      by (destruct Hdisj as [H|H]; [exact H | congruence]).
    rewrite (if_dolen_chain_step (S k) c s _ Hch).
    destruct (Hwv eq_refl) as (xw & Hxw).
    pose proof (Hlf v xw (if_drop (c_bits (f_lcode c v)) s) Hxw Hch) as Hf.
    pose proof (Hlt v xw (if_drop (c_bits (f_lcode c v)) s) Hxw Hch) as Hnc.
    destruct Hir as (Hroot & Hchain).
    pose proof (Hchain v (if_drop (c_bits (f_lcode c v)) s) Hv Hch) as Hvin.
    pose proof (Hlb v Hv) as Hv15.
    pose proof (Hlb _ Hvin) as Hcbc.
    pose proof (if_drop_bud c s (c_bits (f_lcode c v))
                  ltac:(lia) ltac:(lia)) as (_ & B1).
    assert (F1 : f_in (if_drop (c_bits (f_lcode c v)) s) = f_in s)
      by reflexivity.
    assert (O1 : f_out (if_drop (c_bits (f_lcode c v)) s) = f_out s)
      by reflexivity.
    pose proof (if_dolen_nochain_cw k c (if_drop (c_bits (f_lcode c v)) s)
                  (f_lcode c (c_val (f_lcode c v)
                              + if_low (c_op (f_lcode c v))
                                  (if_drop (c_bits (f_lcode c v)) s)))
                  Hnc Hdb Hdee Hdf Hdt (Hup _ Hvin) (Hlee _ Hvin)
                  ltac:(lia) ltac:(lia) Hwn) as W.
    destruct (if_dolen (S k) c (if_drop (c_bits (f_lcode c v)) s)
                (f_lcode c (c_val (f_lcode c v)
                            + if_low (c_op (f_lcode c v))
                                (if_drop (c_bits (f_lcode c v)) s))))
      as [s'|s'|s' m0|]; [ | | | exact I];
      destruct W as (W1 & W2 & W3); repeat split; lia.
  - pose proof (Hlb v Hv) as Hv15.
    pose proof (if_dolen_nochain_cw (S k) c s (f_lcode c v)
                  Hch Hdb Hdee Hdf Hdt (Hup v Hv) (Hlee v Hv)
                  ltac:(lia) ltac:(lia) Hwn) as W.
    destruct (if_dolen (S (S k)) c s (f_lcode c v))
      as [s'|s'|s' m0|]; [ | | | exact I];
      destruct W as (W1 & W2 & W3); repeat split; lia.
Qed.

(** ** Trip- and loop-level composition (2026-08-19, Q4 continuation)

    [if_walk_ok] is the table-side contract the three walks share, over
    [if_ctx]'s fields, with the relativised lcode package's [n] surfaced.
    Discharge routes, per conjunct (all named, none derivable here):
    - strict lcode widths: root region Qed as
      [ItGTblCover.it_covers_root_pos]; the sub-table analogue is a named
      residual.  NOTE for the discharger: over a whole [ztbl] this may
      need index-relativisation (unwritten slots), the same repair shape
      as [lcode_len_bounded].
    - dcode widths in [0,15]: [TblSide]'s bit half ([it_fill] writes
      [len - drop]).
    - [chain_fit] both sides: [inflate_table]'s [root + curr <= MAXBITS]
      construction ([inftrees.c:293-299]); named residual of the fill-loop
      invariant, alongside [SubTblPointersBelowUsed].
    - lext <= 5 / dext <= 13: the [lext]/[dext] literals ([inftrees.c:62],
      [:70]: base-entry [op] is [16 + extra], extras <= 5 resp. <= 13);
      same vm_compute instrument as [lc_len_ok]'s 2026-08-16 check, plus
      fill-loop provenance for dynamic tables. *)
Definition if_walk_ok (c : IfCtx) (n : Z) : Prop :=
  (forall i, 0 <= i < n -> 1 <= c_bits (f_lcode c i) <= 15)
  /\ (forall i, 0 <= c_bits (f_dcode c i) <= 15)
  /\ chain_fit lc_chains (f_lcode c) (f_lmask c)
  /\ chain_fit dc_chains (f_dcode c) (f_dmask c)
  /\ (forall i, 0 <= i < n -> Z.land (c_op (f_lcode c i)) 16 <> 0 ->
        Z.land (c_op (f_lcode c i)) 15 <= 5)
  /\ (forall i, Z.land (c_op (f_dcode c i)) 16 <> 0 ->
        Z.land (c_op (f_dcode c i)) 15 <= 13)
  /\ lcode_two_level c /\ dcode_two_level c
  /\ lcode_len_bounded_upto c n /\ lcode_index_range n c
  /\ 0 <= f_wnext c.

Lemma if_walk_ok_ctx_wf : forall c n, if_walk_ok c n -> if_ctx_wf c.
Proof.
  intros c n (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
  split; [exact H11|]. split; [exact H7|]. split; [exact H8|].
  exists n. split; [exact H9 | exact H10].
Qed.

(** What ONE trip of the body guarantees, in every exit shape: it spends
    at least 1 of the budget, consumes at most 48 bits of cursor, keeps
    the reader's bit count in [0,40], never moves the input cursor
    backwards, and writes between 0 and 258 bytes. *)
Definition trip_facts (c : IfCtx) (s s' : IfSt) : Prop :=
  if_bud c s' <= if_bud c s - 1
  /\ 8 * f_in s' - f_bits s' <= 8 * f_in s - f_bits s + 48
  /\ 0 <= f_bits s' <= 40
  /\ f_in s <= f_in s'
  /\ f_out s <= f_out s' <= f_out s + 258.

Corollary if_dolen_cw_tbl :
  forall c s v n,
    (forall i, 0 <= i < n -> 1 <= c_bits (f_lcode c i) <= 15) ->
    (forall i, 0 <= c_bits (f_dcode c i) <= 15) ->
    chain_fit lc_chains (f_lcode c) (f_lmask c) ->
    chain_fit dc_chains (f_dcode c) (f_dmask c) ->
    lcode_two_level c -> dcode_two_level c ->
    (lc_chains (c_op (f_lcode c v)) = true ->
       exists x, v = Z.land x (f_lmask c)) ->
    lcode_len_bounded_upto c n -> lcode_index_range n c -> 0 <= v < n ->
    (forall i, 0 <= i < n -> Z.land (c_op (f_lcode c i)) 16 <> 0 ->
       Z.land (c_op (f_lcode c i)) 15 <= 5) ->
    (forall i, Z.land (c_op (f_dcode c i)) 16 <> 0 ->
       Z.land (c_op (f_dcode c i)) 15 <= 13) ->
    c_bits (f_lcode c v) <= f_bits s -> 0 <= f_bits s <= 40 ->
    (15 <= f_bits s \/ lc_chains (c_op (f_lcode c v)) = false) ->
    0 <= f_wnext c ->
    match if_dolen tbl_fuel c s (f_lcode c v) with
    | BodyOk s' | BodyEob s' | BodyBad s' _ =>
        8 * f_in s' - f_bits s' <= 8 * f_in s - f_bits s + 48
        /\ f_out s <= f_out s' <= f_out s + 258
        /\ f_in s <= f_in s'
    | BodyFuel => True
    end.
Proof.
  intros c s v n H1 H2 H3 H4 H5 H6 H6a H7 H8 H9 H10 H11 H12 H13 H14 H15.
  exact (if_dolen_cw 14 c s v n H1 H2 H3 H4 H5 H6 H6a H7 H8 H9 H10 H11 H12
           H13 H14 H15).
Qed.

(** The abstract combiner that keeps the kernel away from a case split
    over a concrete [if_dolen] application (the [Qed] hazard documented at
    [InflateFast.v]'s [if_step_unfold]; this file hit it live: the direct
    destruct's [Qed] ran past 8 minutes, this route is instant). *)
Lemma body_match_combine :
  forall (X : IfBody) (P1 P2 P3 Q : IfSt -> Prop),
    X <> BodyFuel ->
    match X with
    | BodyOk s' | BodyEob s' | BodyBad s' _ => P1 s'
    | BodyFuel => True
    end ->
    match X with
    | BodyOk s' | BodyEob s' | BodyBad s' _ => P2 s'
    | BodyFuel => True
    end ->
    match X with
    | BodyOk s' | BodyEob s' | BodyBad s' _ => P3 s'
    | BodyFuel => True
    end ->
    (forall s', P1 s' -> P2 s' -> P3 s' -> Q s') ->
    match X with
    | BodyOk s' | BodyEob s' | BodyBad s' _ => Q s'
    | BodyFuel => False
    end.
Proof.
  intros X P1 P2 P3 Q Hnf H1 H2 H3 HQ.
  destruct X as [s'|s'|s' m|];
    [ exact (HQ s' H1 H2 H3) | exact (HQ s' H1 H2 H3)
    | exact (HQ s' H1 H2 H3) | exact (Hnf eq_refl) ].
Qed.

(** The one-step unfolding of [if_body], as a REFLEXIVITY-proved rewrite
    (the same discipline as [if_step_unfold]/[if_iter_S]): rewriting with
    an opaque equality keeps the kernel from ever having to CONVERT an
    [if_body]-headed type against an [if_dolen]-headed one — that
    conversion whnf-unfolds the literal-fuelled fixpoint and does not
    come back (measured here: [Qed] past 8 minutes; with the rewrite,
    instant). *)
Lemma if_body_unfold :
  forall c s,
    if_body c s
    = if_dolen tbl_fuel c (if_refill15 c s)
        (f_lcode c (Z.land (f_hold (if_refill15 c s)) (f_lmask c))).
Proof. reflexivity. Qed.

Theorem if_body_bud :
  forall c s n,
    if_walk_ok c n -> 0 <= f_bits s <= 40 ->
    match if_body c s with
    | BodyOk s' | BodyEob s' | BodyBad s' _ => trip_facts c s s'
    | BodyFuel => False
    end.
Proof.
  intros c s n Hwalk Hb.
  pose proof (if_body_not_fuel c s (if_walk_ok_ctx_wf c n Hwalk)) as Hnf.
  destruct Hwalk as (Hlb & Hdb & Hlf & Hdf & Hlee & Hdee & Hlt & Hdt & Hup
                     & Hir & Hwn).
  rewrite if_body_unfold in Hnf |- *.
  pose proof (if_refill15_bud c s ltac:(lia))
    as (Ebud & _ & _ & _ & _ & Hrng).
  pose proof (if_refill15_ge15 c s ltac:(lia)) as Hge15.
  pose proof (if_refill15_cur c s) as (Crf & Irf & Orf).
  set (s0 := if_refill15 c s) in *. clearbody s0.
  pose proof (proj1 Hir s0) as Hv0.
  pose proof (Hlb _ Hv0) as Hb0.
  assert (Hdisj : 15 <= f_bits s0
                  \/ lc_chains (c_op (f_lcode c
                       (Z.land (f_hold s0) (f_lmask c)))) = false)
    by (left; lia).
  apply (body_match_combine
           (if_dolen tbl_fuel c s0
              (f_lcode c (Z.land (f_hold s0) (f_lmask c))))
           (fun s' => if_bud c s' <= if_bud c s0 - 1)
           (fun s' => 0 <= f_bits s' <= 40 /\ f_in s' <= f_in s0 + 5)
           (fun s' => 8 * f_in s' - f_bits s' <= 8 * f_in s0 - f_bits s0 + 48
                      /\ f_out s0 <= f_out s' <= f_out s0 + 258
                      /\ f_in s0 <= f_in s')
           (trip_facts c s) Hnf).
  - exact (if_dolen_bud tbl_fuel c s0 (Z.land (f_hold s0) (f_lmask c)) n
             Hlb Hdb Hlf Hdf Hlt Hdt ltac:(intros _; eexists; reflexivity)
             Hup Hir Hv0 ltac:(lia) ltac:(lia) Hdisj).
  - exact (if_dolen_fin tbl_fuel c s0 (Z.land (f_hold s0) (f_lmask c)) n
             Hlb Hdb Hlf Hdf Hlt Hdt ltac:(intros _; eexists; reflexivity)
             Hup Hir Hv0 ltac:(lia) ltac:(lia) Hdisj).
  - exact (if_dolen_cw_tbl c s0 (Z.land (f_hold s0) (f_lmask c)) n
             Hlb Hdb Hlf Hdf Hlt Hdt ltac:(intros _; eexists; reflexivity)
             Hup Hir Hv0 Hlee Hdee ltac:(lia)
             ltac:(lia) Hdisj Hwn).
  - intros s' W1 (WF1 & WF2) (WC1 & WC2 & WC3).
    unfold trip_facts. repeat split; lia.
Qed.

Lemma if_step_bud_abs :
  forall c (b : IfBody) (P : IfSt -> Prop),
    match b with
    | BodyOk s' | BodyEob s' | BodyBad s' _ => P s'
    | BodyFuel => False
    end ->
    match (match b with
           | BodyOk s1 => if if_guard c s1 then IfCont s1 else IfStop s1
           | BodyEob s1 => IfEob s1
           | BodyBad s1 m => IfBad s1 m
           | BodyFuel => IfFuel
           end) with
    | IfCont s' | IfStop s' | IfEob s' | IfBad s' _ => P s'
    | IfFuel => False
    end.
Proof.
  intros c b P H. destruct b as [s1|s1|s1 m|]; cbv beta iota in H |- *;
    [ destruct (if_guard c s1); exact H | exact H | exact H | exact H ].
Qed.

Lemma if_step_bud :
  forall c s n,
    if_walk_ok c n -> 0 <= f_bits s <= 40 ->
    match if_step c s with
    | IfCont s' | IfStop s' | IfEob s' | IfBad s' _ => trip_facts c s s'
    | IfFuel => False
    end.
Proof.
  intros c s n Hwalk Hb. rewrite if_step_unfold.
  exact (if_step_bud_abs c (if_body c s) (trip_facts c s)
           (if_body_bud c s n Hwalk Hb)).
Qed.

(** The loop-level composition.  Every trip's ENTRY satisfies the guard
    (the exit trip included: the loop is bottom-tested), so the exit
    cursor is bounded by the LAST trip entry's [in < last] plus one
    trip's 48, and the exit write cursor by [out < end] plus one trip's
    258 — exactly the [5 + last - in] / [257 + end - out] margins
    [if_finish] recomputes. *)
Lemma if_loop_bud :
  forall m c s n r,
    if_walk_ok c n -> 0 <= f_bits s <= 40 ->
    f_in s < f_last c -> f_out s < f_end c ->
    if_loop m c s = Some r ->
    match r with
    | IfStop s' | IfEob s' | IfBad s' _ =>
        if_bud c s' <= if_bud c s - 1
        /\ 8 * f_in s' - f_bits s' <= 8 * f_last c + 40
        /\ 0 <= f_bits s' <= 40
        /\ f_in s <= f_in s'
        /\ f_out s <= f_out s' /\ f_out s' <= f_end c + 257
    | IfCont _ => False
    | IfFuel => False
    end.
Proof.
  induction m as [|m IH]; intros c s n r Hwalk Hb Hin Hout H;
    [cbn [if_loop] in H; discriminate|].
  rewrite if_loop_S in H.
  pose proof (if_step_bud c s n Hwalk Hb) as HS.
  destruct (if_step c s) as [s1|s1|s1|s1 m1|] eqn:ES.
  - (* fall-through trip: the guard holds at [s1]; recurse *)
    destruct HS as (T1 & T2 & T3 & T4 & T5).
    pose proof (if_step_cont_guard c s s1 ES) as Hg.
    apply if_guard_true in Hg. destruct Hg as (Hg1 & Hg2).
    pose proof (IH c s1 n r Hwalk T3 Hg1 Hg2 H) as HR.
    destruct r as [s'|s'|s'|s' m2|]; [exact HR| | | |exact HR];
      destruct HR as (R1 & R2 & R3 & R4 & R5 & R6);
      repeat split; lia.
  - injection H as H; subst r. cbv beta iota.
    destruct HS as (T1 & T2 & T3 & T4 & T5). repeat split; lia.
  - injection H as H; subst r. cbv beta iota.
    destruct HS as (T1 & T2 & T3 & T4 & T5). repeat split; lia.
  - injection H as H; subst r. cbv beta iota.
    destruct HS as (T1 & T2 & T3 & T4 & T5). repeat split; lia.
  - contradiction HS.
Qed.

(** ** The lax call contract (2026-08-19, Q4 discharge lap)

    [if_wf] minus the three conjuncts nothing in this file's walks
    consumes: [avail_out <= start], [a_bits < 8] (weakened to the walks'
    own [<= 40] — the strict form is NOT an invariant of the mode machine:
    a slow-path symbol decode or a CODELENS exit can reach the fast gate
    holding 8..~31 bits, so a discharge carrying [if_wf] itself would be
    stuck) and the accumulator-range clause.  [if_wf] implies it, so every
    consumer of the measured contract still composes; the reachability
    discharge supplies THIS one. *)
Definition if_wf_lax (a : IfArgs) : Prop :=
  6 <= a_avail_in a
  /\ 258 <= a_avail_out a
  /\ 0 <= a_bits a <= 40
  /\ 1 <= a_lenbits a <= 15
  /\ 1 <= a_distbits a <= 15
  /\ a_sane a = 1
  /\ 0 <= a_whave a <= a_wsize a
  /\ 0 <= a_wnext a <= a_wsize a
  /\ (forall i, 0 <= a_inbuf a i < 256)
  /\ (forall i, 0 <= a_window a i < 256)
  /\ lcode_two_level (if_ctx a)
  /\ dcode_two_level (if_ctx a)
  /\ lcode_len_bounded (if_ctx a).

Lemma if_wf_lax_of_wf : forall a, if_wf a -> if_wf_lax a.
Proof.
  intros a (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12
            & Hlt & Hdt & Hlbnd).
  split; [exact H1|]. split; [exact H2|]. split; [lia|].
  split; [exact H6|]. split; [exact H7|]. split; [exact H8|].
  split; [exact H9|]. split; [exact H10|]. split; [exact H11|].
  split; [exact H12|]. split; [exact Hlt|]. split; [exact Hdt|].
  exact Hlbnd.
Qed.

Lemma if_lax_ctx_wf : forall a, if_wf_lax a -> if_ctx_wf (if_ctx a).
Proof.
  intros a (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & Hlt & Hdt
            & Hlbnd).
  split; [cbn [f_wnext if_ctx]; lia|].
  split; [exact Hlt|]. split; [exact Hdt|]. exact Hlbnd.
Qed.

(** [if_model_total], from the lax contract (the bundled
    [lcode_len_bounded] makes the historical second premise redundant). *)
Theorem if_model_total_lax :
  forall a, if_wf_lax a -> exists y, if_model a = Some y.
Proof.
  intros a Hwf.
  pose proof (if_lax_ctx_wf a Hwf) as Hc.
  unfold if_model.
  destruct (if_loop_total (Z.to_nat (f_end (if_ctx a) - f_out (if_st0 a)))
              (if_ctx a) (if_st0 a) Hc ltac:(lia)) as [r [Heq Hd]].
  rewrite Heq.
  destruct r as [s1|s1|s1|s1 m|]; cbn [loop_done] in Hd; try contradiction;
    eexists; reflexivity.
Qed.

(** ** The [if_finish] unwrap and the budget correspondence

    The table half of [if_wf], at the [IfArgs] level ([f_lcode (if_ctx a)]
    is [a_lcode a] definitionally, so the conjuncts transport by
    conversion). *)
(** RELATIVISED 2026-08-19 (Q4 discharge lap).  The unscoped strict-width
    and lext clauses were UNINHABITABLE at every real table: the fixed
    tables and the initial codes array both default unwritten slots to
    [mkCode 0 0 0] (bits 0), and a DISTS build leaves distance bases
    ([op & 15] up to 13) in the shared array above [nx] — the same
    unit-mismatch class as [lcode_len_bounded]'s repair.  The walks only
    read the lcode at the masked root index and at chain targets, both
    bounded by [lcode_index_range]'s two clauses, so the four lcode-side
    facts share ONE witness [n] with the relativised length package.  The
    dcode-side clauses stay honestly table-wide: bits in [0,15], the
    16-bit values and the dext bound are all EXEMPT at zero slots ([op 0]
    has bit 4 clear) and maintained by every write the builds perform. *)
Definition if_wf_tbl (a : IfArgs) : Prop :=
  (exists n,
      lcode_len_bounded_upto (if_ctx a) n
      /\ lcode_index_range n (if_ctx a)
      /\ (forall i, 0 <= i < n -> 1 <= c_bits (a_lcode a i) <= 15)
      /\ (forall i, 0 <= i < n -> Z.land (c_op (a_lcode a i)) 16 <> 0 ->
            Z.land (c_op (a_lcode a i)) 15 <= 5))
  /\ (forall i, 0 <= c_bits (a_dcode a i) <= 15)
  /\ chain_fit lc_chains (a_lcode a) (f_lmask (if_ctx a))
  /\ chain_fit dc_chains (a_dcode a) (f_dmask (if_ctx a))
  /\ (forall i, Z.land (c_op (a_dcode a i)) 16 <> 0 ->
        Z.land (c_op (a_dcode a i)) 15 <= 13).

Lemma if_wf_walk_ok :
  forall a, if_wf_lax a -> if_wf_tbl a -> exists n, if_walk_ok (if_ctx a) n.
Proof.
  intros a Hwf Htbl.
  destruct Hwf as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10
                   & Hlt & Hdt & Hlbnd).
  destruct Htbl as ((n & Hup & Hir & TW & TL) & T2 & T3 & T4 & T6).
  exists n.
  split; [exact TW|]. split; [exact T2|]. split; [exact T3|].
  split; [exact T4|]. split; [exact TL|]. split; [exact T6|].
  split; [exact Hlt|]. split; [exact Hdt|].
  split; [exact Hup|]. split; [exact Hir|].
  cbn [if_ctx f_wnext]. lia.
Qed.

(** The epilogue's [u32]s unwrapped.  [avail_in]/[avail_out] both recompute
    to the SAME linear expression on either side of their conditional
    ([5 + (last - in)] resp. [257 + (end - out)] — the conditional only
    dodges C pointer overflow), and under the walk's exit facts both
    arguments are within [0, 2^32).  The model budget and the
    reconstructed post-call budget then differ by the constant 40 + 257
    on both sides, so the [- 1] transports. *)
Lemma if_finish_unwrap :
  forall a s' e,
    6 <= a_avail_in a -> 258 <= a_avail_out a ->
    a_avail_in a <= 4294967290 -> a_avail_out a <= 4294967295 ->
    0 <= a_bits a ->
    if_bud (if_ctx a) s' <= if_bud (if_ctx a) (if_st0 a) - 1 ->
    8 * f_in s' - f_bits s' <= 8 * f_last (if_ctx a) + 40 ->
    0 <= f_bits s' <= 40 ->
    f_in (if_st0 a) <= f_in s' ->
    f_out (if_st0 a) <= f_out s' -> f_out s' <= f_end (if_ctx a) + 257 ->
    8 * y_avail_in (if_finish (if_ctx a) s' e)
      + y_bits (if_finish (if_ctx a) s' e)
      + y_avail_out (if_finish (if_ctx a) s' e)
      <= 8 * a_avail_in a + a_bits a + a_avail_out a - 1
    /\ 0 <= y_avail_in (if_finish (if_ctx a) s' e)
    /\ 0 <= y_bits (if_finish (if_ctx a) s' e)
    /\ 0 <= y_avail_out (if_finish (if_ctx a) s' e)
    /\ 0 <= y_hold (if_finish (if_ctx a) s' e).
Proof.
  intros a s' e Hain6 Haout258 Hain Haout Hbits0 Hbud Hcur Hbr Hinm Houtm
    Houte.
  assert (HL : f_last (if_ctx a) = a_next_in a + (a_avail_in a - 5))
    by reflexivity.
  assert (HE : f_end (if_ctx a) = a_next_out a + (a_avail_out a - 257))
    by reflexivity.
  assert (HI0 : f_in (if_st0 a) = a_next_in a) by reflexivity.
  assert (HO0 : f_out (if_st0 a) = a_next_out a) by reflexivity.
  assert (HB0 : f_bits (if_st0 a) = a_bits a) by reflexivity.
  assert (Hbud0 : if_bud (if_ctx a) (if_st0 a)
                  = 8 * a_avail_in a - 40 + a_bits a + (a_avail_out a - 257)).
  { unfold if_bud. rewrite HL, HE, HI0, HO0, HB0. lia. }
  unfold if_bud in Hbud.
  unfold if_finish. cbv zeta.
  cbn [y_avail_in y_bits y_avail_out y_hold].
  set (l := Z.shiftr (f_bits s') 3) in *.
  assert (Hl : l = f_bits s' / 8)
    by (unfold l; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (Hlrange : 0 <= l <= 5).
  { rewrite Hl. split; [apply Z.div_pos; lia|].
    apply Z.div_le_upper_bound; lia. }
  assert (Hshift : Z.shiftl l 3 = 8 * l)
    by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  assert (Hbmod : 0 <= f_bits s' - Z.shiftl l 3 <= 7).
  { rewrite Hshift, Hl.
    pose proof (Z.mod_pos_bound (f_bits s') 8 ltac:(lia)) as Hm.
    pose proof (Z.div_mod (f_bits s') 8 ltac:(lia)) as Hd. lia. }
  rewrite (u32_id (f_bits s' - Z.shiftl l 3)) by lia.
  set (i := f_in s' - l) in *.
  assert (Hi_hi : i <= f_last (if_ctx a) + 5).
  { assert (H8i : 8 * i = (8 * f_in s' - f_bits s')
                          + (f_bits s' - Z.shiftl l 3))
      by (rewrite Hshift; unfold i; lia).
    lia. }
  assert (Hi_lo : a_next_in a - 5 <= i) by (unfold i; lia).
  assert (Havin : (if Z.ltb i (f_last (if_ctx a))
                   then 5 + (f_last (if_ctx a) - i)
                   else 5 - (i - f_last (if_ctx a)))
                  = 5 + (f_last (if_ctx a) - i))
    by (destruct (Z.ltb i (f_last (if_ctx a))); lia).
  rewrite Havin.
  rewrite (u32_id (5 + (f_last (if_ctx a) - i))) by lia.
  assert (Havout : (if Z.ltb (f_out s') (f_end (if_ctx a))
                    then 257 + (f_end (if_ctx a) - f_out s')
                    else 257 - (f_out s' - f_end (if_ctx a)))
                   = 257 + (f_end (if_ctx a) - f_out s'))
    by (destruct (Z.ltb (f_out s') (f_end (if_ctx a))); lia).
  rewrite Havout.
  rewrite (u32_id (257 + (f_end (if_ctx a) - f_out s'))) by lia.
  assert (Hhold : 0 <= Z.land (f_hold s')
                         (Z.shiftl 1 (f_bits s' - Z.shiftl l 3) - 1)).
  { apply land_nonneg_r. rewrite Z.shiftl_1_l.
    pose proof (Z.pow_pos_nonneg 2 (f_bits s' - Z.shiftl l 3)
                  ltac:(lia) ltac:(lia)). lia. }
  repeat split; try lia.
Qed.

(** The composed statement [arm_LEN] consumes: on ANY successful
    [if_model] call under [if_wf] + the walk's table contract + a
    2^24 cap on the two avails (reachability-cheap: they are byte counts
    of live buffers), the reconstructed budget [8*avail_in' + bits' +
    avail_out'] drops by at least 1, and every write-back field the mode
    machine reads back is nonnegative. *)
(** The exit facts, stated GOAL-SIDE over [if_model a] (the landed
    [if_model_total] shape).  KERNEL DISCIPLINE, learned here the hard
    way (three [Qed]s past 8 minutes): any HYPOTHESIS-side unfolding of
    [if_model] — [unfold ... in HM] followed by a rewrite, or a
    [destruct ... eqn:] on the [if_loop] application — hands the kernel a
    conversion between [if_model]-headed and body-headed types whose whnf
    cascades through the literal-fuelled fixpoints and does not come back.
    Goal-side, the same unfolding is one aligned meeting and is instant.
    The [= Some y] corollary below then never touches the unfolded form:
    it rewrites the OPAQUE equation into this lemma's conclusion. *)
Theorem if_model_exit :
  forall a,
    if_wf_lax a -> if_wf_tbl a ->
    a_avail_in a <= 4294967290 -> a_avail_out a <= 4294967295 ->
    match if_model a with
    | None => True
    | Some y =>
        8 * y_avail_in y + y_bits y + y_avail_out y
          <= 8 * a_avail_in a + a_bits a + a_avail_out a - 1
        /\ 0 <= y_avail_in y /\ 0 <= y_bits y /\ 0 <= y_avail_out y
        /\ 0 <= y_hold y
    end.
Proof.
  intros a Hwf Htbl Hain Haout.
  destruct (if_wf_walk_ok a Hwf Htbl) as (n & Hwalk).
  pose proof Hwf as (Hain6 & Haout258 & Hbits & _).
  pose proof (if_walk_ok_ctx_wf _ _ Hwalk) as Hcwf.
  destruct (if_loop_total (Z.to_nat (f_end (if_ctx a) - f_out (if_st0 a)))
              (if_ctx a) (if_st0 a) Hcwf ltac:(lia)) as (r & Heq & Hd).
  assert (Hb0 : 0 <= f_bits (if_st0 a) <= 40) by (cbn [if_st0 f_bits]; lia).
  assert (Hin0 : f_in (if_st0 a) < f_last (if_ctx a))
    by (cbn [if_st0 f_in if_ctx f_last]; lia).
  assert (Hout0 : f_out (if_st0 a) < f_end (if_ctx a))
    by (cbn [if_st0 f_out if_ctx f_end]; lia).
  pose proof (if_loop_bud _ _ _ n r Hwalk Hb0 Hin0 Hout0 Heq) as HL.
  unfold if_model. cbv zeta. rewrite Heq.
  destruct r as [s'|s'|s'|s' m0|]; cbv beta iota;
    [exact I| | | |exact I];
    destruct HL as (L1 & L2 & L3 & L4 & L5 & L6);
    apply if_finish_unwrap; try assumption; lia.
Qed.

Theorem if_model_bud :
  forall a y,
    if_wf_lax a -> if_wf_tbl a ->
    a_avail_in a <= 4294967290 -> a_avail_out a <= 4294967295 ->
    if_model a = Some y ->
    8 * y_avail_in y + y_bits y + y_avail_out y
      <= 8 * a_avail_in a + a_bits a + a_avail_out a - 1
    /\ 0 <= y_avail_in y /\ 0 <= y_bits y /\ 0 <= y_avail_out y
    /\ 0 <= y_hold y.
Proof.
  intros a y Hwf Htbl Hain Haout HM.
  pose proof (if_model_exit a Hwf Htbl Hain Haout) as HE.
  rewrite HM in HE. cbv beta iota in HE. exact HE.
Qed.

(** ** [arm_LEN] — [inflate.c:1023-1072] [case LEN], and LEN_ (2026-08-19, Q4)

    The fast path is the [inflate_fast] call node.  Its contract —
    [if_wf_lax (len_args q)], the walk's table half [if_wf_tbl (len_args q)],
    and a 2^24 cap on the two avails (they are byte counts of live
    buffers) — is a single mode-conditioned premise, itself conditioned on
    the C's own gate [6 <= avail_in && 258 <= avail_out] (the gate IS
    [if_wf]'s first two conjuncts, so the premise cannot be required
    unconditionally at M_LEN).  Under it, [if_model_total] kills the
    [InfFuel] answer and [if_model_bud] pays the rank: the write-back
    budget [8*avail_in' + bits' + avail_out'] drops by at least 1, which
    covers all three exits (ExLen keeps M_LEN: rank falls with the budget;
    ExType descends 16200 -> 16193 in [inf_mrank], paid by the same -1;
    ExBad ascends and needs nothing).

    The slow path is one [inf_decode].  LIT/BAD ascend under a
    nonnegative spend ([TblSide]-half of [LcSide]); the end-of-block
    epsilon (LEN -> TYPE descends) is paid by the EOB entry's strictly
    positive width ([LcSide], clause 2); the length-base fall-through
    supplies [arm_LENEXT]'s entry contract — [1 <= u_length] from
    [LcSide]'s value clause, [u_extra] from the [Z.land _ 15] write —
    and lifts by [arm_ok_mono]. *)

(** The [IfArgs] record [inf_LEN] builds at [inflate.c:1026-1030],
    written from [q] directly ([RESTORE()] only copies [br_hold]/[br_bits]
    into the struct, so [a_hold]/[a_bits] are the reader's — the record
    is CONVERTIBLE to the one in [inf_LEN]'s body). *)
Definition len_args (q : InfSt) : IfArgs :=
  {| a_inbuf     := br_in (q_br q);
     a_next_in   := br_next (q_br q);
     a_avail_in  := br_have (q_br q);
     a_buf       := o_buf (q_ob q);
     a_next_out  := o_put (q_ob q);
     a_avail_out := o_left (q_ob q);
     a_start     := q_out q;
     a_wsize     := w_wsize (s_win (q_st q));
     a_whave     := w_whave (s_win (q_st q));
     a_wnext     := w_wnext (s_win (q_st q));
     a_window    := w_win (s_win (q_st q));
     a_lcode     := tbl_of (q_st q) (t_lencode (s_tab (q_st q)));
     a_dcode     := tbl_of (q_st q) (t_distcode (s_tab (q_st q)));
     a_lenbits   := t_lenbits (s_tab (q_st q));
     a_distbits  := t_distbits (s_tab (q_st q));
     a_sane      := t_sane (s_tab (q_st q));
     a_hold      := br_hold (q_br q);
     a_bits      := br_bits (q_br q) |}.

(** The write-back chain [inflate.c:1027-1032], named so [inf_LEN] can be
    restated over [len_args] by [reflexivity] and the exit case analysis
    can happen on [y_exit y] alone. *)
Definition len_post (q : InfSt) (y : IfOut) : InfSt :=
  let b := q_br q in
  let q0 := q_restore q in
  let st1 := set_bits (set_hold (q_st q0) (y_hold y)) (y_bits y) in
  let q1  := qset_st q0 st1 in
  let q2  := qset_br q1 {| br_in := br_in b; br_have := y_avail_in y;
                           br_next := y_in y;
                           br_hold := br_hold b; br_bits := br_bits b |} in
  let q3  := qset_ob q2 {| o_buf := y_buf y; o_put := y_out y;
                           o_left := y_avail_out y |} in
  let q4  := match y_exit y with
             | ExLen    => q3
             | ExType   => qmode q3 M_TYPE
             | ExBad m  => qbad q3 m
             end in
  let q5 := q_load q4 in
  match q_mode q5 with
  | M_TYPE => qset_st q5 (set_back (q_st q5) (-1))
  | _ => q5
  end.

Definition inf_LEN' (q : InfSt) : InfStep :=
  let st := q_st q in
  let tb := s_tab st in
  let b  := q_br q in
  let o  := q_ob q in
  if Z.leb 6 (br_have b) && Z.leb 258 (o_left o) then
    match if_model (len_args q) with
    | None => InfFuel
    | Some y => InfCont (len_post q y)
    end
  else
    let q0 := qset_st q (set_back st 0) in
    match inf_decode sub_len (tbl_of st (t_lencode tb)) (t_lenbits tb) b with
    | DecFuel      => InfFuel
    | DecLeave b'  => InfLeave (qset_br q0 b')
    | DecOk h b' nb =>
        let st1 := set_length (set_back (q_st q0) (0 + nb)) (c_val h) in
        let q1  := qset_br (qset_st q0 st1) b' in
        if Z.eqb (c_op h) 0 then
          InfCont (qmode q1 M_LIT)
        else if negb (Z.eqb (Z.land (c_op h) 32) 0) then
          InfCont (qmode (qset_st q1 (set_back (q_st q1) (-1))) M_TYPE)
        else if negb (Z.eqb (Z.land (c_op h) 64) 0) then
          InfCont (qbad q1 MSG_LIT_LEN_CODE)
        else
          let st2 := set_extra (q_st q1) (Z.land (c_op h) 15) in
          inf_LENEXT (qmode (qset_st q1 st2) M_LENEXT)
    end.

Lemma inf_LEN_eq : forall q, inf_LEN q = inf_LEN' q.
Proof. reflexivity. Qed.

(** The slow-path decode contract on the LIVE length table.  Discharge
    routes, per clause: (1) is [TblSide]'s bit half; (2) "the end-of-block
    entry consumes" — root region Qed as [ItGTblCover.it_covers_root_pos],
    sub-table analogue a named residual; (3) "an entry that falls through
    to LENEXT carries a positive [val]" — the [lbase] literal floor (3),
    the [dbase] floor (1), and sub-table pointer offsets (>= 2^root >= 1).
    All three hold at all-zero unwritten slots ([op = 0] is LIT-shaped and
    exempt from (2)/(3); [bits = 0] satisfies (1)), so unlike the
    fast path's strict-width premise this one needs no relativisation. *)
Definition LcSide (t : ztbl) : Prop :=
  (forall i, 0 <= c_bits (t i))
  /\ (forall i, Z.land (c_op (t i)) 32 <> 0 -> 1 <= c_bits (t i))
  /\ (forall i, c_op (t i) <> 0 -> Z.land (c_op (t i)) 32 = 0 ->
        Z.land (c_op (t i)) 64 = 0 -> 1 <= c_val (t i)).

Lemma inf_decode_eob_pos :
  forall sub t rb b h b2 nb,
    (forall i, 0 <= c_bits (t i)) ->
    (forall i, Z.land (c_op (t i)) 32 <> 0 -> 1 <= c_bits (t i)) ->
    inf_decode sub t rb b = DecOk h b2 nb ->
    Z.land (c_op h) 32 <> 0 -> 1 <= nb.
Proof.
  intros sub t rb b h b2 nb Hb He H H32. unfold inf_decode in H.
  destruct (inf_fetch t rb b) as [h0 b0|b0|] eqn:Ef;
    [|discriminate|discriminate].
  destruct (inf_fetch_go_entry _ _ _ _ _ _ Ef) as (i0 & ->).
  destruct (sub (t i0)).
  - destruct (inf_fetch2 t (t i0) b0) as [h1 b1|b1|] eqn:Ef2;
      [|discriminate|discriminate].
    destruct (inf_fetch2_go_entry _ _ _ _ _ _ Ef2) as (i1 & ->).
    inversion H; subst.
    pose proof (Hb i0). pose proof (He i1 H32). lia.
  - inversion H; subst. pose proof (He i0 H32). lia.
Qed.

Lemma inf_decode_val_pos :
  forall sub t rb b h b2 nb,
    (forall i, c_op (t i) <> 0 -> Z.land (c_op (t i)) 32 = 0 ->
       Z.land (c_op (t i)) 64 = 0 -> 1 <= c_val (t i)) ->
    inf_decode sub t rb b = DecOk h b2 nb ->
    c_op h <> 0 -> Z.land (c_op h) 32 = 0 -> Z.land (c_op h) 64 = 0 ->
    1 <= c_val h.
Proof.
  intros sub t rb b h b2 nb Hv H H0 H32 H64. unfold inf_decode in H.
  destruct (inf_fetch t rb b) as [h0 b0|b0|] eqn:Ef;
    [|discriminate|discriminate].
  destruct (inf_fetch_go_entry _ _ _ _ _ _ Ef) as (i0 & ->).
  destruct (sub (t i0)).
  - destruct (inf_fetch2 t (t i0) b0) as [h1 b1|b1|] eqn:Ef2;
      [|discriminate|discriminate].
    destruct (inf_fetch2_go_entry _ _ _ _ _ _ Ef2) as (i1 & ->).
    inversion H; subst. exact (Hv i1 H0 H32 H64).
  - inversion H; subst. exact (Hv i0 H0 H32 H64).
Qed.

(** ** Projection piece lemmas for [len_post]'s write-back chain
    (all [reflexivity]; the simpl-never wall: [cbn] declines to reduce
    these nested setter chains, so every reduction is a targeted rewrite
    with an opaque equation — the register's discipline). *)
Lemma q_load_have : forall q, br_have (q_br (q_load q)) = br_have (q_br q).
Proof. reflexivity. Qed.
Lemma q_load_bits : forall q, br_bits (q_br (q_load q)) = s_bits (q_st q).
Proof. reflexivity. Qed.
Lemma q_load_left : forall q, o_left (q_ob (q_load q)) = o_left (q_ob q).
Proof. reflexivity. Qed.
Lemma q_mode_q_load : forall q, q_mode (q_load q) = q_mode q.
Proof. reflexivity. Qed.
Lemma q_st_q_load : forall q, q_st (q_load q) = q_st q.
Proof. reflexivity. Qed.
Lemma q_br_qset_ob : forall q o, q_br (qset_ob q o) = q_br q.
Proof. reflexivity. Qed.
Lemma q_br_qset_br : forall q b, q_br (qset_br q b) = b.
Proof. reflexivity. Qed.
Lemma q_br_qset_st : forall q st, q_br (qset_st q st) = q_br q.
Proof. reflexivity. Qed.
Lemma q_br_qset_z : forall q z, q_br (qset_z q z) = q_br q.
Proof. reflexivity. Qed.
Lemma q_br_qmode : forall q m, q_br (qmode q m) = q_br q.
Proof. reflexivity. Qed.
Lemma q_ob_qset_ob : forall q o, q_ob (qset_ob q o) = o.
Proof. reflexivity. Qed.
Lemma q_ob_qset_br : forall q b, q_ob (qset_br q b) = q_ob q.
Proof. reflexivity. Qed.
Lemma q_ob_qset_st : forall q st, q_ob (qset_st q st) = q_ob q.
Proof. reflexivity. Qed.
Lemma q_ob_qset_z : forall q z, q_ob (qset_z q z) = q_ob q.
Proof. reflexivity. Qed.
Lemma q_ob_qmode : forall q m, q_ob (qmode q m) = q_ob q.
Proof. reflexivity. Qed.
Lemma q_st_qset_ob : forall q o, q_st (qset_ob q o) = q_st q.
Proof. reflexivity. Qed.
Lemma q_st_qset_br : forall q b, q_st (qset_br q b) = q_st q.
Proof. reflexivity. Qed.
Lemma q_st_qset_st : forall q st, q_st (qset_st q st) = st.
Proof. reflexivity. Qed.
Lemma q_st_qset_z : forall q z, q_st (qset_z q z) = q_st q.
Proof. reflexivity. Qed.
Lemma q_st_qmode : forall q m, q_st (qmode q m) = set_mode (q_st q) m.
Proof. reflexivity. Qed.
Lemma q_mode_qset_ob : forall q o, q_mode (qset_ob q o) = q_mode q.
Proof. reflexivity. Qed.
Lemma q_mode_qset_br : forall q b, q_mode (qset_br q b) = q_mode q.
Proof. reflexivity. Qed.
Lemma q_mode_qset_st : forall q st, q_mode (qset_st q st) = h_mode (s_hdr st).
Proof. reflexivity. Qed.
Lemma q_mode_qmode : forall q m, q_mode (qmode q m) = m.
Proof. reflexivity. Qed.
Lemma hdr_set_bits : forall st v, h_mode (s_hdr (set_bits st v)) = h_mode (s_hdr st).
Proof. reflexivity. Qed.
Lemma hdr_set_hold : forall st v, h_mode (s_hdr (set_hold st v)) = h_mode (s_hdr st).
Proof. reflexivity. Qed.
Lemma hdr_set_back : forall st v, h_mode (s_hdr (set_back st v)) = h_mode (s_hdr st).
Proof. reflexivity. Qed.
Lemma hdr_set_mode : forall st m, h_mode (s_hdr (set_mode st m)) = m.
Proof. reflexivity. Qed.
Lemma hdr_restore : forall q, h_mode (s_hdr (q_st (q_restore q))) = q_mode q.
Proof. reflexivity. Qed.
Lemma sbits_set_bits : forall st v, s_bits (set_bits st v) = v.
Proof. reflexivity. Qed.
Lemma sbits_set_mode : forall st m, s_bits (set_mode st m) = s_bits st.
Proof. reflexivity. Qed.
Lemma sbits_qrestore : forall q, s_bits (q_st (q_restore q)) = br_bits (q_br q).
Proof. reflexivity. Qed.
Lemma q_mode_qbad : forall q m, q_mode (qbad q m) = M_BAD.
Proof. reflexivity. Qed.
Lemma q_br_qbad : forall q m, q_br (qbad q m) = q_br q.
Proof. reflexivity. Qed.
Lemma q_ob_qbad : forall q m, q_ob (qbad q m) = q_ob q.
Proof. reflexivity. Qed.
Lemma q_st_qbad : forall q m, q_st (qbad q m) = set_mode (q_st q) M_BAD.
Proof. reflexivity. Qed.

Ltac lp_norm :=
  repeat first
    [ rewrite q_load_have | rewrite q_load_bits | rewrite q_load_left
    | rewrite q_mode_q_load | rewrite q_st_q_load
    | rewrite q_br_qset_ob | rewrite q_br_qset_br | rewrite q_br_qset_st
    | rewrite q_br_qset_z | rewrite q_br_qmode
    | rewrite q_ob_qset_ob | rewrite q_ob_qset_br | rewrite q_ob_qset_st
    | rewrite q_ob_qset_z | rewrite q_ob_qmode
    | rewrite q_st_qset_ob | rewrite q_st_qset_br | rewrite q_st_qset_st
    | rewrite q_st_qset_z | rewrite q_st_qmode
    | rewrite q_mode_qset_ob | rewrite q_mode_qset_br
    | rewrite q_mode_qset_st | rewrite q_mode_qmode
    | rewrite hdr_set_bits | rewrite hdr_set_hold | rewrite hdr_set_back
    | rewrite hdr_set_mode | rewrite hdr_restore
    | rewrite sbits_set_bits | rewrite sbits_set_mode
    | rewrite sbits_qrestore
    | rewrite q_mode_qbad | rewrite q_br_qbad | rewrite q_ob_qbad
    | rewrite q_st_qbad ];
  cbn [br_have br_bits br_in br_next br_hold o_left o_put o_buf].

Lemma arm_LEN :
  forall q, q_pos q -> q_mode q = M_LEN ->
    (Z.leb 6 (br_have (q_br q)) && Z.leb 258 (o_left (q_ob q)) = true ->
       if_wf_lax (len_args q) /\ if_wf_tbl (len_args q)
       /\ br_have (q_br q) <= 4294967290
       /\ o_left (q_ob q) <= 4294967295) ->
    LcSide (tbl_of (q_st q) (t_lencode (s_tab (q_st q)))) ->
    TblSide (tbl_of (q_st q) (t_distcode (s_tab (q_st q)))) ->
    0 <= w_wnext (s_win (q_st q)) ->
    arm_ok q (inf_LEN q).
Proof.
  intros q Hp Hm Hfast Hlc Htd Hwn. pose proof Hp as (Hh & Hb & Hl).
  assert (Hm' : h_mode (s_hdr (q_st q)) = M_LEN) by exact Hm.
  rewrite inf_LEN_eq. unfold inf_LEN'. cbv zeta.
  destruct (Z.leb 6 (br_have (q_br q)) && Z.leb 258 (o_left (q_ob q)))
    eqn:Egate.
  - (* fast path: the inflate_fast call node *)
    destruct (Hfast eq_refl) as (Hwf & Htbl & Hain & Haout).
    (* the landed [if_model_total] idiom: never destruct the [if_model]
       application (whnf-explosive through the literal fuels) — take the
       answer as an EQUATION and rewrite with it *)
    destruct (if_model_total_lax (len_args q) Hwf) as (y & EM).
    rewrite EM. cbv beta iota.
    pose proof (if_model_bud (len_args q) y Hwf Htbl Hain Haout EM)
      as (Bud & Yai & Yb & Yao & Yh).
    cbn [len_args a_avail_in a_bits a_avail_out] in Bud.
    unfold len_post. cbv zeta.
    destruct (y_exit y) eqn:Eex; cbv beta iota.
    + (* ExLen: mode stays M_LEN, the budget's -1 pays the rank *)
      lp_norm. rewrite Hm. cbv beta iota.
      cbn [arm_ok]. split.
      * unfold q_pos. lp_norm. repeat split; lia.
      * apply rank2_lt' with (m := M_LEN) (m' := M_LEN);
          [exact Hm | lp_norm; exact Hm | apply q_pos_bud, Hp |].
        unfold inf_budget. lp_norm. lia.
    + (* ExType: 16200 -> 16193 descends; paid by the same -1 *)
      lp_norm. cbv beta iota.
      cbn [arm_ok]. split.
      * unfold q_pos. lp_norm. repeat split; lia.
      * apply rank2_lt' with (m := M_LEN) (m' := M_TYPE);
          [exact Hm | lp_norm; reflexivity | apply q_pos_bud, Hp |].
        cbn [inf_mrank]. unfold inf_budget. lp_norm. lia.
    + (* ExBad: BAD ascends; nothing owed *)
      lp_norm. cbv beta iota.
      cbn [arm_ok]. split.
      * unfold q_pos. lp_norm. repeat split; lia.
      * apply rank2_lt' with (m := M_LEN) (m' := M_BAD);
          [exact Hm | lp_norm; reflexivity | apply q_pos_bud, Hp |].
        cbn [inf_mrank]. unfold inf_budget. lp_norm. lia.
  - (* slow path: one decode *)
    destruct Hlc as (Lb0 & Leob & Lval).
    destruct (inf_decode sub_len
                (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
                (t_lenbits (s_tab (q_st q))) (q_br q)) as [h b' nb|b'|]
      eqn:Edec.
    2:{ exact I. }
    2:{ exfalso. exact (inf_decode_no_fuel _ _ _ _ Hh Edec). }
    destruct (inf_decode_ok_facts _ _ _ _ _ _ _ Lb0 Edec)
      as ((i0 & Hhe) & Hnb).
    pose proof (inf_decode_bud _ _ _ _ _ _ _ Edec) as (Ebud & Ehave).
    specialize (Ehave Hh).
    pose proof (inf_decode_bits_nonneg _ _ _ _ _ _ _ Edec) as Ebits.
    cbv zeta.
    destruct (Z.eqb (c_op h) 0) eqn:E0.
    + (* literal -> LIT (ascends) *)
      cbn [arm_ok]. split.
      * unfold q_pos. bsimp. repeat split; lia.
      * apply rank2_lt' with (m := M_LEN) (m' := M_LIT);
          [exact Hm | bsimp; reflexivity | apply q_pos_bud, Hp |].
        cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
    + destruct (negb (Z.eqb (Z.land (c_op h) 32) 0)) eqn:E32.
      * (* end of block -> TYPE (descends): the entry's width pays *)
        apply Bool.negb_true_iff, Z.eqb_neq in E32.
        assert (Hnb1 : 1 <= nb).
        { eapply inf_decode_eob_pos;
            [exact Lb0 | exact Leob | exact Edec |].
          rewrite Hhe in E32 |- *. exact E32. }
        cbn [arm_ok]. split.
        { unfold q_pos. bsimp. repeat split; lia. }
        apply rank2_lt' with (m := M_LEN) (m' := M_TYPE);
          [exact Hm | bsimp; reflexivity | apply q_pos_bud, Hp |].
        cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
      * destruct (negb (Z.eqb (Z.land (c_op h) 64) 0)) eqn:E64.
        { (* invalid -> BAD (ascends) *)
          cbn [arm_ok]. split.
          - unfold q_pos. bsimp. repeat split; lia.
          - apply rank2_lt' with (m := M_LEN) (m' := M_BAD);
              [exact Hm | bsimp; reflexivity | apply q_pos_bud, Hp |].
            cbn [inf_mrank]. unfold inf_budget. bsimp. lia. }
        (* length base: falls through IN-CALL to LENEXT *)
        apply Bool.negb_false_iff, Z.eqb_eq in E64.
        apply Bool.negb_false_iff, Z.eqb_eq in E32.
        apply Z.eqb_neq in E0.
        assert (Hval : 1 <= c_val h).
        { eapply inf_decode_val_pos; [exact Lval | exact Edec | | |];
            rewrite Hhe in E0, E32, E64 |- *; assumption. }
        pose proof (land15_range (c_op h)) as He15.
        eapply (arm_ok_mono _ q).
        2:{ apply arm_LENEXT;
            [ unfold q_pos; bsimp; repeat split; lia
            | reflexivity
            | bsimp; lia
            | bsimp; lia
            | bsimp; lia
            | bsimp; exact Htd ]. }
        apply rank2_le' with (m := M_LEN) (m' := M_LENEXT);
          [ exact Hm | reflexivity
          | cbn [inf_mrank]; unfold inf_budget; bsimp; lia ].
Qed.

(** LEN_ delegates to LEN ([inflate.c:1023-1024]); every premise transports
    by conversion ([qmode] only writes [h_mode], which nothing in
    [len_args]/[LcSide]/[TblSide] reads). *)
Lemma arm_LEN_ :
  forall q, q_pos q -> q_mode q = M_LEN_ ->
    (Z.leb 6 (br_have (q_br q)) && Z.leb 258 (o_left (q_ob q)) = true ->
       if_wf_lax (len_args q) /\ if_wf_tbl (len_args q)
       /\ br_have (q_br q) <= 4294967290
       /\ o_left (q_ob q) <= 4294967295) ->
    LcSide (tbl_of (q_st q) (t_lencode (s_tab (q_st q)))) ->
    TblSide (tbl_of (q_st q) (t_distcode (s_tab (q_st q)))) ->
    0 <= w_wnext (s_win (q_st q)) ->
    arm_ok q (inf_LEN_ q).
Proof.
  intros q Hp Hm Hfast Hlc Htd Hwn.
  unfold inf_LEN_.
  eapply (arm_ok_mono _ q).
  2:{ apply arm_LEN.
      - unfold q_pos. bsimp. exact Hp.
      - reflexivity.
      - exact Hfast.
      - exact Hlc.
      - exact Htd.
      - bsimp. exact Hwn. }
  apply rank2_le' with (m := M_LEN_) (m' := M_LEN);
    [exact Hm | reflexivity |].
  cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
Qed.

(** ** TABLE / LENLENS / CODELENS (2026-08-19, Q4)

    Own accounting first: TABLE spends 14 bits; LENLENS's [ll_go] spends 3
    per written code length; CODELENS's inner [while] budget is
    non-increasing per [cl_step].  Their [it_model] [InfFuel]s die via
    [GtItTotal.it_model_total], whose [LensBounded] premise is maintained
    by the loops themselves over a [b_lens] that starts in range — the
    "one small invariant" ([lens_ok], a mode-conditioned entry premise;
    discharge route: [b_lens] is only ever written by these two arms with
    3-bit reads, [c_val < 16] symbols, in-range repeats, or zeros, from an
    all-zero initial array).

    The happy-path tails fall through IN-CALL (LENLENS -> CODELENS ->
    LEN_), and the tables the tail consumes are built by THIS trip's
    [it_model] — their contracts ([TblSide]/[LcSide]/[if_wf_tbl]/chain
    facts) are it_model-OUTPUT facts, not derivable from any entry premise
    here.  Packaging (option (a), and the same mechanism as the
    termination Section's [Hstep] Variable — "the intended mechanism for a
    dependency this layer does not own"): each arm takes its callee's
    whole obligation as a NAMED premise ([forall q', q_mode q' = <mode> ->
    q_pos q' -> arm_ok q' (<callee> q')]).  Discharge route: the callee's
    arm lemma ([arm_CODELENS] / [arm_LEN_]) plus (i) the it_model output
    contracts (T5 family: [ItGTblCover.it_covers_root_pos], the sub-table
    analogue, [chain_fit], the lext/dext literal bounds) and (ii) the
    reachability facts at the constructed state ([bits < 8],
    [hold < 2^bits], byte-valued buffers) — both living with the
    step_ok_covered discharge, where every named side condition becomes a
    reachability obligation. *)

Definition lens_ok (a : zarr) : Prop := forall i, 0 <= a i <= 15.

Lemma zset_lens_ok :
  forall a i v, lens_ok a -> 0 <= v <= 15 -> lens_ok (zset a i v).
Proof.
  intros a i v Ha Hv j. unfold zset.
  destruct (Z.eqb j i); [exact Hv | apply Ha].
Qed.

Lemma zfill_lens_ok :
  forall n a i v, lens_ok a -> 0 <= v <= 15 -> lens_ok (zfill n a i v).
Proof.
  induction n as [|n IH]; intros a i v Ha Hv; cbn [zfill]; [exact Ha|].
  apply IH; [apply zset_lens_ok; assumption | exact Hv].
Qed.

(** One CODELENS inner-loop trip: reader budget non-increasing,
    [have]/[bits] nonnegative, [lens] range preserved.  [ClLeave] carries
    no obligation (it maps to [InfLeave]); [ClFuel] is dead by
    [inf_fetch_no_fuel]. *)
Lemma cl_step_walk :
  forall t nb tot s,
    TblSide t ->
    0 <= br_have (cl_br s) -> 0 <= br_bits (cl_br s) ->
    lens_ok (cl_lens s) ->
    match cl_step t nb tot s with
    | ClCont s' | ClDone s' | ClBad s' _ =>
        8 * br_have (cl_br s') + br_bits (cl_br s')
          <= 8 * br_have (cl_br s) + br_bits (cl_br s)
        /\ 0 <= br_have (cl_br s') /\ 0 <= br_bits (cl_br s')
        /\ lens_ok (cl_lens s')
    | ClLeave _ => True
    | ClFuel => False
    end.
Proof.
  intros t nb tot s Htbl Hh Hb Hlens. unfold cl_step.
  destruct (Z.leb tot (cl_have s)); cbv beta iota.
  { split; [lia|]. split; [exact Hh|]. split; [exact Hb|]. exact Hlens. }
  destruct (inf_fetch t nb (cl_br s)) as [h b|b|] eqn:Ef; cbv beta iota.
  2:{ exact I. }
  2:{ exfalso. exact (inf_fetch_no_fuel _ _ _ Hh Ef). }
  destruct (inf_fetch_go_entry _ _ _ _ _ _ Ef) as (i0 & Hhe).
  assert (Hcb : 0 <= c_bits h <= 15)
    by (rewrite Hhe; exact (proj1 (Htbl i0))).
  assert (Hcv : 0 <= c_val h < 65536)
    by (rewrite Hhe; exact (proj2 (Htbl i0))).
  pose proof (inf_fetch_ok_bits _ _ _ _ _ Ef) as Hble.
  pose proof Ef as Ef'. apply inf_fetch_bud in Ef' as (Ebud & Ehave).
  specialize (Ehave Hh).
  destruct (Z.ltb (c_val h) 16) eqn:Ev16.
  { apply Z.ltb_lt in Ev16.
    cbn [cl_br cl_lens cl_have].
    rewrite dropbits_have, dropbits_bits.
    split; [lia|]. split; [lia|]. split; [lia|].
    apply zset_lens_ok; [exact Hlens | lia]. }
  destruct (inf_nb (if Z.eqb (c_val h) 16 then c_bits h + 2
                    else if Z.eqb (c_val h) 17 then c_bits h + 3
                    else c_bits h + 7) b) as [b'|b'] eqn:Enb; [|exact I].
  pose proof (inf_nb_ok _ _ _ Enb) as Hneed.
  apply inf_nb_bud in Enb as (Ebud2 & Ebits2 & Ehave2).
  specialize (Ehave2 Ehave).
  cbv zeta.
  destruct (Z.eqb (c_val h) 16) eqn:E16v.
  { cbv beta iota in Hneed |- *.
    destruct (Z.eqb (cl_have s) 0).
    { cbn [cl_br cl_lens cl_have].
      rewrite dropbits_have, dropbits_bits.
      split; [lia|]. split; [lia|]. split; [lia|]. exact Hlens. }
    cbv beta iota.
    destruct (Z.ltb tot (cl_have s
                + (3 + br_bits_of 2 (br_dropbits (c_bits h) b')))).
    { cbn [cl_br cl_lens cl_have].
      rewrite !dropbits_have, !dropbits_bits.
      split; [lia|]. split; [lia|]. split; [lia|]. exact Hlens. }
    cbn [cl_br cl_lens cl_have].
    rewrite !dropbits_have, !dropbits_bits.
    split; [lia|]. split; [lia|]. split; [lia|].
    apply zfill_lens_ok; [exact Hlens | apply Hlens]. }
  destruct (Z.eqb (c_val h) 17) eqn:E17v.
  { cbv beta iota in Hneed |- *.
    destruct (Z.ltb tot (cl_have s
                + (3 + br_bits_of 3 (br_dropbits (c_bits h) b')))).
    { cbn [cl_br cl_lens cl_have].
      rewrite !dropbits_have, !dropbits_bits.
      split; [lia|]. split; [lia|]. split; [lia|]. exact Hlens. }
    cbn [cl_br cl_lens cl_have].
    rewrite !dropbits_have, !dropbits_bits.
    pose proof (bits_of_range 3 (br_dropbits (c_bits h) b') ltac:(lia)) as Hbo.
    split; [lia|]. split; [lia|]. split; [lia|].
    apply zfill_lens_ok; [exact Hlens | lia]. }
  { cbv beta iota in Hneed |- *.
    destruct (Z.ltb tot (cl_have s
                + (11 + br_bits_of 7 (br_dropbits (c_bits h) b')))).
    { cbn [cl_br cl_lens cl_have].
      rewrite !dropbits_have, !dropbits_bits.
      split; [lia|]. split; [lia|]. split; [lia|]. exact Hlens. }
    cbn [cl_br cl_lens cl_have].
    rewrite !dropbits_have, !dropbits_bits.
    pose proof (bits_of_range 7 (br_dropbits (c_bits h) b') ltac:(lia)) as Hbo.
    split; [lia|]. split; [lia|]. split; [lia|].
    apply zfill_lens_ok; [exact Hlens | lia]. }
Qed.

Lemma cl_loop_walk :
  forall m t nb tot s r,
    TblSide t ->
    0 <= br_have (cl_br s) -> 0 <= br_bits (cl_br s) ->
    lens_ok (cl_lens s) ->
    cl_loop m t nb tot s = Some r ->
    match r with
    | ClDone s' | ClBad s' _ =>
        8 * br_have (cl_br s') + br_bits (cl_br s')
          <= 8 * br_have (cl_br s) + br_bits (cl_br s)
        /\ 0 <= br_have (cl_br s') /\ 0 <= br_bits (cl_br s')
        /\ lens_ok (cl_lens s')
    | ClLeave _ => True
    | ClCont _ => True
    | ClFuel => False
    end.
Proof.
  induction m as [|m IH]; intros t nb tot s r Htbl Hh Hb Hlens H;
    [cbn [cl_loop] in H; discriminate|].
  rewrite cl_loop_S in H.
  pose proof (cl_step_walk t nb tot s Htbl Hh Hb Hlens) as HS.
  destruct (cl_step t nb tot s) as [s1|s1|s1 m1|s1|] eqn:ES.
  - destruct HS as (S1 & S2 & S3 & S4).
    pose proof (IH t nb tot s1 r Htbl S2 S3 S4 H) as HR.
    destruct r as [s'|s'|s' m2|s'|]; try exact HR;
      destruct HR as (R1 & R2 & R3 & R4);
      (split; [lia|]); (split; [lia|]); (split; [lia|]); exact R4.
  - injection H as H; subst r. cbv beta iota. exact HS.
  - injection H as H; subst r. cbv beta iota. exact HS.
  - injection H as H; subst r. cbv beta iota. exact I.
  - contradiction HS.
Qed.

(** LENLENS's first [while]: 3 bits per written length, values 3-bit. *)
Lemma ll_go_walk :
  forall f ncode have lens b,
    0 <= br_have b -> 0 <= br_bits b -> lens_ok lens ->
    match ll_go f ncode have lens b with
    | LlOk hv ls b' =>
        8 * br_have b' + br_bits b' <= 8 * br_have b + br_bits b
        /\ 0 <= br_have b' /\ 0 <= br_bits b' /\ lens_ok ls
    | LlLeave _ _ _ => True
    end.
Proof.
  induction f as [|f IH]; intros ncode have lens b Hh Hb Hlens;
    cbn [ll_go].
  - split; [lia|]. split; [lia|]. split; [lia|]. exact Hlens.
  - destruct (Z.ltb have ncode); cbv beta iota;
      [|split; [lia|]; split; [lia|]; split; [lia|]; exact Hlens].
    destruct (inf_nb 3 b) as [b'|b'] eqn:Enb; cbv beta iota; [|exact I].
    pose proof (inf_nb_ok _ _ _ Enb) as H3.
    apply inf_nb_bud in Enb as (E1 & E2 & E3). specialize (E3 Hh).
    pose proof (bits_of_range 3 b' ltac:(lia)) as Hbo.
    assert (Hv3 : 0 <= br_bits_of 3 b' <= 15) by lia.
    assert (Hh' : 0 <= br_have (br_dropbits 3 b'))
      by (rewrite dropbits_have; lia).
    assert (Hb' : 0 <= br_bits (br_dropbits 3 b'))
      by (rewrite dropbits_bits; lia).
    pose proof (IH ncode (have + 1)
                  (zset lens (inf_order have) (br_bits_of 3 b'))
                  (br_dropbits 3 b') Hh' Hb'
                  (zset_lens_ok _ _ _ Hlens Hv3)) as HR.
    destruct (ll_go f ncode (have + 1)
                (zset lens (inf_order have) (br_bits_of 3 b'))
                (br_dropbits 3 b')) as [hv ls b2|hv ls b2]; [|exact I].
    destruct HR as (R1 & R2 & R3 & R4).
    rewrite dropbits_have, dropbits_bits in R1.
    split; [lia|]. split; [lia|]. split; [lia|]. exact R4.
Qed.

Lemma ll_zero_walk :
  forall f have lens, lens_ok lens -> lens_ok (snd (ll_zero f have lens)).
Proof.
  induction f as [|f IH]; intros have lens H; cbn [ll_zero snd].
  - exact H.
  - destruct (Z.ltb have 19); cbv beta iota; [|exact H].
    apply IH. apply zset_lens_ok; [exact H | lia].
Qed.

Lemma arm_CODELENS :
  forall c q, q_pos q -> q_mode q = M_CODELENS ->
    TblSide (tbl_of (q_st q) (t_lencode (s_tab (q_st q)))) ->
    lens_ok (b_lens (s_bld (q_st q))) ->
    0 <= b_have (s_bld (q_st q)) ->
    0 <= b_nlen (s_bld (q_st q)) -> 0 <= b_ndist (s_bld (q_st q)) ->
    (forall q', q_mode q' = M_LEN_ -> q_pos q' ->
       arm_ok q' (inf_LEN_ q')) ->
    arm_ok q (inf_CODELENS c q).
Proof.
  intros c q Hp Hm Htl Hlens Hhave Hnlen Hndist HLEN.
  pose proof Hp as (Hh & Hb & Hl).
  unfold inf_CODELENS. cbv zeta beta.
  destruct (cl_loop_at_codelens_fuel
              (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
              (t_lenbits (s_tab (q_st q)))
              (b_nlen (s_bld (q_st q)) + b_ndist (s_bld (q_st q)))
              {| cl_have := b_have (s_bld (q_st q));
                 cl_lens := b_lens (s_bld (q_st q));
                 cl_br := q_br q |}
              ltac:(cbn [cl_br]; lia) ltac:(cbn [cl_have]; lia))
    as (r & Hr & Hexit).
  rewrite Hr. cbv beta iota.
  pose proof (cl_loop_walk
                (S (Z.to_nat (b_nlen (s_bld (q_st q))
                              + b_ndist (s_bld (q_st q)))))
                (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
                (t_lenbits (s_tab (q_st q)))
                (b_nlen (s_bld (q_st q)) + b_ndist (s_bld (q_st q)))
                {| cl_have := b_have (s_bld (q_st q));
                   cl_lens := b_lens (s_bld (q_st q));
                   cl_br := q_br q |} r Htl Hh Hb Hlens Hr) as HW.
  cbn [cl_br cl_lens cl_have] in HW.
  destruct r as [s1|s1|s1 m1|s1|]; cbn [cl_exit] in Hexit;
    try contradiction; [| |exact I].
  - (* ClDone: the table builds, then the LEN_ tail *)
    destruct HW as (W1 & W2 & W3 & W4).
    destruct (Z.eqb (cl_lens s1 256) 0).
    { cbn [arm_ok]. split.
      - unfold q_pos. bsimp. repeat split; lia.
      - apply rank2_lt' with (m := M_CODELENS) (m' := M_BAD);
          [exact Hm | bsimp; reflexivity | apply q_pos_bud, Hp |].
        cbn [inf_mrank]. unfold inf_budget. bsimp. lia. }
    unfold inf_table.
    assert (HLB1 : LensBounded (cl_lens s1) (b_nlen (s_bld (q_st q))))
      by (intros i _; apply W4).
    match goal with
    | |- context [it_model CT_LENS ?l ?cs ?rt ?t0] =>
        remember (it_model CT_LENS l cs rt t0) as R1 eqn:EI1
    end.
    destruct R1 as [o1|].
    2:{ exfalso.
        exact (it_model_total _ _ _ _ _ Hnlen HLB1 (eq_sym EI1)). }
    cbv beta iota zeta.
    destruct (negb (Z.eqb (o_ret o1) 0)).
    { cbn [arm_ok]. split.
      - unfold q_pos. bsimp. repeat split; lia.
      - apply rank2_lt' with (m := M_CODELENS) (m' := M_BAD);
          [exact Hm | bsimp; reflexivity | apply q_pos_bud, Hp |].
        cbn [inf_mrank]. unfold inf_budget. bsimp. lia. }
    assert (HLB2 : LensBounded (fun i => cl_lens s1 (i + b_nlen (s_bld (q_st q))))
                     (b_ndist (s_bld (q_st q))))
      by (intros i _; cbv beta; apply W4).
    match goal with
    | |- context [it_model CT_DISTS ?l ?cs ?rt ?t0] =>
        remember (it_model CT_DISTS l cs rt t0) as R2 eqn:EI2
    end.
    destruct R2 as [o2|].
    2:{ exfalso.
        exact (it_model_total _ _ _ _ _ Hndist HLB2 (eq_sym EI2)). }
    cbv beta iota zeta.
    destruct (negb (Z.eqb (o_ret o2) 0)).
    { cbn [arm_ok]. split.
      - unfold q_pos. bsimp. repeat split; lia.
      - apply rank2_lt' with (m := M_CODELENS) (m' := M_BAD);
          [exact Hm | bsimp; reflexivity | apply q_pos_bud, Hp |].
        cbn [inf_mrank]. unfold inf_budget. bsimp. lia. }
    destruct (Z.eqb (n_flush c) Z_TREES); [exact I|].
    eapply (arm_ok_mono _ q).
    2:{ apply HLEN; [bsimp; reflexivity |].
        unfold q_pos. bsimp. repeat split; lia. }
    apply rank2_le' with (m := M_CODELENS) (m' := M_LEN_);
      [exact Hm | bsimp; reflexivity |].
    cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
  - (* ClBad -> BAD (ascends, budget non-increasing) *)
    destruct HW as (W1 & W2 & W3 & W4).
    cbn [arm_ok]. split.
    + unfold q_pos. bsimp. repeat split; lia.
    + apply rank2_lt' with (m := M_CODELENS) (m' := M_BAD);
        [exact Hm | bsimp; reflexivity | apply q_pos_bud, Hp |].
      cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
Qed.

Lemma arm_LENLENS :
  forall c q, q_pos q -> q_mode q = M_LENLENS ->
    lens_ok (b_lens (s_bld (q_st q))) ->
    (forall q', q_mode q' = M_CODELENS -> q_pos q' ->
       arm_ok q' (inf_CODELENS c q')) ->
    arm_ok q (inf_LENLENS c q).
Proof.
  intros c q Hp Hm Hlens HCL. pose proof Hp as (Hh & Hb & Hl).
  unfold inf_LENLENS. cbv zeta.
  pose proof (ll_go_walk 19 (b_ncode (s_bld (q_st q)))
                (b_have (s_bld (q_st q))) (b_lens (s_bld (q_st q)))
                (q_br q) Hh Hb Hlens) as HW.
  match goal with
  | |- context [ll_go ?f ?nc ?hv0 ?ls0 ?b0] =>
      remember (ll_go f nc hv0 ls0 b0) as LG eqn:ELG
  end.
  destruct LG as [hv ls b|hv ls b]; [|exact I].
  destruct HW as (W1 & W2 & W3 & W4).
  remember (ll_zero 19 hv ls) as LZ eqn:EZ.
  destruct LZ as [hv1 ls1]. cbv beta iota.
  assert (Hls1 : lens_ok ls1).
  { pose proof (ll_zero_walk 19 hv ls W4) as HZ. rewrite <- EZ in HZ.
    exact HZ. }
  unfold inf_table.
  assert (HLB : LensBounded ls1 19) by (intros i _; apply Hls1).
  match goal with
  | |- context [it_model CT_CODES ?l ?cs ?rt ?t0] =>
      remember (it_model CT_CODES l cs rt t0) as R1 eqn:EI1
  end.
  destruct R1 as [o1|].
  2:{ exfalso.
      assert (Hc19 : 0 <= 19) by lia.
      exact (it_model_total _ _ _ _ _ Hc19 HLB (eq_sym EI1)). }
  cbv beta iota zeta.
  destruct (negb (Z.eqb (o_ret o1) 0)).
  { cbn [arm_ok]. split.
    - unfold q_pos. bsimp. repeat split; lia.
    - apply rank2_lt' with (m := M_LENLENS) (m' := M_BAD);
        [exact Hm | bsimp; reflexivity | apply q_pos_bud, Hp |].
      cbn [inf_mrank]. unfold inf_budget. bsimp. lia. }
  eapply (arm_ok_mono _ q).
  2:{ apply HCL; [bsimp; reflexivity |].
      unfold q_pos. bsimp. repeat split; lia. }
  apply rank2_le' with (m := M_LENLENS) (m' := M_CODELENS);
    [exact Hm | bsimp; reflexivity |].
  cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
Qed.

Lemma arm_TABLE :
  forall c q, q_pos q -> q_mode q = M_TABLE ->
    lens_ok (b_lens (s_bld (q_st q))) ->
    (forall q', q_mode q' = M_CODELENS -> q_pos q' ->
       arm_ok q' (inf_CODELENS c q')) ->
    arm_ok q (inf_TABLE c q).
Proof.
  intros c q Hp Hm Hlens HCL. pose proof Hp as (Hh & Hb & Hl).
  unfold inf_TABLE.
  destruct (inf_nb 14 (q_br q)) as [b|b] eqn:Enb; [|exact I].
  pose proof (inf_nb_ok _ _ _ Enb) as E14.
  apply inf_nb_bud in Enb as (E1 & E2 & E3). specialize (E3 Hh).
  cbv zeta.
  destruct (Z.ltb 286 (br_bits_of 5 b + 257)
            || Z.ltb 30 (br_bits_of 5 (br_dropbits 5 b) + 1)).
  { cbn [arm_ok]. split.
    - unfold q_pos. bsimp. repeat split; lia.
    - apply rank2_lt' with (m := M_TABLE) (m' := M_BAD);
        [exact Hm | bsimp; reflexivity | apply q_pos_bud, Hp |].
      cbn [inf_mrank]. unfold inf_budget. bsimp. lia. }
  eapply (arm_ok_mono _ q).
  2:{ apply arm_LENLENS.
      - unfold q_pos. bsimp. repeat split; lia.
      - bsimp. reflexivity.
      - cbn [qmode qset_st q_st set_mode set_have set_ncode set_ndist
             set_nlen s_bld b_lens]. exact Hlens.
      - exact HCL. }
  apply rank2_le' with (m := M_TABLE) (m' := M_LENLENS);
    [exact Hm | bsimp; reflexivity |].
  cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
Qed.


Definition match_side (q : InfSt) : Prop :=
  1 <= u_length (s_cur (q_st q))
  /\ 0 <= u_offset (s_cur (q_st q)) < 4294967296
  /\ 0 <= w_wnext (s_win (q_st q)).

(** ** [step_ok_covered], 32/32 — every mode of [inf_step] discharged.

    The premise list is option-(a): per-arm minimal side conditions,
    mode-conditioned, each named above at its arm with its discharge
    route.  The three in-call tails (LENLENS -> CODELENS -> LEN_) appear
    as callee obligations. *)
Theorem step_ok_covered :
  forall c q,
    q_pos q ->
    0 <= u_length (s_cur (q_st q)) ->
    (q_mode q = M_MATCH -> match_side q) ->
    (* the gzip header arms (2026-08-19): a byte-valued input window, and a
       nonnegative accumulator where EXLEN reads it into [state->length].
       DISCHARGE ROUTE (TL ruling: every premise names its route): real
       inputs are [zlist] byte lists (Codec/ZRepro plumbing), and the
       accumulator is 0 after every INITBITS and byte-built otherwise —
       reachability facts of the mode machine's own writes. *)
    (q_mode q = M_FLAGS \/ q_mode q = M_TIME \/ q_mode q = M_OS
       \/ q_mode q = M_EXLEN ->
     (forall j, 0 <= br_in (q_br q) j) /\ 0 <= br_hold (q_br q)) ->
    (* the LEN-chain arms below LEN (2026-08-19): [arm_MATCH]'s entry
       contract, a nonnegative extra-bits count, the live distance table's
       [TblSide], and DISTEXT's offset headroom.
       DISCHARGE ROUTES (TL ruling, per premise): the u_length/u_extra/
       u_offset facts are [Z.land _ 15] / table-value WRITE-SITE facts of
       the LEN/DIST arms themselves; [TblSide] is table provenance — via
       the it_model/ptr family (GtPtrProv.ptr_model_wf's pattern,
       [it_fill]'s [len - drop] widths + [u16] value truncation) for
       dynamic tables, and by [vm_compute] at [lenfix]/[distfix] for the
       fixed ones; the wnext bound is [inflateReset]'s zero write plus
       [updatewindow]'s range. *)
    (q_mode q = M_LENEXT \/ q_mode q = M_DIST \/ q_mode q = M_DISTEXT ->
       1 <= u_length (s_cur (q_st q)) /\ 0 <= w_wnext (s_win (q_st q))) ->
    (q_mode q = M_LENEXT \/ q_mode q = M_DISTEXT ->
       0 <= u_extra (s_cur (q_st q)) <= 15) ->
    (q_mode q = M_LENEXT \/ q_mode q = M_DIST ->
       TblSide (tbl_of (q_st q) (t_distcode (s_tab (q_st q))))) ->
    (q_mode q = M_DISTEXT ->
       0 <= u_offset (s_cur (q_st q))
       /\ u_offset (s_cur (q_st q)) + Z.shiftl 1 (u_extra (s_cur (q_st q)))
          <= 4294967296) ->
    (* LEN / LEN_ (2026-08-19, Q4 continuation).  DISCHARGE ROUTES: the
       gate-conditioned call contract is [if_wf] (measured on 560 recorded
       entry states; its table conjuncts and [if_wf_tbl] are it_model
       provenance — see [if_walk_ok]'s per-conjunct routes above) plus a
       2^24 cap on the avails (byte counts of live buffers); [LcSide] and
       [TblSide] as at their definitions; wnext as at the LENEXT chain. *)
    (q_mode q = M_LEN \/ q_mode q = M_LEN_ ->
       (Z.leb 6 (br_have (q_br q)) && Z.leb 258 (o_left (q_ob q)) = true ->
          if_wf_lax (len_args q) /\ if_wf_tbl (len_args q)
          /\ br_have (q_br q) <= 4294967290
          /\ o_left (q_ob q) <= 4294967295)
       /\ LcSide (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
       /\ TblSide (tbl_of (q_st q) (t_distcode (s_tab (q_st q))))
       /\ 0 <= w_wnext (s_win (q_st q))) ->
    (* TABLE / LENLENS / CODELENS (2026-08-19, Q4 continuation).
       DISCHARGE ROUTES: [lens_ok] is the write-site invariant of the two
       arms' own loops from an all-zero initial array; the b_* bounds are
       TABLE's own [BITS(5)+257]/[BITS(5)+1]/write-site facts; the
       CODELENS-entry [TblSide] is it_model output provenance (the
       codelens table LENLENS just built); the two callee obligations are
       the [arm_CODELENS]/[arm_LEN_] lemmas plus it_model output contracts
       and constructed-state reachability — see the section header at
       [arm_CODELENS]. *)
    (q_mode q = M_TABLE \/ q_mode q = M_LENLENS \/ q_mode q = M_CODELENS ->
       lens_ok (b_lens (s_bld (q_st q)))) ->
    (q_mode q = M_TABLE \/ q_mode q = M_LENLENS ->
       forall q', q_mode q' = M_CODELENS -> q_pos q' ->
         arm_ok q' (inf_CODELENS c q')) ->
    (q_mode q = M_CODELENS ->
       TblSide (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
       /\ 0 <= b_have (s_bld (q_st q))
       /\ 0 <= b_nlen (s_bld (q_st q)) /\ 0 <= b_ndist (s_bld (q_st q))
       /\ (forall q', q_mode q' = M_LEN_ -> q_pos q' ->
             arm_ok q' (inf_LEN_ q'))) ->
    step_ok c q.
Proof.
  intros c q Hp Hlen Hms Hgz Hcs Hce Hct Hco Hln Hlens3 Hcl Hcod.
  unfold step_ok, inf_step.
  destruct (q_mode q) eqn:Hm; try exact I.
  - exact (arm_HEAD c q Hp Hm).
  - exact (arm_FLAGS q Hp Hm (proj1 (Hgz (or_introl eq_refl)))).
  - exact (arm_TIME q Hp Hm (proj1 (Hgz (or_intror (or_introl eq_refl))))).
  - exact (arm_OS q Hp Hm
             (proj1 (Hgz (or_intror (or_intror (or_introl eq_refl)))))).
  - exact (arm_EXLEN q Hp Hm
             (proj2 (Hgz (or_intror (or_intror (or_intror eq_refl)))))
             (proj1 (Hgz (or_intror (or_intror (or_intror eq_refl)))))).
  - exact (arm_EXTRA q Hp Hm (fun _ => Hlen)).
  - exact (arm_NAME q Hp Hm).
  - exact (arm_COMMENT q Hp Hm).
  - exact (arm_HCRC q Hp Hm).
  - exact (arm_DICTID c q Hp Hm).
  - exact (arm_DICT c q Hp Hm).
  - exact (arm_TYPE c q M_TYPE Hp Hm ltac:(cbn [inf_mrank]; lia)).
  - exact (arm_TYPEDO c q M_TYPEDO Hp Hm ltac:(cbn [inf_mrank]; lia)).
  - exact (arm_STORED c q Hp Hm).
  - exact (arm_COPY_ q Hp Hm Hlen).
  - exact (arm_COPY q M_COPY Hp Hm ltac:(cbn [inf_mrank]; lia) Hlen).
  - exact (arm_TABLE c q Hp Hm (Hlens3 (or_introl eq_refl))
             (Hcl (or_introl eq_refl))).
  - exact (arm_LENLENS c q Hp Hm
             (Hlens3 (or_intror (or_introl eq_refl)))
             (Hcl (or_intror eq_refl))).
  - destruct (Hcod eq_refl) as (C1 & C2 & C3 & C4 & C5).
    exact (arm_CODELENS c q Hp Hm C1
             (Hlens3 (or_intror (or_intror eq_refl))) C2 C3 C4 C5).
  - destruct (Hln (or_intror eq_refl)) as (L1 & L2 & L3 & L4).
    exact (arm_LEN_ q Hp Hm L1 L2 L3 L4).
  - destruct (Hln (or_introl eq_refl)) as (L1 & L2 & L3 & L4).
    exact (arm_LEN q Hp Hm L1 L2 L3 L4).
  - exact (arm_LENEXT q Hp Hm (Hce (or_introl eq_refl))
             (proj1 (Hcs (or_introl eq_refl)))
             (proj2 (Hcs (or_introl eq_refl)))
             (Hct (or_introl eq_refl))).
  - exact (arm_DIST q Hp Hm
             (proj1 (Hcs (or_intror (or_introl eq_refl))))
             (proj2 (Hcs (or_intror (or_introl eq_refl))))
             (Hct (or_intror eq_refl))).
  - exact (arm_DISTEXT q Hp Hm (Hce (or_intror eq_refl))
             (proj1 (Hcs (or_intror (or_intror eq_refl))))
             (proj1 (Hco eq_refl)) (proj2 (Hco eq_refl))
             (proj2 (Hcs (or_intror (or_intror eq_refl))))).
  - destruct (Hms eq_refl) as (H1 & H2 & H3).
    exact (arm_MATCH q M_MATCH Hp Hm ltac:(cbn [inf_mrank]; lia) H1 H2 H3).
  - exact (arm_LIT q M_LIT Hp Hm ltac:(cbn [inf_mrank]; lia)).
  - exact (arm_CHECK q Hp Hm).
  - exact (arm_LENGTH q Hp Hm).
Qed.

(** ** CAP relaxation (pres lane, 2026-08-19)

    The 2^24 caps this chain used to carry were HEADROOM; the true
    ceilings are [if_finish]'s u32 give-back windows
    ([avail_in + 5 < 2^32], [avail_out < 2^32] — the C's own unsigned
    write-backs).  The premises above are relaxed in place (every [lia]
    has slack to the ceilings); the original 2^24 forms stay derivable —
    kept here as corollaries so an in-flight consumer of the measured
    contract needs no edit. *)
Corollary if_model_bud_cap24 :
  forall a y,
    if_wf_lax a -> if_wf_tbl a ->
    a_avail_in a <= 16777216 -> a_avail_out a <= 16777216 ->
    if_model a = Some y ->
    8 * y_avail_in y + y_bits y + y_avail_out y
      <= 8 * a_avail_in a + a_bits a + a_avail_out a - 1
    /\ 0 <= y_avail_in y /\ 0 <= y_bits y /\ 0 <= y_avail_out y
    /\ 0 <= y_hold y.
Proof.
  intros a y Hwf Htbl Hain Haout HM.
  apply if_model_bud; try assumption; lia.
Qed.

Corollary step_ok_covered_cap24 :
  forall c q,
    q_pos q ->
    0 <= u_length (s_cur (q_st q)) ->
    (q_mode q = M_MATCH -> match_side q) ->
    (* the gzip header arms (2026-08-19): a byte-valued input window, and a
       nonnegative accumulator where EXLEN reads it into [state->length].
       DISCHARGE ROUTE (TL ruling: every premise names its route): real
       inputs are [zlist] byte lists (Codec/ZRepro plumbing), and the
       accumulator is 0 after every INITBITS and byte-built otherwise —
       reachability facts of the mode machine's own writes. *)
    (q_mode q = M_FLAGS \/ q_mode q = M_TIME \/ q_mode q = M_OS
       \/ q_mode q = M_EXLEN ->
     (forall j, 0 <= br_in (q_br q) j) /\ 0 <= br_hold (q_br q)) ->
    (* the LEN-chain arms below LEN (2026-08-19): [arm_MATCH]'s entry
       contract, a nonnegative extra-bits count, the live distance table's
       [TblSide], and DISTEXT's offset headroom.
       DISCHARGE ROUTES (TL ruling, per premise): the u_length/u_extra/
       u_offset facts are [Z.land _ 15] / table-value WRITE-SITE facts of
       the LEN/DIST arms themselves; [TblSide] is table provenance — via
       the it_model/ptr family (GtPtrProv.ptr_model_wf's pattern,
       [it_fill]'s [len - drop] widths + [u16] value truncation) for
       dynamic tables, and by [vm_compute] at [lenfix]/[distfix] for the
       fixed ones; the wnext bound is [inflateReset]'s zero write plus
       [updatewindow]'s range. *)
    (q_mode q = M_LENEXT \/ q_mode q = M_DIST \/ q_mode q = M_DISTEXT ->
       1 <= u_length (s_cur (q_st q)) /\ 0 <= w_wnext (s_win (q_st q))) ->
    (q_mode q = M_LENEXT \/ q_mode q = M_DISTEXT ->
       0 <= u_extra (s_cur (q_st q)) <= 15) ->
    (q_mode q = M_LENEXT \/ q_mode q = M_DIST ->
       TblSide (tbl_of (q_st q) (t_distcode (s_tab (q_st q))))) ->
    (q_mode q = M_DISTEXT ->
       0 <= u_offset (s_cur (q_st q))
       /\ u_offset (s_cur (q_st q)) + Z.shiftl 1 (u_extra (s_cur (q_st q)))
          <= 4294967296) ->
    (* LEN / LEN_ (2026-08-19, Q4 continuation).  DISCHARGE ROUTES: the
       gate-conditioned call contract is [if_wf] (measured on 560 recorded
       entry states; its table conjuncts and [if_wf_tbl] are it_model
       provenance — see [if_walk_ok]'s per-conjunct routes above) plus a
       2^24 cap on the avails (byte counts of live buffers); [LcSide] and
       [TblSide] as at their definitions; wnext as at the LENEXT chain. *)
    (q_mode q = M_LEN \/ q_mode q = M_LEN_ ->
       (Z.leb 6 (br_have (q_br q)) && Z.leb 258 (o_left (q_ob q)) = true ->
          if_wf_lax (len_args q) /\ if_wf_tbl (len_args q)
          /\ br_have (q_br q) <= 16777216 /\ o_left (q_ob q) <= 16777216)
       /\ LcSide (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
       /\ TblSide (tbl_of (q_st q) (t_distcode (s_tab (q_st q))))
       /\ 0 <= w_wnext (s_win (q_st q))) ->
    (* TABLE / LENLENS / CODELENS (2026-08-19, Q4 continuation).
       DISCHARGE ROUTES: [lens_ok] is the write-site invariant of the two
       arms' own loops from an all-zero initial array; the b_* bounds are
       TABLE's own [BITS(5)+257]/[BITS(5)+1]/write-site facts; the
       CODELENS-entry [TblSide] is it_model output provenance (the
       codelens table LENLENS just built); the two callee obligations are
       the [arm_CODELENS]/[arm_LEN_] lemmas plus it_model output contracts
       and constructed-state reachability — see the section header at
       [arm_CODELENS]. *)
    (q_mode q = M_TABLE \/ q_mode q = M_LENLENS \/ q_mode q = M_CODELENS ->
       lens_ok (b_lens (s_bld (q_st q)))) ->
    (q_mode q = M_TABLE \/ q_mode q = M_LENLENS ->
       forall q', q_mode q' = M_CODELENS -> q_pos q' ->
         arm_ok q' (inf_CODELENS c q')) ->
    (q_mode q = M_CODELENS ->
       TblSide (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
       /\ 0 <= b_have (s_bld (q_st q))
       /\ 0 <= b_nlen (s_bld (q_st q)) /\ 0 <= b_ndist (s_bld (q_st q))
       /\ (forall q', q_mode q' = M_LEN_ -> q_pos q' ->
             arm_ok q' (inf_LEN_ q'))) ->
    step_ok c q.
Proof.
  intros c q Hp Hlen Hms Hgz Hcs Hce Hct Hco Hln Hlens3 Hcl Hcod.
  apply step_ok_covered; try assumption.
  intros Hm. destruct (Hln Hm) as (Hg & L2 & L3 & L4).
  split; [|split; [exact L2 | split; [exact L3 | exact L4]]].
  intros Hgate. destruct (Hg Hgate) as (A & B & C & D).
  split; [exact A|]. split; [exact B|]. split; lia.
Qed.
