(** CresChain.v -- the hash-chain soundness invariant behind [cRes].

    [longest_match] (deflate.c:1439-1471) never compares [scan[2]]; [hash3_det]
    says it need not, PROVIDED every position it dereferences on the chain for
    bucket [h] really hashes to [h].  This file proves that, in the form the
    measurement on the shipped binary produced:

      Live(h) = the maximal prefix p_0, p_1, ... of  H[h], P[p & wmask], ...
                with p_0 >= limit and p_i > limit for i >= 1
                (limit = max 0 (strstart - MAX_DIST), the loop's own bound)

      (1) forall h, forall p in Live(h),  h3 p = h
      (2) Live(h) is strictly decreasing
      (3) at a longest_match entry: ins_h = h3 strstart,
          H[ins_h] = strstart, P[strstart & wmask] = cur_match
      (4) the recycling lemma: P[i] is authoritative for the unique
          p = i (mod w_size) with p > strstart - w_size, which is what carries
          the invariant through slide_hash

    The measurement that motivated the prefix shape: stated over the WHOLE
    chain (1) is false, and false at positions well inside MAX_DIST of
    strstart, because [prev] has only [w_size] slots for a [2*w_size] position
    space and the insert at [p + w_size] recycles the slot that held the
    predecessor of [p].  The loop can never observe that -- reaching [p]
    needs [p > limit] while the recycle needs [strstart >= p + w_size], i.e.
    [p <= limit - 262] -- which is exactly why the prefix qualifier, and not a
    distance qualifier, is the right one.

    Everything is proved; there is no Admitted/Axiom/Parameter/Hypothesis at
    top level.  Dependencies this file does not own are Section variables,
    which discharge into universal quantification. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
     Base Chunk Deflate.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** * 1. Mask arithmetic

    [p & (w_size - 1)] is the only non-linear operation in the family; every
    fact the chain reasoning needs about it is here, so that nothing below has
    to see a [mod]. *)
Section MaskArith.
  Variables ws k : Z.
  Hypothesis Hk : 0 <= k.
  Hypothesis Hws : ws = 2 ^ k.

  Lemma ws_pos : 0 < ws.
  Proof. subst ws. apply Z.pow_pos_nonneg; lia. Qed.

  Lemma mask_mod : forall p, Z.land p (ws - 1) = p mod ws.
  Proof.
    intros p. subst ws.
    replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia).
    apply Z.land_ones; lia.
  Qed.

  Lemma mask_range : forall p, 0 <= Z.land p (ws - 1) < ws.
  Proof.
    intros p. rewrite mask_mod. apply Z.mod_pos_bound, ws_pos.
  Qed.

  (** the slide moves every position down by [w_size] and leaves its slot
      alone -- half of the recycling lemma *)
  Lemma mask_sub : forall p, Z.land (p - ws) (ws - 1) = Z.land p (ws - 1).
  Proof.
    intros p. rewrite !mask_mod.
    replace (p - ws) with (p + (-1) * ws) by ring.
    apply Z.mod_add. pose proof ws_pos. lia.
  Qed.

  (** the other half: inside any window of [w_size] consecutive positions the
      slot index is injective, so a live position owns its slot *)
  Lemma mask_inj : forall lo p q,
    lo < p <= lo + ws -> lo < q <= lo + ws ->
    Z.land p (ws - 1) = Z.land q (ws - 1) -> p = q.
  Proof.
    intros lo p q Hp Hq E. rewrite !mask_mod in E.
    pose proof ws_pos as Hpos.
    assert (Hd : (p - q) mod ws = 0).
    { rewrite Zminus_mod, E, Z.sub_diag. apply Zmod_0_l. }
    apply Z.mod_divide in Hd; [| lia].
    destruct Hd as [c Hc].
    destruct (Z.lt_trichotomy c 0) as [H1|[H1|H1]]; nia.
  Qed.
End MaskArith.

(** * 2. Bit lemmas for the rolling hash

    [UPDATE_HASH] keeps only [hash_bits] bits, and [hash_shift] is
    [ceil(hash_bits/3)], so a byte that entered three updates ago has been
    shifted clean out.  That is what makes [ins_h] equal to the 3-byte hash of
    the CURRENT position rather than of some longer suffix. *)
Lemma mask_bit_lt : forall n i, 0 <= i < n -> Z.testbit (2 ^ n - 1) i = true.
Proof.
  intros n i H.
  replace (2 ^ n - 1) with (Z.ones n) by (rewrite Z.ones_equiv; lia).
  apply Z.ones_spec_low; lia.
Qed.

Lemma mask_bit_ge : forall n i, 0 <= n <= i -> Z.testbit (2 ^ n - 1) i = false.
Proof.
  intros n i H.
  replace (2 ^ n - 1) with (Z.ones n) by (rewrite Z.ones_equiv; lia).
  apply Z.ones_spec_high; lia.
Qed.

Lemma agree_shift :
  forall s n x y, 0 <= s -> 0 <= n ->
    (forall i, 0 <= i < n - s -> Z.testbit x i = Z.testbit y i) ->
    Z.land (Z.shiftl x s) (2 ^ n - 1) = Z.land (Z.shiftl y s) (2 ^ n - 1).
Proof.
  intros s n x y Hs Hn Hag.
  apply Z.bits_inj'; intros i Hi.
  rewrite !Z.land_spec, !Z.shiftl_spec by lia.
  destruct (Z.ltb_spec i n) as [Hlt|Hge].
  - rewrite mask_bit_lt by lia. rewrite !andb_true_r.
    destruct (Z.ltb_spec i s) as [Hsi|Hsi].
    + rewrite !Z.testbit_neg_r by lia. reflexivity.
    + apply Hag. lia.
  - rewrite mask_bit_ge by lia. now rewrite !andb_false_r.
Qed.

Section Rolling.
  Variable g : DeflGeom.
  Variable n : Z.
  Hypothesis Hn : 0 <= n.
  Hypothesis Hs : 0 <= dg_hash_shift g.
  Hypothesis Hm : dg_hash_mask g = 2 ^ n - 1.
  Hypothesis Hcover : n <= 3 * dg_hash_shift g.

  Local Notation s := (dg_hash_shift g).

  Lemma uh_low_bits :
    forall a b i, 0 <= i < n - 2 * s ->
      Z.testbit (update_hash g a b) i = Z.testbit b i.
  Proof.
    intros a b i Hi. unfold update_hash. rewrite Hm.
    rewrite Z.land_spec, Z.lxor_spec, Z.shiftl_spec by lia.
    rewrite mask_bit_lt by lia.
    rewrite (Z.testbit_neg_r a (i - s)) by lia.
    now rewrite andb_true_r.
  Qed.

  Lemma uh_cong_shift :
    forall x y d,
      (forall i, 0 <= i < n - s -> Z.testbit x i = Z.testbit y i) ->
      update_hash g x d = update_hash g y d.
  Proof.
    intros x y d Hag. unfold update_hash. rewrite Hm.
    rewrite !land_lxor_distr. f_equal.
    apply agree_shift; try lia. exact Hag.
  Qed.

  (** the byte three updates back is gone: this is what makes the rolling
      [ins_h] a 3-byte hash and not a running hash of everything seen *)
  Theorem update_hash_forget :
    forall a b c d,
      update_hash g (update_hash g (update_hash g a b) c) d
      = update_hash g (update_hash g b c) d.
  Proof.
    intros a b c d. apply uh_cong_shift. intros i Hi.
    set (A := update_hash g a b).
    unfold update_hash. rewrite Hm.
    rewrite !Z.land_spec, !Z.lxor_spec.
    rewrite mask_bit_lt by lia.
    rewrite !andb_true_r.
    rewrite !Z.shiftl_spec by lia.
    f_equal.
    destruct (Z.ltb_spec i s) as [Hsi|Hsi].
    - rewrite !Z.testbit_neg_r by lia. reflexivity.
    - unfold A. apply uh_low_bits. lia.
  Qed.

End Rolling.

(** * 3. The chain invariant and what it gives [longest_match]

    [flr ss] is the RECYCLING floor: [prev[i]] is authoritative exactly for the
    unique position congruent to [i] mod [w_size] that is above it, because the
    insert at [p + w_size] is what overwrites the slot of [p].  [lim ss] is the
    loop's own bound and sits 262 above the floor, so everything the loop can
    reach is inside the authoritative region -- with room to spare. *)
Section Chain.
  Variable g : DeflGeom.
  Variables wbits hbits : Z.
  Hypothesis Hwb : 0 <= wbits.
  Hypothesis Hhb : 0 <= hbits.
  Hypothesis Hgws : dg_w_size g = 2 ^ wbits.
  Hypothesis Hgwm : dg_w_mask g = dg_w_size g - 1.
  Hypothesis Hghs : dg_hash_size g = 2 ^ hbits.
  Hypothesis Hghm : dg_hash_mask g = dg_hash_size g - 1.
  Hypothesis Hgmd : dg_max_dist g = dg_w_size g - 262.

  Definition idx (p : Z) : Z := Z.land p (dg_w_mask g).
  Definition h3 (w : zarr) (p : Z) : Z :=
    update_hash g (update_hash g (w p) (w (p + 1))) (w (p + 2)).
  Definition flr (ss : Z) : Z := Z.max 0 (ss - dg_w_size g).
  Definition lim (ss : Z) : Z := Z.max 0 (ss - dg_max_dist g).

  Lemma ws_gt0 : 0 < dg_w_size g.
  Proof. rewrite Hgws. apply Z.pow_pos_nonneg; lia. Qed.

  Lemma flr_nonneg : forall ss, 0 <= flr ss.
  Proof. intros. unfold flr. lia. Qed.

  Lemma flr_le_lim : forall ss, flr ss <= lim ss.
  Proof. intros. unfold flr, lim. rewrite Hgmd. lia. Qed.

  Lemma flr_lo : forall ss, ss - dg_w_size g <= flr ss.
  Proof. intros. unfold flr. lia. Qed.

  Lemma flr_mono : forall ss ss', ss <= ss' -> flr ss <= flr ss'.
  Proof. intros. unfold flr. lia. Qed.

  Lemma idx_range : forall p, 0 <= idx p < dg_w_size g.
  Proof.
    intros p. unfold idx. rewrite Hgwm.
    apply (mask_range (dg_w_size g) wbits Hwb Hgws).
  Qed.

  (** recycling lemma, part 1: sliding a position by [w_size] leaves its
      [prev] slot alone *)
  Lemma idx_sub : forall p, idx (p - dg_w_size g) = idx p.
  Proof.
    intros p. unfold idx. rewrite Hgwm.
    apply (mask_sub (dg_w_size g) wbits Hwb Hgws).
  Qed.

  (** recycling lemma, part 2: inside one window of positions the slot is
      owned by exactly one of them *)
  Lemma idx_inj : forall lo p q,
    lo < p <= lo + dg_w_size g -> lo < q <= lo + dg_w_size g ->
    idx p = idx q -> p = q.
  Proof.
    intros lo p q Hp Hq E. unfold idx in E. rewrite Hgwm in E.
    exact (mask_inj (dg_w_size g) wbits Hwb Hgws lo p q Hp Hq E).
  Qed.

  Lemma hash_range : forall a b, 0 <= update_hash g a b < dg_hash_size g.
  Proof.
    intros a b. unfold update_hash. rewrite Hghm.
    apply (mask_range (dg_hash_size g) hbits Hhb Hghs).
  Qed.

  (** The inductive invariant.  [Ins] is the set of positions the encoder has
      run INSERT_STRING on; it is a parameter rather than a definition because
      which positions those are is the caller's business, and every operation
      below says how it changes. *)
  Record ChainInv (w P H : zarr) (ss la : Z) (Ins : Z -> Prop) : Prop := {
    ci_ins_lo   : forall p, Ins p -> 0 <= p;
    ci_ins_hi   : forall p, Ins p -> p <= ss;
    ci_ins_fill : forall p, Ins p -> p + 3 <= ss + la;
    ci_head_ins : forall h, 0 <= h < dg_hash_size g ->
                  H h = NIL \/ (Ins (H h) /\ H h <= ss);
    ci_head_h3  : forall h, 0 <= h < dg_hash_size g -> flr ss < H h ->
                  h3 w (H h) = h;
    ci_prev     : forall p, Ins p -> flr ss < p -> p <= ss ->
                  flr ss < P (idx p) ->
                  Ins (P (idx p)) /\ P (idx p) < p /\ h3 w (P (idx p)) = h3 w p;
    ci_prev_hi  : forall p, Ins p -> P (idx p) <= ss
  }.

  Arguments ci_ins_lo {w P H ss la Ins}.
  Arguments ci_ins_hi {w P H ss la Ins}.
  Arguments ci_ins_fill {w P H ss la Ins}.
  Arguments ci_head_ins {w P H ss la Ins}.
  Arguments ci_head_h3 {w P H ss la Ins}.
  Arguments ci_prev {w P H ss la Ins}.
  Arguments ci_prev_hi {w P H ss la Ins}.

  (** [Reach P H b h p]: [p] is on the prefix of bucket [h]'s chain that stays
      strictly above [b].  This is [longest_match]'s walk: it starts at
      [head[h]] and follows [prev[cur & wmask]] exactly while the value it
      reads is [> limit]. *)
  Inductive Reach (P H : zarr) (b h : Z) : Z -> Prop :=
  | reach0 : b < H h -> Reach P H b h (H h)
  | reachS : forall p, Reach P H b h p -> b < P (idx p) ->
             Reach P H b h (P (idx p)).

  Lemma reach_mono : forall P H b b' h p,
    b' <= b -> Reach P H b h p -> Reach P H b' h p.
  Proof.
    intros P H b b' h p Hle R. induction R.
    - apply reach0. lia.
    - apply reachS; [assumption | lia].
  Qed.

  Lemma reach_props :
    forall w P H ss la Ins, ChainInv w P H ss la Ins ->
    forall h p, 0 <= h < dg_hash_size g -> Reach P H (flr ss) h p ->
      Ins p /\ flr ss < p /\ p <= ss /\ h3 w p = h.
  Proof.
    intros w P H ss la Ins INV h p Hh R.
    induction R as [Hb | q Rq IH Hb].
    - destruct (ci_head_ins INV h Hh) as [E | [HI Hle]].
      + rewrite E in Hb. unfold NIL in Hb.
        pose proof (flr_nonneg ss). lia.
      + repeat split; try assumption. now apply (ci_head_h3 INV h Hh).
    - destruct IH as [HIq [Hlo [Hhi Hq3]]].
      destruct (ci_prev INV q HIq Hlo Hhi Hb) as [HI [Hlt Hh3]].
      repeat split; try assumption; try lia.
  Qed.

  (** [Live h p]: [p] is in the maximal prefix of chain [h] with
      [p_0 >= limit] and [p_i > limit] for [i >= 1].  The asymmetry is
      deflate_slow's, not ours: it calls [longest_match] when
      [strstart - hash_head <= MAX_DIST], i.e. [hash_head >= limit], while the
      loop's own continuation test is the strict [> limit]. *)
  Inductive Live (P H : zarr) (ss h : Z) : Z -> Prop :=
  | live0 : H h <> NIL -> lim ss <= H h -> Live P H ss h (H h)
  | liveS : forall p, Live P H ss h p -> lim ss < P (idx p) ->
            Live P H ss h (P (idx p)).

  Lemma live_reach :
    forall w P H ss la Ins, ChainInv w P H ss la Ins ->
    forall h p, 0 <= h < dg_hash_size g -> Live P H ss h p ->
      Reach P H (flr ss) h p.
  Proof.
    intros w P H ss la Ins INV h p Hh L. induction L as [Hne Hge | q L IH Hgt].
    - apply reach0.
      destruct (ci_head_ins INV h Hh) as [E | [HI Hle]]; [contradiction|].
      pose proof (ci_ins_lo INV _ HI).
      pose proof (flr_le_lim ss). unfold flr, lim in *.
      unfold NIL in Hne. rewrite Hgmd in *. lia.
    - apply reachS; [assumption|]. pose proof (flr_le_lim ss). lia.
  Qed.

  (** ** (1) the invariant [hash3_det]'s skip needs *)
  Theorem live_hash_sound :
    forall w P H ss la Ins, ChainInv w P H ss la Ins ->
    forall h p, 0 <= h < dg_hash_size g -> Live P H ss h p -> h3 w p = h.
  Proof.
    intros w P H ss la Ins INV h p Hh L.
    apply (reach_props w P H ss la Ins INV h p Hh).
    exact (live_reach w P H ss la Ins INV h p Hh L).
  Qed.

  (** ** (2) the prefix is strictly decreasing *)
  Theorem live_decreasing :
    forall w P H ss la Ins, ChainInv w P H ss la Ins ->
    forall h p, 0 <= h < dg_hash_size g -> Live P H ss h p ->
      lim ss < P (idx p) -> P (idx p) < p.
  Proof.
    intros w P H ss la Ins INV h p Hh L Hgt.
    pose proof (live_reach w P H ss la Ins INV h p Hh L) as R.
    destruct (reach_props w P H ss la Ins INV h p Hh R) as [HI [Hlo [Hhi _]]].
    pose proof (flr_le_lim ss).
    assert (Hgt' : flr ss < P (idx p)) by lia.
    destruct (ci_prev INV p HI Hlo Hhi Hgt') as [_ [Hlt _]].
    exact Hlt.
  Qed.

  (** every live position is a real, already-inserted window position, which
      is what lets the caller read its three bytes at all *)
  Theorem live_in_window :
    forall w P H ss la Ins, ChainInv w P H ss la Ins ->
    forall h p, 0 <= h < dg_hash_size g -> Live P H ss h p ->
      Ins p /\ 0 <= p /\ p <= ss /\ p + 3 <= ss + la.
  Proof.
    intros w P H ss la Ins INV h p Hh L.
    pose proof (live_reach w P H ss la Ins INV h p Hh L) as R.
    destruct (reach_props w P H ss la Ins INV h p Hh R) as [HI [Hlo [Hhi _]]].
    pose proof (ci_ins_lo INV _ HI). pose proof (ci_ins_fill INV _ HI).
    repeat split; assumption.
  Qed.
(** * 4. The invariant is preserved by the two operations that touch the chain

    [INSERT_STRING] (which is the only writer of [head]/[prev] on the hot path)
    and [fill_window]'s slide.  Everything else in [deflate_slow] moves
    [strstart] forward, which only shortens the live prefix -- [flr_advance]. *)





  (** ** what [insert_string] actually writes *)
  Lemma insert_string_fields :
    forall (l : LSt) (str : Z),
      let hh := update_hash g (ls_insh l) (ls_window l (str + MIN_MATCH - 1)) in
      fst (insert_string g str l) = ls_head l hh
      /\ ls_insh (snd (insert_string g str l)) = hh
      /\ ls_head (snd (insert_string g str l)) = zset (ls_head l) hh (u16 str)
      /\ ls_prev (snd (insert_string g str l))
         = zset (ls_prev l) (idx str) (ls_head l hh)
      /\ ls_window (snd (insert_string g str l)) = ls_window l
      /\ ls_strstart (snd (insert_string g str l)) = ls_strstart l
      /\ ls_lookahead (snd (insert_string g str l)) = ls_lookahead l.
  Proof.
    intros l str. unfold insert_string, idx. cbn. repeat split.
  Qed.

  (** ** (3) the three entry conditions at a [longest_match] call

      [deflate_slow] does [hash_head = INSERT_STRING(s, s->strstart, ...)] and
      then calls [longest_match(s, hash_head)], so at that entry the state is
      the post-insert one and [cur_match] is the value the insert returned. *)
  Theorem longest_match_entry :
    forall (l : LSt) (str : Z),
      h3 (ls_window l) str
        = update_hash g (ls_insh l) (ls_window l (str + MIN_MATCH - 1)) ->
      0 <= str < 65536 ->
      let r  := insert_string g str l in
      let l' := snd r in
      ls_insh l' = h3 (ls_window l') str
      /\ ls_head l' (ls_insh l') = str
      /\ ls_prev l' (idx str) = fst r.
  Proof.
    intros l str Hsync Hstr r l'.
    destruct (insert_string_fields l str)
      as [Hf [Hi [Hh [Hp [Hw [_ _]]]]]].
    cbn zeta in *.
    repeat split.
    - unfold l', r. rewrite Hi, Hw. now rewrite Hsync.
    - unfold l', r. rewrite Hi, Hh, zset_same. now apply u16_id.
    - unfold l', r. rewrite Hp, zset_same. now rewrite Hf.
  Qed.

  (** ** [insert_string] preserves the invariant

      [Hfresh] -- no bucket already points at [str] or beyond -- is the
      "positions are inserted in increasing order" side condition; it is what
      makes the new chain strictly decreasing at its head. *)
  Lemma insert_inv :
    forall w P Hd ss la Ins str insh,
      ChainInv w P Hd ss la Ins ->
      flr ss < str -> str <= ss -> str + 3 <= ss + la -> 0 <= str < 65536 ->
      (forall h, 0 <= h < dg_hash_size g -> Hd h < str) ->
      update_hash g insh (w (str + 2)) = h3 w str ->
      let hh := update_hash g insh (w (str + 2)) in
      ChainInv w (zset P (idx str) (Hd hh)) (zset Hd hh (u16 str)) ss la
          (fun p => Ins p \/ p = str).
  Proof.
    intros w P Hd ss la Ins str insh IV Hlo Hhi Hfill Hu Hfresh Hsync hh.
    pose proof ws_gt0 as Hws0.
    pose proof (flr_nonneg ss) as Hfl0.
    pose proof (flr_lo ss) as Hfll.
    assert (Hhh : 0 <= hh < dg_hash_size g) by apply hash_range.
    assert (Hustr : u16 str = str) by (apply u16_id; lia).
    constructor.
    - intros p [Hp | Hp]; [exact (ci_ins_lo IV p Hp) | lia].
    - intros p [Hp | Hp]; [exact (ci_ins_hi IV p Hp) | lia].
    - intros p [Hp | Hp]; [exact (ci_ins_fill IV p Hp) | lia].
    - intros h Hh. destruct (Z.eq_dec h hh) as [->|Hne].
      + rewrite zset_same, Hustr. right. split; [right; reflexivity | lia].
      + rewrite zset_other by assumption.
        destruct (ci_head_ins IV h Hh) as [E | [HI Hle]].
        * now left.
        * right. split; [now left | exact Hle].
    - intros h Hh Hgt. destruct (Z.eq_dec h hh) as [->|Hne].
      + rewrite zset_same, Hustr. symmetry. exact Hsync.
      + rewrite zset_other in Hgt by assumption.
        rewrite zset_other by assumption. exact (ci_head_h3 IV h Hh Hgt).
    - intros p Hp Hplo Hphi Hgt.
      destruct (Z.eq_dec p str) as [->|Hne].
      + rewrite zset_same in Hgt. rewrite zset_same.
        assert (HIh : Ins (Hd hh) /\ Hd hh <= ss).
        { destruct (ci_head_ins IV hh Hhh) as [E | HI]; [| exact HI].
          rewrite E in Hgt. unfold NIL in Hgt. lia. }
        destruct HIh as [HI Hle].
        repeat split.
        * now left.
        * exact (Hfresh hh Hhh).
        * rewrite (ci_head_h3 IV hh Hhh Hgt). exact Hsync.
      + assert (Hdiff : idx p <> idx str).
        { intros E. apply Hne.
          assert (Hp1 : ss - dg_w_size g < p <= ss - dg_w_size g + dg_w_size g)
            by lia.
          assert (Hp2 : ss - dg_w_size g < str <= ss - dg_w_size g + dg_w_size g)
            by lia.
          exact (idx_inj (ss - dg_w_size g) p str Hp1 Hp2 E). }
        rewrite zset_other in Hgt by assumption.
        rewrite zset_other by assumption.
        assert (HIp : Ins p) by (destruct Hp; [assumption | congruence]).
        destruct (ci_prev IV p HIp Hplo Hphi Hgt) as [A [B C]].
        repeat split; [now left | exact B | exact C].
    - intros p Hp. assert (Hss0 : 0 <= ss) by lia.
      destruct (Z.eq_dec (idx p) (idx str)) as [E|Hne].
      + rewrite E, zset_same.
        destruct (ci_head_ins IV hh Hhh) as [E2 | [HI _]].
        * rewrite E2. unfold NIL. lia.
        * exact (ci_ins_hi IV _ HI).
      + rewrite zset_other by assumption.
        assert (HIp : Ins p) by
          (destruct Hp; [assumption | subst p; contradiction]).
        exact (ci_prev_hi IV p HIp).
  Qed.

  (** Advancing [strstart] (and reading more input) only raises the floor and
      the fill bound, both of which shorten the live prefix.  This is the case
      that covers every step of [deflate_slow] that is not an insert. *)
  Lemma flr_advance :
    forall w P Hd ss la Ins ss' la',
      ChainInv w P Hd ss la Ins -> ss <= ss' -> ss + la <= ss' + la' ->
      ChainInv w P Hd ss' la' Ins.
  Proof.
    intros w P Hd ss la Ins ss' la' IV Hle Hfill.
    pose proof (flr_mono ss ss' Hle) as Hm.
    constructor.
    - intros p Hp. exact (ci_ins_lo IV p Hp).
    - intros p Hp. pose proof (ci_ins_hi IV p Hp). lia.
    - intros p Hp. pose proof (ci_ins_fill IV p Hp). lia.
    - intros h Hh. destruct (ci_head_ins IV h Hh) as [E | [HI Hle2]].
      + now left.
      + right. split; [exact HI | lia].
    - intros h Hh Hgt. apply (ci_head_h3 IV h Hh). lia.
    - intros p Hp Hplo Hphi Hgt.
      pose proof (ci_ins_hi IV p Hp).
      exact (ci_prev IV p Hp ltac:(lia) ltac:(lia) ltac:(lia)).
    - intros p Hp. pose proof (ci_prev_hi IV p Hp). lia.
  Qed.


  (** ** (4) the slide, and the recycling lemma that carries it

      [fill_window] slides when [strstart >= w_size + MAX_DIST]: it memmoves
      [window[w_size .. strstart+lookahead)] down to 0, drops [w_size] off
      [strstart], and [slide_hash]es [head] and [prev] -- subtract [w_size],
      clamp anything below it to NIL.

      The whole case turns on [idx_sub]: a position and its slid image occupy
      the SAME [prev] slot, because [prev] is indexed mod [w_size].  That is
      the recycling lemma read forwards; read backwards it says the slot for
      [p] is authoritative only until the insert at [p + w_size], which is why
      the invariant is prefix-shaped and not distance-shaped. *)
  Lemma slide_val : forall n ws' a i,
    0 <= i < n -> slide_range n ws' a i = u16 (slide_one ws' (a i)).
  Proof.
    intros n ws' a i Hi. unfold slide_range.
    destruct (Z.leb_spec 0 i) as [_|]; [|lia].
    destruct (Z.ltb_spec i n) as [_|]; [|lia]. reflexivity.
  Qed.

  Lemma slide_one_ge : forall v,
    dg_w_size g <= v -> slide_one (dg_w_size g) v = v - dg_w_size g.
  Proof.
    intros v Hv. unfold slide_one.
    destruct (Z.leb_spec (dg_w_size g) v); [reflexivity | lia].
  Qed.

  Lemma slide_one_lt : forall v,
    v < dg_w_size g -> slide_one (dg_w_size g) v = NIL.
  Proof.
    intros v Hv. unfold slide_one.
    destruct (Z.leb_spec (dg_w_size g) v); [lia | reflexivity].
  Qed.

  Lemma winmove_lo : forall w cnt i,
    0 <= i < cnt -> win_move 0 (dg_w_size g) cnt w i = w (i + dg_w_size g).
  Proof.
    intros w cnt i Hi. unfold win_move.
    destruct (Z.leb_spec 0 i) as [_|]; [|lia].
    destruct (Z.ltb_spec i (0 + cnt)) as [_|]; [|lia].
    cbn. now replace (i - 0 + dg_w_size g) with (i + dg_w_size g) by ring.
  Qed.

  Lemma h3_slide : forall w cnt p, 0 <= p -> p + 2 < cnt ->
    h3 (win_move 0 (dg_w_size g) cnt w) p = h3 w (p + dg_w_size g).
  Proof.
    intros w cnt p H0 H2. unfold h3. rewrite !winmove_lo by lia.
    replace (p + 1 + dg_w_size g) with (p + dg_w_size g + 1) by ring.
    replace (p + 2 + dg_w_size g) with (p + dg_w_size g + 2) by ring.
    reflexivity.
  Qed.

  Lemma slide_inv :
    forall w P Hd ss la Ins,
      ChainInv w P Hd ss la Ins ->
      dg_w_size g <= ss -> ss + la <= 2 * dg_w_size g -> 0 <= la ->
      2 * dg_w_size g <= 65536 ->
      ChainInv (win_move 0 (dg_w_size g) (ss + la - dg_w_size g) w)
               (slide_range (dg_w_size g) (dg_w_size g) P)
               (slide_range (dg_hash_size g) (dg_w_size g) Hd)
               (ss - dg_w_size g) la
               (fun p => 0 <= p /\ Ins (p + dg_w_size g)).
  Proof.
    intros w P Hd ss la Ins IV Hss Hsl Hla Hu.
    pose proof ws_gt0 as Hws0.
    pose proof (flr_nonneg (ss - dg_w_size g)) as Hf0.
    pose proof (flr_lo (ss - dg_w_size g)) as Hfl.
    assert (Hfss : flr ss = ss - dg_w_size g) by (unfold flr; lia).
    assert (Hu0 : u16 NIL = NIL) by (unfold NIL; apply u16_id; lia).
    constructor.
    - intros p [Hp _]. exact Hp.
    - intros p [_ Hp]. pose proof (ci_ins_hi IV _ Hp). lia.
    - intros p [_ Hp]. pose proof (ci_ins_fill IV _ Hp). lia.
    - intros h Hh. rewrite slide_val by lia.
      destruct (Z_lt_le_dec (Hd h) (dg_w_size g)) as [Hlt|Hge].
      + rewrite slide_one_lt by lia. rewrite Hu0. now left.
      + assert (HI : Ins (Hd h)).
        { destruct (ci_head_ins IV h Hh) as [E | [HI _]]; [| exact HI].
          rewrite E in Hge. unfold NIL in Hge. lia. }
        pose proof (ci_ins_hi IV _ HI) as Hle.
        rewrite slide_one_ge by lia. rewrite u16_id by lia.
        right. split; [split; [lia | now replace (Hd h - dg_w_size g
                                                  + dg_w_size g)
                                        with (Hd h) by ring] | lia].
    - intros h Hh Hgt. rewrite slide_val in Hgt by lia. rewrite slide_val by lia.
      destruct (Z_lt_le_dec (Hd h) (dg_w_size g)) as [Hlt|Hge].
      + rewrite slide_one_lt in Hgt by lia. rewrite Hu0 in Hgt.
        unfold NIL in Hgt. lia.
      + assert (HI : Ins (Hd h)).
        { destruct (ci_head_ins IV h Hh) as [E | [HI _]]; [| exact HI].
          rewrite E in Hge. unfold NIL in Hge. lia. }
        pose proof (ci_ins_hi IV _ HI) as Hle.
        pose proof (ci_ins_fill IV _ HI) as Hfill.
        rewrite slide_one_ge in Hgt by lia. rewrite u16_id in Hgt by lia.
        rewrite slide_one_ge by lia. rewrite u16_id by lia.
        rewrite h3_slide by lia.
        replace (Hd h - dg_w_size g + dg_w_size g) with (Hd h) by ring.
        apply (ci_head_h3 IV h Hh). lia.
    - intros p [Hp0 Hp] Hplo Hphi Hgt.
      assert (Hidx : idx p = idx (p + dg_w_size g)).
      { rewrite <- (idx_sub (p + dg_w_size g)).
        f_equal. ring. }
      rewrite Hidx in Hgt |- *.
      rewrite slide_val in Hgt by apply idx_range.
      rewrite slide_val by apply idx_range.
      pose proof (ci_prev_hi IV _ Hp) as Hqle.
      pose proof (ci_ins_hi IV _ Hp) as Hple.
      pose proof (ci_ins_fill IV _ Hp) as Hpfill.
      destruct (Z_lt_le_dec (P (idx (p + dg_w_size g))) (dg_w_size g))
        as [Hlt|Hge].
      + rewrite slide_one_lt in Hgt by lia. rewrite Hu0 in Hgt.
        unfold NIL in Hgt. lia.
      + rewrite slide_one_ge in Hgt by lia. rewrite u16_id in Hgt by lia.
        rewrite slide_one_ge by lia. rewrite u16_id by lia.
        destruct (ci_prev IV (p + dg_w_size g) Hp ltac:(lia) ltac:(lia)
                          ltac:(lia)) as [A [B C]].
        pose proof (ci_ins_fill IV _ A) as Hqfill.
        pose proof (ci_ins_lo IV _ A) as Hqlo.
        repeat split.
        * lia.
        * now replace (P (idx (p + dg_w_size g)) - dg_w_size g + dg_w_size g)
            with (P (idx (p + dg_w_size g))) by ring.
        * lia.
        * rewrite !h3_slide by lia.
          replace (P (idx (p + dg_w_size g)) - dg_w_size g + dg_w_size g)
            with (P (idx (p + dg_w_size g))) by ring.
          exact C.
    - intros p [Hp0 Hp].
      assert (Hidx : idx p = idx (p + dg_w_size g)).
      { rewrite <- (idx_sub (p + dg_w_size g)). f_equal. ring. }
      rewrite Hidx. rewrite slide_val by apply idx_range.
      pose proof (ci_prev_hi IV _ Hp) as Hqle.
      destruct (Z_lt_le_dec (P (idx (p + dg_w_size g))) (dg_w_size g))
        as [Hlt|Hge].
      + rewrite slide_one_lt by lia. rewrite Hu0. unfold NIL. lia.
      + rewrite slide_one_ge by lia. rewrite u16_id by lia. lia.
  Qed.


  (** * 5. What the invariant buys [cRes]

      [longest_match] byte-compares offsets 0 and 1 and then jumps to offset 2
      of the previous best length, never comparing offset 2 itself.  Given the
      chain invariant, that is sound: the candidate and [strstart] are in the
      same bucket, so their 3-byte hashes agree, and [hash3_det] makes the hash
      injective in the third byte once the first two are fixed.  This is the
      step Deflate.v's own comment calls "the load-bearing step of cRes". *)
  Lemma skip_scan2_ok :
    forall w p q,
      8 <= hbits ->
      0 <= w (p + 2) < 256 -> 0 <= w (q + 2) < 256 ->
      h3 w p = h3 w q ->
      w p = w q -> w (p + 1) = w (q + 1) ->
      w (p + 2) = w (q + 2).
  Proof.
    intros w p q Hh8 Hbp Hbq Hh Hb0 Hb1.
    assert (H256 : 256 <= 2 ^ hbits).
    { replace 256 with (2 ^ 8) by reflexivity. apply Z.pow_le_mono_r; lia. }
    apply (hash3_det g (update_hash g (w p) (w (p + 1)))
                     (w (p + 2)) (w (q + 2)) hbits); try lia.
    unfold h3 in Hh. rewrite Hh. now rewrite Hb0, Hb1.
  Qed.

  (** the form the caller uses: a live candidate agrees with [strstart] at
      offset 2 as soon as it agrees at offsets 0 and 1 *)
  Theorem live_match_byte2 :
    forall w P Hd ss la Ins h p,
      ChainInv w P Hd ss la Ins ->
      0 <= h < dg_hash_size g -> Live P Hd ss h p -> h3 w ss = h ->
      8 <= hbits ->
      0 <= w (p + 2) < 256 -> 0 <= w (ss + 2) < 256 ->
      w p = w ss -> w (p + 1) = w (ss + 1) ->
      w (p + 2) = w (ss + 2).
  Proof.
    intros w P Hd ss la Ins h p IV Hh L Hss Hh8 Hbp Hbs Hb0 Hb1.
    apply (skip_scan2_ok w p ss Hh8 Hbp Hbs); try assumption.
    rewrite (live_hash_sound w P Hd ss la Ins IV h p Hh L). now rewrite Hss.
  Qed.

  (** the distance bound the emitted LZ77 token needs: every live candidate is
      within MAX_DIST, which is what makes [resolve] read inside the history
      rather than off the front of it *)
  Theorem live_dist_bound :
    forall w P Hd ss la Ins h p,
      ChainInv w P Hd ss la Ins -> 0 <= h < dg_hash_size g ->
      Live P Hd ss h p -> 0 <= ss - p <= dg_max_dist g.
  Proof.
    intros w P Hd ss la Ins h p IV Hh L.
    destruct (live_in_window w P Hd ss la Ins IV h p Hh L) as [_ [Hlo [Hhi _]]].
    assert (Hge : lim ss <= p).
    { destruct L as [Hne Hge | q L Hgt]; [exact Hge | lia]. }
    unfold lim in Hge. lia.
  Qed.


  (** ** the rest of [fill_window]: writing input ABOVE [strstart+lookahead]

      [win_blit] (read_buf) and [win_zero] (the WIN_INIT fill) only touch
      indices at or above [strstart + lookahead], and [ci_ins_fill] says every
      inserted position hashes bytes strictly below that.  Stated through
      [arr_eq_on] so it composes with the rest of the tree. *)
  Lemma h3_ext :
    forall w w' ss la p,
      arr_eq_on w w' 0 (ss + la) -> 0 <= p -> p + 3 <= ss + la ->
      h3 w p = h3 w' p.
  Proof.
    intros w w' ss la p Hext H0 H3. unfold h3.
    rewrite (arr_eq_on_at w w' 0 (ss + la) p Hext) by lia.
    rewrite (arr_eq_on_at w w' 0 (ss + la) (p + 1) Hext) by lia.
    rewrite (arr_eq_on_at w w' 0 (ss + la) (p + 2) Hext) by lia.
    reflexivity.
  Qed.

  Lemma window_ext_inv :
    forall w w' P Hd ss la Ins,
      ChainInv w P Hd ss la Ins -> arr_eq_on w w' 0 (ss + la) ->
      ChainInv w' P Hd ss la Ins.
  Proof.
    intros w w' P Hd ss la Ins IV Hext.
    pose proof (flr_nonneg ss) as Hf0.
    assert (Hh3 : forall p, Ins p -> h3 w p = h3 w' p).
    { intros p Hp. apply (h3_ext w w' ss la p Hext).
      - exact (ci_ins_lo IV p Hp).
      - exact (ci_ins_fill IV p Hp). }
    constructor.
    - intros p Hp. exact (ci_ins_lo IV p Hp).
    - intros p Hp. exact (ci_ins_hi IV p Hp).
    - intros p Hp. exact (ci_ins_fill IV p Hp).
    - intros h Hh. exact (ci_head_ins IV h Hh).
    - intros h Hh Hgt.
      assert (HI : Ins (Hd h)).
      { destruct (ci_head_ins IV h Hh) as [E | [HI _]]; [| exact HI].
        rewrite E in Hgt. unfold NIL in Hgt. lia. }
      rewrite <- (Hh3 _ HI). exact (ci_head_h3 IV h Hh Hgt).
    - intros p Hp Hplo Hphi Hgt.
      destruct (ci_prev IV p Hp Hplo Hphi Hgt) as [A [B C]].
      repeat split; [exact A | exact B |].
      rewrite <- (Hh3 _ A), <- (Hh3 _ Hp). exact C.
    - intros p Hp. exact (ci_prev_hi IV p Hp).
  Qed.

  (** ** one [deflate_slow] trip: advance [strstart], then INSERT_STRING there

      This is the composition the loop actually performs, and it is worth
      having as one lemma because the [Hfresh] side condition of [insert_inv]
      -- no bucket already points at the position being inserted -- is
      discharged from the invariant at the PRE-advance [strstart], not the
      post-advance one.  Getting that order wrong is the obvious way to get
      stuck here. *)
  Lemma advance_insert_inv :
    forall w P Hd ss la Ins ss' la' insh,
      ChainInv w P Hd ss la Ins ->
      ss < ss' -> ss + la <= ss' + la' ->
      3 <= la' -> 0 <= ss' < 65536 -> flr ss' < ss' ->
      update_hash g insh (w (ss' + 2)) = h3 w ss' ->
      let hh := update_hash g insh (w (ss' + 2)) in
      ChainInv w (zset P (idx ss') (Hd hh)) (zset Hd hh (u16 ss')) ss' la'
               (fun p => Ins p \/ p = ss').
  Proof.
    intros w P Hd ss la Ins ss' la' insh IV Hlt Hfill Hla Hss' Hflr Hsync hh.
    assert (Hfresh : forall h, 0 <= h < dg_hash_size g -> Hd h < ss').
    { intros h Hh. destruct (ci_head_ins IV h Hh) as [E | [_ Hle]].
      - rewrite E. unfold NIL.
        pose proof (flr_nonneg ss'). lia.
      - lia. }
    pose proof (flr_advance w P Hd ss la Ins ss' la' IV ltac:(lia) Hfill)
      as IV'.
    exact (insert_inv w P Hd ss' la' Ins ss' insh IV' Hflr ltac:(lia)
             ltac:(lia) ltac:(lia) Hfresh Hsync).
  Qed.


  (** [slide_inv] restated on the model function [slide_hash] itself, so a
      caller inside [fw_step] can use it without re-deriving the field
      projections.  [fw_step]'s slide branch memmoves the window (that is the
      [ls_window] hypothesis), drops [w_size] off [strstart], and then applies
      exactly this [slide_hash]. *)
  Lemma slide_hash_inv :
    forall w P Hd ss la Ins (l : LSt),
      ChainInv w P Hd ss la Ins ->
      dg_w_size g <= ss -> ss + la <= 2 * dg_w_size g -> 0 <= la ->
      2 * dg_w_size g <= 65536 ->
      ls_window l = win_move 0 (dg_w_size g) (ss + la - dg_w_size g) w ->
      ls_prev l = P -> ls_head l = Hd ->
      ls_strstart l = ss - dg_w_size g -> ls_lookahead l = la ->
      ChainInv (ls_window (slide_hash g l)) (ls_prev (slide_hash g l))
               (ls_head (slide_hash g l)) (ls_strstart (slide_hash g l))
               (ls_lookahead (slide_hash g l))
               (fun p => 0 <= p /\ Ins (p + dg_w_size g)).
  Proof.
    intros w P Hd ss la Ins l IV Hss Hsl Hla Hu Hw Hp Hh Hs Hlk.
    unfold slide_hash. cbn [ls_window ls_prev ls_head ls_strstart ls_lookahead
                            setL_prev setL_head].
    rewrite Hw, Hp, Hh, Hs, Hlk.
    exact (slide_inv w P Hd ss la Ins IV Hss Hsl Hla Hu).
  Qed.


  (** A trap worth closing here rather than downstream: [Live] starts at
      [head[h]], and at a [longest_match] entry that is [strstart] itself,
      because [deflate_slow] inserts BEFORE it calls.  The C starts its walk one
      link further on, at [prev[strstart & wmask]] = the returned [hash_head],
      so a token-level statement must quantify over the SUCCESSORS, where the
      distance is genuinely >= 1. *)
  Theorem live_step_dist :
    forall w P Hd ss la Ins h p,
      ChainInv w P Hd ss la Ins -> 0 <= h < dg_hash_size g ->
      Live P Hd ss h p -> lim ss < P (idx p) ->
      1 <= ss - P (idx p) <= dg_max_dist g.
  Proof.
    intros w P Hd ss la Ins h p IV Hh L Hgt.
    pose proof (live_decreasing w P Hd ss la Ins IV h p Hh L Hgt) as Hdec.
    destruct (live_in_window w P Hd ss la Ins IV h p Hh L) as [_ [_ [Hple _]]].
    pose proof (live_dist_bound w P Hd ss la Ins h (P (idx p)) IV Hh
                  (liveS P Hd ss h p L Hgt)) as [_ Hub].
    lia.
  Qed.

End Chain.

(** * 6. Match validity: what [longest_match] actually establishes

    [lm_ok] byte-checks offsets 0 and 1 (and the two [best_len] sentinels);
    [lm_cpl] runs the compare loop from offset 3; offset 2 is never compared.
    Together with [live_match_byte2] -- which supplies offset 2 from the chain
    invariant and [hash3_det] -- that is EVERY offset below the reported
    length, which is exactly the fact [cRes] needs about an emitted [TMatch]:
    the bytes it tells the decoder to copy are the bytes that were there. *)
Lemma lm_cpl_agree :
  forall fuel w a b j i,
    j <= i -> i < lm_cpl fuel w a b j -> w (a + i) = w (b + i).
Proof.
  induction fuel as [|f IH]; intros w a b j i Hji Hlt; cbn [lm_cpl] in Hlt.
  - lia.
  - destruct (Z.leb_spec MAX_MATCH j) as [Hmm|Hmm]; [lia|].
    destruct (Z.eqb_spec (w (a + j)) (w (b + j))) as [Heq|Hne]; [|lia].
    destruct (Z.eq_dec i j) as [->|Hij].
    + exact Heq.
    + apply (IH w a b (j + 1) i); lia.
Qed.

Theorem lm_match_valid :
  forall c st,
    lm_ok c st = true ->
    x_win c (m_cur st + 2) = x_win c (x_scan c + 2) ->
    forall i, 0 <= i < lm_len c st ->
      x_win c (x_scan c + i) = x_win c (m_cur st + i).
Proof.
  intros c st Hok Hb2 i Hi.
  assert (Hlen : lm_len c st
                 = lm_cpl (Z.to_nat MAX_MATCH) (x_win c) (x_scan c) (m_cur st) 3).
  { unfold lm_len. now rewrite Hok. }
  unfold lm_ok in Hok. rewrite !andb_true_iff in Hok.
  destruct Hok as [[[_ _] H0] H1].
  apply Z.eqb_eq in H0. apply Z.eqb_eq in H1.
  destruct (Z.eq_dec i 0) as [->|Hi0].
  { rewrite !Z.add_0_r. now symmetry. }
  destruct (Z.eq_dec i 1) as [->|Hi1].
  { now symmetry. }
  destruct (Z.eq_dec i 2) as [->|Hi2].
  { now symmetry. }
  rewrite Hlen in Hi.
  apply (lm_cpl_agree (Z.to_nat MAX_MATCH) (x_win c) (x_scan c) (m_cur st) 3 i);
    lia.
Qed.

(** The end-to-end encoder-side statement this node was staffed to reach:
    a candidate on the live chain that [longest_match] accepts agrees with
    the history at EVERY offset it reports. *)
Theorem live_match_bytes_agree :
  forall g wbits hbits w P Hd ss la Ins h c st,
    0 <= wbits -> 0 <= hbits -> 8 <= hbits ->
    dg_w_size g = 2 ^ wbits -> dg_w_mask g = dg_w_size g - 1 ->
    dg_hash_size g = 2 ^ hbits -> dg_hash_mask g = dg_hash_size g - 1 ->
    dg_max_dist g = dg_w_size g - 262 ->
    ChainInv g w P Hd ss la Ins ->
    0 <= h < dg_hash_size g ->
    Live g P Hd ss h (m_cur st) ->
    h3 g w ss = h ->
    x_win c = w -> x_scan c = ss ->
    0 <= w (m_cur st + 2) < 256 -> 0 <= w (ss + 2) < 256 ->
    lm_ok c st = true ->
    forall i, 0 <= i < lm_len c st -> w (ss + i) = w (m_cur st + i).
Proof.
  intros g wbits hbits w P Hd ss la Ins h c st Hwb Hhb Hh8 Hgws Hgwm Hghs Hghm
         Hgmd IV Hh L Hss Hcw Hcs Hbp Hbs Hok i Hi.
  assert (Hb0 : x_win c (m_cur st) = x_win c (x_scan c)).
  { unfold lm_ok in Hok. rewrite !andb_true_iff in Hok.
    destruct Hok as [[[_ _] H0] _]. now apply Z.eqb_eq in H0. }
  assert (Hb1 : x_win c (m_cur st + 1) = x_win c (x_scan c + 1)).
  { unfold lm_ok in Hok. rewrite !andb_true_iff in Hok.
    destruct Hok as [[[_ _] _] H1]. now apply Z.eqb_eq in H1. }
  rewrite Hcw, Hcs in Hb0, Hb1.
  assert (Hb2 : w (m_cur st + 2) = w (ss + 2)).
  { eapply live_match_byte2; try eassumption; try lia. }
  pose proof (lm_match_valid c st Hok
                ltac:(rewrite Hcw, Hcs; exact Hb2) i Hi) as Hagree.
  rewrite Hcw, Hcs in Hagree. exact Hagree.
Qed.
