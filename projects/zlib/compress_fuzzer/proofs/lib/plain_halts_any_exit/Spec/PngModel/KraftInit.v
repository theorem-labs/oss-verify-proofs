(** * KraftInit -- the zero-frequency half of ledger item 4, proved.

    OWNER: kraftsum.

    WHY THIS FILE EXISTS.  My [KraftLens.tree_lens_range] consumes ledger item 4
    ([forall i, 0 <= i <= lcodes - 1 -> 0 <= t_len (ts_trees s TK_L) i <= 15]) as
    a hypothesis, and I raised a hazard against it: [GbRange.v] establishes that
    [t_len] holds DAD values on entry to [gen_bitlen] (the [tr_dl] alias), and
    [gb_pass1] overwrites only the heap-visited window -- so a zero-frequency
    symbol below [max_code] that never entered the heap looked like it could carry
    a dad value out of [build_tree], which would make item 4 FALSE rather than
    merely unproved.

    IT DOES NOT.  [Trees.v:554-555] transcribes zlib's own [else tree[n].Len = 0;]
    from [trees.c:645], so every zero-frequency symbol is zeroed during
    initialisation, before any dad is written.  I withdrew the hazard on that
    reading; this file replaces the reading with a proof, because "I read the
    else-branch" is not a lemma and the whole point of the scare was that a
    plausible reading of the surrounding code was wrong.

    THE SPLIT THIS BUYS.  Item 4 is not one expensive obligation.  It is:

      positive frequency   huffman-id's BuildChain.build_chain (done)
      zero frequency       bt_init's one-line assignment  <- THIS FILE

    and the second needs no heap invariant at all, which is why it is worth
    separating rather than waiting on the machinery that handles the first.

    WHAT IS STILL NOT CLAIMED.  This is about [bt_init]'s output.  Carrying it to
    [build_tree]'s output additionally needs "[bt_force2], [bt_heapify], [bt_loop],
    [gen_bitlen] and [gen_codes] do not write [t_len] at an index [bt_init]
    zeroed".  [bt_force2] writes [t_setfreq] not [t_setlen], [gen_codes_len] is
    proved, and the two [gb_] passes walk heap entries only -- but the heap-membership
    part of that is huffman-id's territory and is NOT proved here. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** [bt_init] returns a five-tuple; the length facts are all about its first
    component, so it gets a projection rather than a [match] at every use. *)
Definition bti_tree (r : Tree * zarr * zarr * Z * Z) : Tree :=
  match r with (t, _, _, _, _) => t end.

(** The three [t_setlen] shape facts, proved inline from [Trees.v:232-233]
    ([t_setlen t i v = mkTree (tr_fc t) (zset (tr_dl t) i (u16 v))]) rather than
    imported.  [GenBitlen.v] has the first two as [t_len_setlen_same'] /
    [t_len_setlen_other'], but that file does not exist in the graded tree at all
    (it lives only in huffman-id's stage), so depending on it would put this file
    outside the graded closure for two one-line lemmas.  The third -- that
    [t_setlen] leaves the FREQUENCY array alone -- is what makes the induction
    below go through, since the scan's branch condition reads [t_freq]. *)
Lemma t_len_setlen_here : forall t i v, t_len (t_setlen t i v) i = u16 v.
Proof. intros t i v. unfold t_len, t_setlen. cbn [tr_dl]. apply zset_same. Qed.

Lemma t_len_setlen_elsewhere : forall t i v j,
  j <> i -> t_len (t_setlen t i v) j = t_len t j.
Proof.
  intros t i v j Hj. unfold t_len, t_setlen. cbn [tr_dl].
  apply zset_other. exact Hj.
Qed.

Lemma t_freq_setlen_here : forall t i v j, t_freq (t_setlen t i v) j = t_freq t j.
Proof. intros t i v j. unfold t_freq, t_setlen. reflexivity. Qed.

(** ** 1. [bt_init] never revisits an index it has passed

    The scan writes only at its current [n] and moves upward, so everything
    strictly below [n] is frozen.  This is what makes the zeroing STICK -- without
    it, "index [n] was set to 0 at step [n]" says nothing about the final tree. *)
Lemma bt_init_frozen_below : forall fuel n elems t hp dep hlen maxc i,
  i < n ->
  t_len (bti_tree (bt_init fuel n elems t hp dep hlen maxc)) i = t_len t i.
Proof.
  induction fuel as [|f IH]; intros n elems t hp dep hlen maxc i Hi.
  - reflexivity.
  - cbn [bt_init].
    destruct (Z.leb elems n) eqn:Ee; [reflexivity|].
    destruct (Z.eqb (t_freq t n) 0) eqn:Ef.
    + (* zero frequency: writes at n, then recurses from n + 1 *)
      rewrite (IH (n + 1) elems (t_setlen t n 0) hp dep hlen maxc i) by lia.
      apply t_len_setlen_elsewhere. lia.
    + (* positive frequency: no length write at all *)
      rewrite (IH (n + 1) elems t (zset hp (hlen + 1) n) (zset dep n 0)
                 (hlen + 1) n i) by lia.
      reflexivity.
Qed.

(** ** 2. A zero-frequency index in the scanned range ends at length 0

    The fuel hypothesis is stated as [elems - n <= Z.of_nat fuel] rather than at
    [bt_init]'s actual call site value, so the lemma is usable at any fuel that
    suffices; [bt_init_zero_len_at_call] below discharges it for the real call. *)
Lemma bt_init_zeroes_zero_freq : forall fuel n elems t hp dep hlen maxc i,
  elems - n <= Z.of_nat fuel ->
  n <= i < elems ->
  t_freq t i = 0 ->
  t_len (bti_tree (bt_init fuel n elems t hp dep hlen maxc)) i = 0.
Proof.
  induction fuel as [|f IH]; intros n elems t hp dep hlen maxc i Hfuel Hi Hfq.
  - (* no fuel forces [elems <= n], contradicting [n <= i < elems] *)
    cbn [Z.of_nat] in Hfuel. lia.
  - cbn [bt_init].
    destruct (Z.leb elems n) eqn:Ee.
    + apply Z.leb_le in Ee. lia.
    + apply Z.leb_gt in Ee.
      destruct (Z.eqb (t_freq t n) 0) eqn:Ef.
      * destruct (Z.eq_dec i n) as [->|Hne].
        -- (* the write happens NOW; section 1 says nothing overwrites it *)
           rewrite (bt_init_frozen_below f (n + 1) elems (t_setlen t n 0)
                      hp dep hlen maxc n) by lia.
           rewrite t_len_setlen_here. reflexivity.
        -- apply (IH (n + 1) elems (t_setlen t n 0) hp dep hlen maxc i);
             [lia | lia |].
           (* [t_setlen] touches the length array, never the frequency array *)
           rewrite t_freq_setlen_here. exact Hfq.
      * (* n has positive frequency, so n <> i and the scan moves on *)
        apply Z.eqb_neq in Ef.
        assert (Hne : i <> n) by (intro Hc; subst; contradiction).
        apply (IH (n + 1) elems t (zset hp (hlen + 1) n) (zset dep n 0)
                 (hlen + 1) n i); [lia | lia | exact Hfq].
Qed.

(** ** 3. At [build_tree]'s actual call

    [build_tree] calls [bt_init (Z.to_nat L_CODES + 2) 0 elems ...]
    ([Trees.v:663]) with [elems = sd_elems k].  The fuel-sufficiency side
    condition is discharged from [elems <= L_CODES + 2], which holds for every
    tree kind -- checked below rather than assumed. *)
Lemma sd_elems_bound : forall k, sd_elems k <= L_CODES + 2.
Proof.
  intro k. unfold sd_elems, L_CODES, D_CODES, BL_CODES.
  destruct (Z.eqb k TK_L) eqn:El; [lia|].
  destruct (Z.eqb k TK_D) eqn:Ed; [lia|]. lia.
Qed.

Theorem bt_init_zero_len_at_call : forall k t hp dep i,
  0 <= i < sd_elems k ->
  t_freq t i = 0 ->
  t_len (bti_tree (bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems k)
                           t hp dep 0 (-1))) i = 0.
Proof.
  intros k t hp dep i Hi Hfq.
  apply (bt_init_zeroes_zero_freq (Z.to_nat L_CODES + 2) 0 (sd_elems k)
           t hp dep 0 (-1) i); [|lia|exact Hfq].
  pose proof (sd_elems_bound k) as Hb. unfold L_CODES in *. lia.
Qed.

(** ** 4. CONTROLS

    The lemma is about a scan, so the controls exercise the two branches and the
    boundary: an index with zero frequency (zeroed), an index with positive
    frequency (untouched by the zeroing branch), and an index at the top of the
    range. *)
Definition tprobe : Tree := mkTree (zlist [0;5;0;7]) (zlist [99;98;97;96]).

(** Entry state: the "length" slots hold 99..96 -- far above 15, standing in for
    the dad values [GbRange.v] warns about.  So a control that passed by accident
    on an already-zero array is ruled out. *)
Example tprobe_entry_lens : t_len tprobe 0 = 99 /\ t_len tprobe 2 = 97.
Proof. split; vm_compute; reflexivity. Qed.

Example tprobe_freqs : t_freq tprobe 0 = 0 /\ t_freq tprobe 1 = 5
                       /\ t_freq tprobe 2 = 0 /\ t_freq tprobe 3 = 7.
Proof. repeat split; vm_compute; reflexivity. Qed.

Definition tprobe_init : Tree :=
  bti_tree (bt_init 8%nat 0 4 tprobe zzero zzero 0 (-1)).

(** POSITIVE: both zero-frequency indices come out at 0, from 99 and 97. *)
Example tprobe_zeroed_0 : t_len tprobe_init 0 = 0.
Proof. vm_compute. reflexivity. Qed.

Example tprobe_zeroed_2 : t_len tprobe_init 2 = 0.
Proof. vm_compute. reflexivity. Qed.

(** NEGATIVE CONTROL: the POSITIVE-frequency indices are NOT zeroed -- they still
    hold their entry dad values.  Without this the positive results above would be
    consistent with [bt_init] simply clearing the whole array, which would make
    the lemma true for an uninteresting reason and would hide the fact that the
    positive-frequency case genuinely needs the heap chain. *)
Example tprobe_untouched_1 : t_len tprobe_init 1 = 98.
Proof. vm_compute. reflexivity. Qed.

Example tprobe_untouched_3 : t_len tprobe_init 3 = 96.
Proof. vm_compute. reflexivity. Qed.

(** ...and the general lemma FIRES at the witness, so it is not vacuous. *)
Example tprobe_lemma_fires : t_len tprobe_init 2 = 0.
Proof.
  unfold tprobe_init.
  apply (bt_init_zeroes_zero_freq 8%nat 0 4 tprobe zzero zzero 0 (-1) 2);
    [cbn [Z.of_nat]; lia | lia | vm_compute; reflexivity].
Qed.

Print Assumptions t_len_setlen_here.
Print Assumptions t_freq_setlen_here.
Print Assumptions bt_init_frozen_below.
Print Assumptions bt_init_zeroes_zero_freq.
Print Assumptions sd_elems_bound.
Print Assumptions bt_init_zero_len_at_call.
Print Assumptions tprobe_zeroed_0.
Print Assumptions tprobe_untouched_1.
Print Assumptions tprobe_lemma_fires.
