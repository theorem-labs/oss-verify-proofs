(** * KeyClass — the ownership S-instance (pieces 1-2 in this bed).

    pres lane (q4).  Target: g1's [zr_fill_class] (ItGClassHead.v
    , RATIFIED 2026-08-21; my ratification message has the
    check list).  Piece 1 locked the spellings; this iteration proves
    piece 2: the seam/kth/bridge helpers, [ent_of_tie], [own_seed] and
    THE TIE [trip_owner].



    THE ONE DELIBERATE DELTA from the head's proposed theorem shape
    (its comment invites premise adjustment; the conclusion Prop is
    verbatim): the theorem concludes at a DEFINITE witness [ent_of]
    instead of a universally quantified [ent] under the fixpoint tie
    [ent sym = it_entry c sym (c_bits (ent sym))] — that tie holds for
    it_entry at EVERY bits argument ([bits_it_entry]), so it does not
    pin [ent] and the universal form is unprovable (adversarial [ent]
    with wrong bits defeats [T i = ent sym]).  Consumers take [ent]
    existentially (B3 heads, zr_codes_own), so they witness [ent_of];
    [ent_of_tie] exports the fixpoint spelling those consumers'
    [zr_*_ents_of_tie] premises want.

    Engine consumed, not mirrored (one-engine rule): CovInv/CovCtxOk,
    Pos, cov_step_cont, cov_pre (ItGTblCover); it_mass_ext/zero_on
    (ItGTblGeom); the MSB/LSB seam halves (Huff.code_bits_rev_write_bits
    + HuffGenCodes.write_bits_zrev); rank_prefix/zcount_code_offset
    (KeyRank) and nc_it_mass/it_mass_split/cntL (KeyTie) from this bed.
    The loop recursion will follow g1's nom_loop precedent
    (ItGMarkers:696) because [BreakShape] is not loop-invariant, so
    cov_loop_side's S-only conclusion cannot carry it.

    Ledger design (why these clauses):
    - [OwnBelow] guards cells by FULLY consumed position windows
      (CovBelow's guard, richer payload).  A fully consumed root
      window implies all its children are filled, so the pointer arm
      carries FULL [zr_ptr_children] — verbatim the head's arm — plus
      one region bound [val + 2^op <= s_next] that keeps later trips
      (which write only at [s_next ..)) off the closed children.
    - [OwnOpen] is the single in-progress phase-2 window at [s_low]:
      pointer geometry already in the table, children owned only
      below the consumed position.
    - region accounting [s_next + 2^s_curr = s_used /\ s_used < 65536]
      makes the u16 [c_val] readback of pointer records exact
      (mkCodeT truncates; ENOUGH_LENS/ENOUGH_DISTS keep used small,
      and the [x_root = x_max] worlds never create sub-tables). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff HuffGenCodes Inftrees ItGTblRev ItGTblGeom ItGTblSortWin
  InftreesBridge ItGTblCover ItGSubCover.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproQ6K.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import KeyTie KeyRank KeyBits.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** Verbatim duplicates from ItGClassHead.v ()

    Until-landing-home rule, same as ItGWidth.v's copy of
    [zr_ptr_children]: one home is chosen at the landing train. *)

Definition zr_ptr_children (T : ztbl) (root : Z) (lens : list nat)
           (ent : nat -> Code) (i op val : Z) : Prop :=
  forall j, 0 <= j < 2 ^ op ->
    exists sym cw, code_for lens 15%nat sym = Some cw
      /\ root < Z.of_nat (length cw) <= root + op
      /\ T (val + j) = ent sym
      /\ c_bits (ent sym) = Z.of_nat (length cw) - root
      /\ firstn (length cw)
           (write_bits (Z.to_nat root) i ++ write_bits (Z.to_nat op) j)
         = cw.

Definition zr_fill_class (T : ztbl) (root : Z) (lens : list nat)
           (ent : nat -> Code) : Prop :=
  forall i, 0 <= i < 2 ^ root ->
    (exists sym cw, code_for lens 15%nat sym = Some cw
       /\ Z.of_nat (length cw) <= root
       /\ T i = ent sym
       /\ c_bits (ent sym) = Z.of_nat (length cw)
       /\ firstn (length cw) (write_bits (Z.to_nat root) i) = cw)
    \/ (c_bits (T i) = root
        /\ 1 <= c_op (T i) <= 15 - root
        /\ 2 ^ root <= c_val (T i)
        /\ zr_ptr_children T root lens ent i (c_op (T i)) (c_val (T i)))
    \/ (T i = mkCodeT 64 1 0 /\ root = 1 /\ i = 1).

(* ------------------------------------------------------------------ *)
(** ** Helpers *)

(** The tree has two [zrev]s (ItGTblRev's odd/div2 form is what CovInv
    speaks; HuffGenCodes' mod/div form is what the seam lemma speaks);
    they agree. *)
Lemma zrev_agree : forall n h,
  zrev n h = HuffGenCodes.zrev n h.
Proof.
  induction n as [|k IH]; intro h; [reflexivity|].
  cbn [ItGTblRev.zrev HuffGenCodes.zrev].
  rewrite IH, Zmod_odd, Z.div2_div.
  destruct (Z.odd h); lia.
Qed.

(** The MSB/LSB seam, composed from the two landed halves. *)
Lemma code_bits_zrev_write : forall n h,
  code_bits (zrev n h) n = write_bits n h.
Proof.
  intros n h.
  rewrite zrev_agree, code_bits_rev_write_bits, write_bits_zrev.
  apply rev_involutive.
Qed.

(** The k-th index of length [b] in [L], counting from 0. *)
Fixpoint kth_len_sym (L : list nat) (b k : nat) : nat :=
  match L with
  | [] => 0
  | x :: L' =>
      if Nat.eq_dec x b
      then match k with
           | O => 0
           | S k' => S (kth_len_sym L' b k')
           end
      else S (kth_len_sym L' b k)
  end.

Lemma kth_len_sym_spec : forall (L : list nat) (b k : nat),
  (k < count_len L b)%nat ->
  (kth_len_sym L b k < length L)%nat
  /\ nth_error L (kth_len_sym L b k) = Some b
  /\ count_len (firstn (kth_len_sym L b k) L) b = k.
Proof.
  induction L as [|x L IH]; intros b k Hk.
  - unfold count_len in Hk. cbn in Hk. lia.
  - rewrite count_len_cons in Hk. cbn [kth_len_sym].
    destruct (Nat.eq_dec x b) as [->|Hne].
    + destruct k as [|k'].
      * split; [cbn [length]; lia|].
        split; [reflexivity|]. reflexivity.
      * destruct (IH b k' ltac:(lia)) as (H1 & H2 & H3).
        split; [cbn [length]; lia|].
        split; [exact H2|].
        cbn [firstn]. rewrite count_len_cons.
        destruct (Nat.eq_dec b b); [lia|congruence].
    + destruct (IH b k Hk) as (H1 & H2 & H3).
      split; [cbn [length]; lia|].
      split; [exact H2|].
      cbn [firstn]. rewrite count_len_cons.
      destruct (Nat.eq_dec x b); [congruence|lia].
Qed.

(** The histogram bridge: [it_pre]'s count over the window of an
    appended lens list IS [count_len] of the window list. *)
Lemma sw_cnt_app_count_len : forall (l1 l2 : list nat) (b : nat),
  sw_cnt (zlens (l1 ++ l2)) (Z.of_nat (length l1)) (Z.of_nat b)
  = Z.of_nat (count_len l1 b).
Proof.
  intros l1 l2 b. unfold sw_cnt.
  rewrite it_count_spec, Nat2Z.id.
  rewrite zcount_zlens_firstn by (rewrite app_length; lia).
  rewrite firstn_app, firstn_all, Nat.sub_diag.
  cbn [firstn]. rewrite app_nil_r.
  change (zzero (Z.of_nat b)) with 0. lia.
Qed.

(** [zcount] reads its array only on the scanned window. *)
Lemma zcount_ext_on : forall (n : nat) (i : Z) (a b : zarr) (v : Z),
  (forall j, i <= j < i + Z.of_nat n -> a j = b j) ->
  zcount n i a v = zcount n i b v.
Proof.
  induction n as [|n IH]; intros i a b v H; cbn [zcount]; [reflexivity|].
  rewrite (H i) by lia.
  rewrite (IH (i + 1) a b v) by (intros j Hj; apply H; lia).
  reflexivity.
Qed.

(** The histogram bridge at an ARBITRARY lens array agreeing with the
    list on the window — the consumers' premise shape (q7's telescope
    and g1's dispatch both run [it_pre] on zarr fields). *)
Lemma sw_cnt_agree_count_len : forall (lens : zarr) (l1 : list nat)
                                      (b : nat),
  arr_eq_on lens (zlens l1) 0 (Z.of_nat (length l1)) ->
  sw_cnt lens (Z.of_nat (length l1)) (Z.of_nat b)
  = Z.of_nat (count_len l1 b).
Proof.
  intros lens l1 b Hag. unfold sw_cnt.
  rewrite it_count_spec, Nat2Z.id.
  rewrite (zcount_ext_on (length l1) 0 lens (zlens l1) (Z.of_nat b))
    by (intros j Hj; apply Hag; lia).
  rewrite zcount_zlens_firstn by lia.
  rewrite firstn_all.
  change (zzero (Z.of_nat b)) with 0. lia.
Qed.

(** [it_entry] echoes its bits argument. *)
Lemma bits_it_entry : forall c w b,
  0 <= b < 256 -> c_bits (ZReproQ6K.it_entry c w b) = b.
Proof.
  intros c w b Hb. unfold ZReproQ6K.it_entry.
  destruct (Z.ltb (w + 1) (x_match c));
    [|destruct (Z.leb (x_match c) w)]; apply bits_mkCodeT; lia.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The canonical entry witness *)

Definition ent_of (c : ItCtx) (l1 : list nat) (sym : nat) : Code :=
  match code_for l1 15%nat sym with
  | Some cw =>
      ZReproQ6K.it_entry c (Z.of_nat sym)
        (if x_root c <? Z.of_nat (length cw)
         then Z.of_nat (length cw) - x_root c
         else Z.of_nat (length cw))
  | None => ZReproQ6K.it_entry c (Z.of_nat sym) 0
  end.

(** [code_for]'s output length is the symbol's length, in [1..15]. *)
Lemma code_for_length_window : forall l1 sym cw,
  code_for l1 15%nat sym = Some cw ->
  (1 <= length cw <= 15)%nat.
Proof.
  intros l1 sym cw Hcf. unfold code_for in Hcf. revert Hcf.
  destruct (nth_error l1 sym) as [len|]; intro Hcf; [|discriminate].
  revert Hcf.
  destruct (Nat.eqb_spec len 0) as [E|E]; cbn [orb]; intro Hcf;
    [discriminate|].
  revert Hcf.
  destruct (Nat.ltb_spec 15 len) as [E2|E2]; cbn [orb]; intro Hcf;
    [discriminate|].
  injection Hcf as <-. rewrite code_bits_length. lia.
Qed.

(** The fixpoint spelling the B3-side consumers
    ([zr_len_ents_of_tie]/[zr_dist_ents_of_tie]) take as premise. *)
Lemma ent_of_tie : forall c l1 sym,
  0 <= x_root c ->
  ent_of c l1 sym
  = ZReproQ6K.it_entry c (Z.of_nat sym) (c_bits (ent_of c l1 sym)).
Proof.
  intros c l1 sym Hroot. unfold ent_of.
  destruct (code_for l1 15%nat sym) as [cw|] eqn:Hcf.
  - pose proof (code_for_length_window l1 sym cw Hcf) as Hlen.
    rewrite bits_it_entry; [reflexivity|].
    destruct (Z.ltb_spec (x_root c) (Z.of_nat (length cw))); lia.
  - rewrite bits_it_entry; [reflexivity|lia].
Qed.

(* ------------------------------------------------------------------ *)
(** ** The ledger *)

(** LEAF payload at root cell [i] — verbatim the head's first arm. *)
Definition OwnLeaf (T : ztbl) (root : Z) (lens : list nat)
           (ent : nat -> Code) (i : Z) : Prop :=
  exists sym cw, code_for lens 15%nat sym = Some cw
    /\ Z.of_nat (length cw) <= root
    /\ T i = ent sym
    /\ c_bits (ent sym) = Z.of_nat (length cw)
    /\ firstn (length cw) (write_bits (Z.to_nat root) i) = cw.

(** Pointer payload at a CLOSED root cell: the head's second arm plus
    the region-protection bound. *)
Definition OwnPtr (T : ztbl) (root : Z) (lens : list nat)
           (ent : nat -> Code) (nxt i : Z) : Prop :=
  c_bits (T i) = root
  /\ 1 <= c_op (T i) <= 15 - root
  /\ 2 ^ root <= c_val (T i)
  /\ c_val (T i) + 2 ^ (c_op (T i)) <= nxt
  /\ zr_ptr_children T root lens ent i (c_op (T i)) (c_val (T i)).

(** Every root cell whose position window is fully consumed is
    classified. *)
Definition OwnBelow (root : Z) (lens : list nat) (ent : nat -> Code)
           (T : ztbl) (nxt P : Z) : Prop :=
  forall i, 0 <= i < 2 ^ root ->
    (zrev (Z.to_nat root) i + 1) * 2 ^ (15 - root) <= P ->
    OwnLeaf T root lens ent i \/ OwnPtr T root lens ent nxt i.

(** The single OPEN phase-2 window at [i = s_low]: geometry is in the
    table (ties to the walk's [s_next]/[s_curr]); children owned only
    below the consumed position. *)
Definition OwnOpen (T : ztbl) (root : Z) (lens : list nat)
           (ent : nat -> Code) (nxt curr P i : Z) : Prop :=
  c_bits (T i) = root
  /\ c_op (T i) = curr
  /\ c_val (T i) = nxt
  /\ 1 <= curr <= 15 - root
  /\ 2 ^ root <= nxt
  /\ (forall j, 0 <= j < 2 ^ curr ->
        zrev (Z.to_nat root) i * 2 ^ (15 - root)
        + (zrev (Z.to_nat curr) j + 1) * 2 ^ (15 - root - curr) <= P ->
        exists sym cw, code_for lens 15%nat sym = Some cw
          /\ root < Z.of_nat (length cw) <= root + curr
          /\ T (nxt + j) = ent sym
          /\ c_bits (ent sym) = Z.of_nat (length cw) - root
          /\ firstn (length cw)
               (write_bits (Z.to_nat root) i
                ++ write_bits (Z.to_nat curr) j)
             = cw).

(** The carrier — pure ownership payload.  Region accounting
    (next + 2^curr = used, used <= 65535) and the capacity/sizing
    clause are NOT here: they are g1's SubLedger's conjuncts
    (ItGSubCover:764), carried alongside by ledger_step_cont and read
    as premises by my step lemmas — engine consumed, not mirrored. *)
Definition Own (c : ItCtx) (cnt0 : zarr) (lens : list nat)
           (ent : nat -> Code) (st : ItSt) : Prop :=
  OwnBelow (x_root c) lens ent (s_tbl st) (s_next st)
           (Pos (it_mass 15%nat 1 cnt0) st)
  /\ (s_drop st = x_root c ->
        OwnOpen (s_tbl st) (x_root c) lens ent (s_next st) (s_curr st)
                (Pos (it_mass 15%nat 1 cnt0) st) (s_low st)).

(** What the last trip leaves behind, beyond [Own]: everything the
    finish read and the model-level assembly need about the break
    state.  Derived inside the break case from CovInv-at-the-last-trip
    (not loop-invariant — hence the nom_loop-pattern recursion). *)
Definition BreakShape (c : ItCtx) (cnt0 : zarr) (st1 : ItSt) : Prop :=
  it_mass 15%nat 1 (s_count st1) = 0
  /\ (it_mass 15%nat 1 cnt0 = 2 ^ 15 -> s_huff st1 = 0)
  /\ (x_max c = 1 -> it_mass 15%nat 1 cnt0 = 2 ^ 14 ->
        s_huff st1 = 1 /\ s_next st1 = 0 /\ s_drop st1 = 0
        /\ s_len st1 = 1).

(* ------------------------------------------------------------------ *)
(** ** Piece 2 — THE TIE

    The current trip's work-list entry is a symbol of [l1] whose
    canonical codeword is exactly the trip's reversed huff at the
    trip's length.  Engine: CovInv's window bracket + counts equation
    + position link; rank_prefix (KeyRank); nc_it_mass + it_mass_split
    (KeyTie); zcount_zlens_firstn (KeyRank); the seam. *)
Lemma trip_owner : forall c cnt0 (l1 : list nat) st,
  CovCtxOk c cnt0 ->
  CovInv c cnt0 st ->
  arr_eq_on (x_lens c) (zlens l1) 0 (Z.of_nat (length l1)) ->
  x_codes c = Z.of_nat (length l1) ->
  exists sym : nat,
    x_work c (s_sym st) = Z.of_nat sym
    /\ (sym < length l1)%nat
    /\ code_for l1 15%nat sym
       = Some (write_bits (Z.to_nat (s_len st)) (s_huff st)).
Proof.
  intros c cnt0 l1 st Hctx Hinv Hagree Hxcodes.
  pose proof Hagree as HagU. unfold arr_eq_on in HagU.
  destruct Hctx as (Hroot & Hmask & Hmx & Hmxnz & Hmxz & Hnn & Hcodes
                    & Hlens & Hcnt0 & Hwork & Hupper & Hcase & Hrootmx).
  destruct Hinv as (Hlen & Hhuff & HwinL & HwinU & Hcnt & Hpos & Hcov
                    & Hphase).
  set (L := s_len st) in *.
  set (Lnat := Z.to_nat L) in *.
  assert (HLnat : Z.of_nat Lnat = L) by (unfold Lnat; lia).
  assert (HL1 : (1 <= Lnat <= 15)%nat) by (unfold Lnat; lia).
  (* the histogram bridge, pointwise *)
  assert (Hbr : forall b : nat,
             cnt0 (Z.of_nat b) = Z.of_nat (count_len l1 b)).
  { intro b. rewrite Hcnt0, Hxcodes.
    apply sw_cnt_agree_count_len. exact Hagree. }
  (* the trip's window rank *)
  set (kz := s_sym st - sw_offs cnt0 L).
  assert (Hkz : 0 <= kz < cnt0 L) by (unfold kz; lia).
  set (knat := Z.to_nat kz).
  assert (Hknat : Z.of_nat knat = kz) by (unfold knat; lia).
  assert (Hkcnt : (knat < count_len l1 Lnat)%nat).
  { pose proof (Hbr Lnat) as Hb. rewrite HLnat in Hb. lia. }
  (* the owner symbol *)
  destruct (kth_len_sym_spec l1 Lnat knat Hkcnt) as (Hslt & Hsnth & Hsoff).
  set (sym := kth_len_sym l1 Lnat knat) in *.
  exists sym.
  assert (Hxlens_sym : x_lens c (Z.of_nat sym) = L).
  { rewrite HagU by lia.
    unfold zlens. rewrite Nat2Z.id.
    assert (Hn : nth sym l1 0%nat = Lnat)
      by (apply nth_error_nth; exact Hsnth).
    rewrite Hn. exact HLnat. }
  (* rank_prefix at sym, at the ARBITRARY lens array *)
  assert (Hrank :
      snd (it_sort (length l1) 0 (x_lens c) (sw_offs cnt0) zzero)
          (sw_offs cnt0 (x_lens c (Z.of_nat sym))
           + it_count sym 0 (x_lens c) zzero
               (x_lens c (Z.of_nat sym)))
      = Z.of_nat sym).
  { apply (rank_prefix (x_lens c) (Z.of_nat (length l1)) cnt0).
    - intros i Hi. apply Hlens. lia.
    - rewrite Hcnt0, Hxcodes. reflexivity.
    - rewrite Nat2Z.id. lia.
    - exact Hslt.
    - rewrite Hxlens_sym. lia. }
  rewrite Hxlens_sym in Hrank.
  (* the rank term computes to kz *)
  assert (Hcount_sym : it_count sym 0 (x_lens c) zzero L = kz).
  { rewrite it_count_spec.
    change (zzero L) with 0.
    rewrite (zcount_ext_on sym 0 (x_lens c) (zlens l1) L)
      by (intros j Hj; apply HagU; lia).
    rewrite <- HLnat.
    rewrite zcount_zlens_firstn by lia.
    rewrite Hsoff. lia. }
  rewrite Hcount_sym in Hrank.
  (* the work entry *)
  assert (Hwork_sym : x_work c (s_sym st) = Z.of_nat sym).
  { rewrite Hwork, Hxcodes. unfold sw_work.
    rewrite Nat2Z.id.
    replace (sw_cnt (x_lens c) (Z.of_nat (length l1))) with cnt0
      by (rewrite Hcnt0, Hxcodes; reflexivity).
    replace (s_sym st) with (sw_offs cnt0 L + kz) by (unfold kz; lia).
    exact Hrank. }
  (* code_for at sym *)
  assert (Hcf : code_for l1 15%nat sym
      = Some (code_bits (Z.of_nat (nc l1 Lnat + knat)) Lnat)).
  { unfold code_for. rewrite Hsnth.
    destruct (Nat.eqb_spec Lnat 0) as [E|E]; [lia|].
    destruct (Nat.ltb_spec 15 Lnat) as [E2|E2]; [lia|].
    cbn [orb]. unfold code_offset. rewrite Hsoff. reflexivity. }
  (* the value equation: split both masses at L *)
  assert (Hval : Z.of_nat (nc l1 Lnat + knat) = zrev Lnat (s_huff st)).
  { assert (HmS : forall (k : nat) (len : Z) (cnt : zarr),
        it_mass (S k) len cnt
        = cnt len * 2 ^ Z.of_nat k + it_mass k (len + 1) cnt)
      by reflexivity.
    pose proof (it_mass_split (16 - Lnat) 15 1 cnt0 ltac:(lia))
      as Hsplit0.
    pose proof (it_mass_split (16 - Lnat) 15 1 (s_count st) ltac:(lia))
      as Hsplit1.
    replace (15 - (16 - Lnat))%nat with (Lnat - 1)%nat
      in Hsplit0, Hsplit1 by lia.
    replace (1 + Z.of_nat (Lnat - 1)) with L in Hsplit0, Hsplit1 by lia.
    replace (Z.of_nat (16 - Lnat)) with (16 - L) in Hsplit0, Hsplit1
      by lia.
    assert (Hpeel0 : it_mass (16 - Lnat) L cnt0
        = cnt0 L * 2 ^ (15 - L) + it_mass (15 - Lnat) (L + 1) cnt0).
    { replace (16 - Lnat)%nat with (S (15 - Lnat))%nat by lia.
      rewrite HmS.
      replace (Z.of_nat (15 - Lnat)) with (15 - L) by lia.
      reflexivity. }
    assert (Hpeel1 : it_mass (16 - Lnat) L (s_count st)
        = s_count st L * 2 ^ (15 - L)
          + it_mass (15 - Lnat) (L + 1) (s_count st)).
    { replace (16 - Lnat)%nat with (S (15 - Lnat))%nat by lia.
      rewrite HmS.
      replace (Z.of_nat (15 - Lnat)) with (15 - L) by lia.
      reflexivity. }
    assert (Hzero : it_mass (Lnat - 1) 1 (s_count st) = 0).
    { apply it_mass_zero_on. intros j Hj.
      rewrite (Hcnt j) by lia.
      destruct (Z.ltb_spec j L); [reflexivity|lia]. }
    assert (Habove : it_mass (15 - Lnat) (L + 1) (s_count st)
                     = it_mass (15 - Lnat) (L + 1) cnt0).
    { apply it_mass_ext. intros j Hj.
      rewrite (Hcnt j) by lia.
      destruct (Z.ltb_spec j L); [lia|].
      destruct (Z.eqb_spec j L); [lia|]. reflexivity. }
    assert (HcntL : s_count st L = sw_offs cnt0 L + cnt0 L - s_sym st).
    { rewrite (Hcnt L) by lia.
      destruct (Z.ltb_spec L L); [lia|].
      destruct (Z.eqb_spec L L); [reflexivity|congruence]. }
    assert (Hnc_eq : it_mass (Lnat - 1) 1 cnt0
                     = it_mass (Lnat - 1) 1 (cntL l1)).
    { apply it_mass_ext. intros j Hj.
      rewrite <- (Z2Nat.id j) by lia.
      rewrite Hbr, cntL_in_window by lia. reflexivity. }
    pose proof (nc_it_mass l1 Lnat ltac:(lia)) as HncZ.
    rewrite <- Hnc_eq in HncZ.
    assert (HPpos : 0 < 2 ^ (15 - L)) by (apply pow2_pos_z; lia).
    assert (Hpow : 2 ^ (16 - L) = 2 * 2 ^ (15 - L)).
    { replace (16 - L) with (Z.succ (15 - L)) by lia.
      rewrite Z.pow_succ_r by lia. reflexivity. }
    assert (Hkzdef : kz = s_sym st - sw_offs cnt0 L) by reflexivity.
    rewrite Hpeel0 in Hsplit0.
    rewrite Hpeel1, Hzero, Habove, HcntL in Hsplit1.
    rewrite Hpow in Hsplit0, Hsplit1.
    unfold Pos in Hpos.
    rewrite Hsplit0, Hsplit1 in Hpos.
    rewrite Nat2Z.inj_add, HncZ, Hknat.
    nia. }
  rewrite Hval in Hcf.
  rewrite code_bits_zrev_write in Hcf.
  refine (conj Hwork_sym (conj Hslt _)).
  exact Hcf.
Qed.

(** Seed: the ledger is vacuously true at the PreGo state (position 0,
    phase 1). *)
Lemma own_seed : forall c cnt0 l1 ent st,
  s_count st = cnt0 ->
  s_drop st = 0 ->
  1 <= x_root c <= 15 ->
  Own c cnt0 l1 ent st.
Proof.
  intros c cnt0 l1 ent st Hc Hd Hr.
  assert (Hpos0 : Pos (it_mass 15%nat 1 cnt0) st = 0).
  { unfold Pos. rewrite Hc. lia. }
  unfold Own. rewrite Hpos0, Hd.
  split.
  - intros i Hi Habs. exfalso.
    pose proof (zrev_nonneg (Z.to_nat (x_root c)) i).
    assert (0 < 2 ^ (15 - x_root c)) by (apply pow2_pos_z; lia).
    nia.
  - intro Habs. lia.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Piece 3a/3b — the fill transport (statements frozen; the fill
    term is spelled VERBATIM as it_step's zeta-expanded let-body, so
    the step dissection in KeyStep.v applies these with no conversion;
    cov_after_fill (ItGTblCover:406) uses the same spelling). *)

(** Phase 1: the trip's fill writes [it_here] at every root cell of the
    trip's freshly consumed windows (they are exactly the cells
    congruent to huff mod 2^len — zrev_window_hit scaled), and misses
    every already-classified cell and every closed child (in phase 1
    there are none: OwnPtr's region bound against next = 0 refutes the
    arm).  New cells become OwnLeaf via trip_owner + firstn_write_bits
    + write_bits_mod_low. *)
Lemma own_fill_short : forall c cnt0 (l1 : list nat) st,
  CovCtxOk c cnt0 ->
  CovInv c cnt0 st ->
  arr_eq_on (x_lens c) (zlens l1) 0 (Z.of_nat (length l1)) ->
  x_codes c = Z.of_nat (length l1) ->
  s_drop st = 0 ->
  OwnBelow (x_root c) l1 (ent_of c l1) (s_tbl st) (s_next st)
           (Pos (it_mass 15%nat 1 cnt0) st) ->
  OwnBelow (x_root c) l1 (ent_of c l1)
    (it_fill (Z.to_nat (Z.shiftl 1 (s_curr st)
                        / Z.shiftl 1 (s_len st - s_drop st)))
             (s_tbl st) (s_next st + Z.shiftr (s_huff st) (s_drop st))
             (Z.shiftl 1 (s_len st - s_drop st)) (it_here c st))
    (s_next st)
    (Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st)).
Proof.
  intros c cnt0 l1 st Hctx Hinv Hagree Hxcodes Hdrop Hbelow.
  pose proof Hctx as Hctx2.
  pose proof Hinv as Hinv2.
  destruct Hctx as (Hroot & Hmask & Hmx & Hmxnz & Hmxz & Hnn & Hcodes
                    & Hlens & Hcnt0 & Hwork & Hupper & Hcase & Hrootmx).
  destruct Hinv as (Hlen & Hhuff & HwinL & HwinU & Hcnt & Hpos & Hcov
                    & Hphase).
  destruct Hphase as [(Hd0 & Hcu & Hnx & Hlowv & Hlr)
                     |(Hd2 & Hrl & Hnx2 & Hlow2 & Hlb)];
    [|exfalso; lia].
  destruct (trip_owner c cnt0 l1 st Hctx2 Hinv2 Hagree Hxcodes)
    as (sym & Hwsym & Hslt & Hcf).
  assert (HpL : 0 < 2 ^ (s_len st)) by (apply pow2_pos_z; lia).
  assert (Hpr : 0 < 2 ^ (x_root c)) by (apply pow2_pos_z; lia).
  assert (Hp15L : 0 < 2 ^ (15 - s_len st)) by (apply pow2_pos_z; lia).
  assert (Hp15r : 0 < 2 ^ (15 - x_root c)) by (apply pow2_pos_z; lia).
  assert (HprL : 0 < 2 ^ (x_root c - s_len st)) by (apply pow2_pos_z; lia).
  assert (HLid : Z.of_nat (Z.to_nat (s_len st)) = s_len st) by lia.
  assert (Hrid : Z.of_nat (Z.to_nat (x_root c)) = x_root c) by lia.
  assert (Hdid : Z.of_nat (Z.to_nat (x_root c) - Z.to_nat (s_len st))
                 = x_root c - s_len st) by lia.
  assert (Hsplit15 : 2 ^ (15 - s_len st)
                     = 2 ^ (x_root c - s_len st) * 2 ^ (15 - x_root c)).
  { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  (* normalize the fill term *)
  rewrite Hdrop, Hnx, Hcu, Z.sub_0_r, Z.shiftr_0_r, Z.add_0_l.
  rewrite !shiftl1 by lia.
  rewrite <- Z.pow_sub_r by lia.
  (* the scale-free hit characterization, instantiated *)
  pose proof (zrev_window_hit (Z.to_nat (s_len st)) (Z.to_nat (x_root c))
                (s_huff st)) as Hwh0.
  intros j Hj Hguard.
  pose proof (Hwh0 j) as Hwh.
  rewrite HLid, Hrid, Hdid in Hwh.
  specialize (Hwh ltac:(lia) ltac:(lia) ltac:(lia)).
  pose proof (zrev_nonneg (Z.to_nat (x_root c)) j) as Hzjn.
  pose proof (zrev_lt (Z.to_nat (x_root c)) j) as Hzjl.
  rewrite Hrid in Hzjl.
  pose proof (zrev_nonneg (Z.to_nat (s_len st)) (s_huff st)) as Hzhn.
  pose proof (zrev_lt (Z.to_nat (s_len st)) (s_huff st)) as Hzhl.
  rewrite HLid in Hzhl.
  assert (HZid : Z.of_nat (Z.to_nat (2 ^ (x_root c - s_len st)))
                 = 2 ^ (x_root c - s_len st)) by lia.
  destruct (Z_le_gt_dec ((zrev (Z.to_nat (x_root c)) j + 1)
                         * 2 ^ (15 - x_root c))
                        (Pos (it_mass 15%nat 1 cnt0) st)) as [Hold|Hnew].
  - (* OLD: untouched — the hit set's windows all lie strictly above P *)
    assert (Hmiss : it_fill (Z.to_nat (2 ^ (x_root c - s_len st)))
                      (s_tbl st) (s_huff st) (2 ^ (s_len st))
                      (it_here c st) j
                    = s_tbl st j).
    { rewrite it_fill_get by lia.
      destruct (Z.leb_spec (s_huff st) j) as [Hle|]; cbn [andb];
        [|reflexivity].
      destruct (Z.ltb_spec j (s_huff st
                 + Z.of_nat (Z.to_nat (2 ^ (x_root c - s_len st)))
                   * 2 ^ (s_len st))) as [Hlt|]; cbn [andb];
        [|reflexivity].
      destruct (Z.eqb_spec ((j - s_huff st) mod 2 ^ (s_len st)) 0)
        as [Hmod|]; cbn [andb]; [|reflexivity].
      exfalso.
      assert (Hjm : j mod 2 ^ (s_len st) = s_huff st).
      { apply Z.mod_divide in Hmod; [|lia].
        destruct Hmod as [q Hq].
        replace j with (s_huff st + q * 2 ^ (s_len st)) by lia.
        rewrite Z.mod_add by lia.
        apply Z.mod_small; lia. }
      apply (proj2 Hwh) in Hjm.
      destruct Hjm as [Hlo Hhi].
      assert (Hstep : zrev (Z.to_nat (s_len st)) (s_huff st)
                        * 2 ^ (x_root c - s_len st)
                        * 2 ^ (15 - x_root c)
                      <= zrev (Z.to_nat (x_root c)) j
                         * 2 ^ (15 - x_root c)) by nia.
      rewrite Hpos, Hsplit15 in Hold. nia. }
    destruct (Hbelow j Hj Hold) as [Hleaf | Hptr].
    + left. unfold OwnLeaf in Hleaf |- *.
      destruct Hleaf as (sym' & cw' & H1 & H2 & H3 & H4 & H5).
      exists sym', cw'. rewrite Hmiss. tauto.
    + exfalso.
      destruct Hptr as (Hb & Hop & Hval & Hreg & _).
      assert (0 < 2 ^ (c_op (s_tbl st j))) by (apply pow2_pos_z; lia).
      lia.
  - (* NEW: exactly the hit cells; they become OwnLeaf *)
    rewrite Hpos, Hsplit15 in Hnew, Hguard.
    assert (Hlo : zrev (Z.to_nat (s_len st)) (s_huff st)
                    * 2 ^ (x_root c - s_len st)
                  <= zrev (Z.to_nat (x_root c)) j) by nia.
    assert (Hhi : zrev (Z.to_nat (x_root c)) j
                  < zrev (Z.to_nat (s_len st)) (s_huff st)
                      * 2 ^ (x_root c - s_len st)
                    + 2 ^ (x_root c - s_len st)) by nia.
    assert (Hjm : j mod 2 ^ (s_len st) = s_huff st)
      by (apply (proj1 Hwh); split; assumption).
    pose proof (Z.div_mod j (2 ^ (s_len st)) ltac:(lia)) as Hdm.
    assert (Hj2 : j = s_huff st + (j / 2 ^ (s_len st)) * 2 ^ (s_len st))
      by lia.
    assert (Hqb : 0 <= j / 2 ^ (s_len st) < 2 ^ (x_root c - s_len st)).
    { split.
      - apply Z.div_pos; lia.
      - apply Z.div_lt_upper_bound; [lia|].
        rewrite <- Z.pow_add_r by lia.
        replace (s_len st + (x_root c - s_len st)) with (x_root c) by lia.
        lia. }
    assert (Hhit : it_fill (Z.to_nat (2 ^ (x_root c - s_len st)))
                     (s_tbl st) (s_huff st) (2 ^ (s_len st))
                     (it_here c st) j
                   = it_here c st).
    { rewrite Hj2.
      replace ((j / 2 ^ (s_len st)) * 2 ^ (s_len st)) with
        (Z.of_nat (Z.to_nat (j / 2 ^ (s_len st))) * 2 ^ (s_len st)) by lia.
      apply it_fill_hit; [lia|lia]. }
    left. unfold OwnLeaf.
    exists sym, (write_bits (Z.to_nat (s_len st)) (s_huff st)).
    assert (Hlenw : Z.of_nat (length (write_bits (Z.to_nat (s_len st))
                                        (s_huff st))) = s_len st)
      by (rewrite write_bits_length; lia).
    assert (Hent : ent_of c l1 sym
                   = ZReproQ6K.it_entry c (Z.of_nat sym) (s_len st)).
    { unfold ent_of. rewrite Hcf. cbv beta iota.
      rewrite Hlenw.
      destruct (Z.ltb_spec (x_root c) (s_len st)); [lia|reflexivity]. }
    assert (Hhere : it_here c st
                    = ZReproQ6K.it_entry c (Z.of_nat sym) (s_len st)).
    { rewrite it_here_entry, Hwsym, Hdrop, Z.sub_0_r. reflexivity. }
    split; [exact Hcf|].
    split; [rewrite Hlenw; lia|].
    split; [rewrite Hhit, Hhere, Hent; reflexivity|].
    split.
    + rewrite Hent. rewrite bits_it_entry by lia. now rewrite Hlenw.
    + rewrite write_bits_length.
      rewrite firstn_write_bits by lia.
      apply write_bits_mod_low.
      rewrite HLid, Hjm.
      rewrite Z.mod_small by lia.
      reflexivity.
Qed.

(** Phase 2: the fill writes children of the OPEN window only (base
    s_next >= 2^root misses all root cells and all closed children via
    their region bounds); newly consumed child windows are exactly the
    cells congruent to (huff >> root) mod 2^(len-root) one level down.
    len <= root + curr comes from SubLedger's capacity clause: below-len
    counts are zero (counts equation), so len > root + curr would make
    wmass (root+curr) vanish (wmass_zero_on) and the capacity clause
    would put the window top at or below P, contradicting the position
    link's P < top.  The child payload: trip_owner + write_bits_app_split
    + firstn_write_bits + write_bits_mod_low + Z.shiftr_div_pow2. *)
(** Three conclusions, assembled by the caller per exit branch:
    (i) reads of every below-P root cell and closed child are
    preserved (fill base >= next misses them all — fill_miss_below
    against the region bounds), so OwnBelow AT P transports;
    (ii) the open window's children extend to P + 2^(15-len);
    (iii) if this trip's chunk lands exactly on the window top (the
    boundary trip — the only way the open window can complete), the
    window upgrades to a closed OwnPtr at the WIDENED region bound
    next + 2^curr (= the creation exit's next'; the no-creation exit
    is impossible at the boundary, which the caller shows from
    CovInv(st')'s position link). *)
Lemma own_fill_long : forall c cnt0 (l1 : list nat) st,
  CovCtxOk c cnt0 ->
  CovInv c cnt0 st ->
  SubLedger (x_type c) c cnt0 st ->
  arr_eq_on (x_lens c) (zlens l1) 0 (Z.of_nat (length l1)) ->
  x_codes c = Z.of_nat (length l1) ->
  s_drop st = x_root c ->
  OwnBelow (x_root c) l1 (ent_of c l1) (s_tbl st) (s_next st)
           (Pos (it_mass 15%nat 1 cnt0) st) ->
  OwnOpen (s_tbl st) (x_root c) l1 (ent_of c l1) (s_next st) (s_curr st)
          (Pos (it_mass 15%nat 1 cnt0) st) (s_low st) ->
  OwnBelow (x_root c) l1 (ent_of c l1)
    (it_fill (Z.to_nat (Z.shiftl 1 (s_curr st)
                        / Z.shiftl 1 (s_len st - s_drop st)))
             (s_tbl st) (s_next st + Z.shiftr (s_huff st) (s_drop st))
             (Z.shiftl 1 (s_len st - s_drop st)) (it_here c st))
    (s_next st)
    (Pos (it_mass 15%nat 1 cnt0) st)
  /\ OwnOpen
    (it_fill (Z.to_nat (Z.shiftl 1 (s_curr st)
                        / Z.shiftl 1 (s_len st - s_drop st)))
             (s_tbl st) (s_next st + Z.shiftr (s_huff st) (s_drop st))
             (Z.shiftl 1 (s_len st - s_drop st)) (it_here c st))
    (x_root c) l1 (ent_of c l1) (s_next st) (s_curr st)
    (Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st)) (s_low st)
  /\ (Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st)
      = UnitStart (x_root c) (s_low st) + 2 ^ (15 - x_root c) ->
      OwnPtr
        (it_fill (Z.to_nat (Z.shiftl 1 (s_curr st)
                            / Z.shiftl 1 (s_len st - s_drop st)))
                 (s_tbl st) (s_next st + Z.shiftr (s_huff st) (s_drop st))
                 (Z.shiftl 1 (s_len st - s_drop st)) (it_here c st))
        (x_root c) l1 (ent_of c l1)
        (s_next st + 2 ^ (s_curr st)) (s_low st)).
Proof.
  intros c cnt0 l1 st Hctx Hinv Hled Hagree Hxcodes Hdrop Hbelow Hopen.
  pose proof Hctx as Hctx2. pose proof Hinv as Hinv2.
  destruct Hctx as (Hroot & Hmask & Hmx & Hmxnz & Hmxz & Hnn & Hcodes
                    & Hlens & Hcnt0 & Hwork & Hupper & Hcase & Hrootmx).
  destruct Hinv as (Hlen & Hhuff & HwinL & HwinU & Hcnt & Hpos & Hcov
                    & Hphase).
  destruct Hphase as [(Hd0 & Hcu & Hnx & Hlowv & Hlr)
                     |(Hd2 & Hrl & Hnx2 & Hlow2 & Hlb)];
    [exfalso; lia|].
  destruct Hled as [Hgen Hph2].
  destruct Hph2 as [(Hd0' & Hu0 & Hn0)
                   |(Hd2' & Hcurr & Husedeq & Hnx3 & Hused65 & Hclosed
                     & Hgsub & Hrootlow & Hcap)];
    [exfalso; lia|].
  destruct (trip_owner c cnt0 l1 st Hctx2 Hinv2 Hagree Hxcodes)
    as (sym & Hwsym & Hslt & Hcf).
  destruct Hopen as (Ho1 & Ho2 & Ho3 & Ho4 & Ho5 & Hokids).
  assert (HpL : 0 < 2 ^ (s_len st)) by (apply pow2_pos_z; lia).
  assert (Hpr : 0 < 2 ^ (x_root c)) by (apply pow2_pos_z; lia).
  assert (Hp15L : 0 < 2 ^ (15 - s_len st)) by (apply pow2_pos_z; lia).
  assert (Hp15r : 0 < 2 ^ (15 - x_root c)) by (apply pow2_pos_z; lia).
  assert (HpLr : 0 < 2 ^ (s_len st - x_root c)) by (apply pow2_pos_z; lia).
  assert (Hpcurr : 0 < 2 ^ (s_curr st)) by (apply pow2_pos_z; lia).
  assert (Hp15rc : 0 < 2 ^ (15 - x_root c - s_curr st))
    by (apply pow2_pos_z; lia).
  assert (HLid : Z.of_nat (Z.to_nat (s_len st)) = s_len st) by lia.
  assert (Hrid : Z.of_nat (Z.to_nat (x_root c)) = x_root c) by lia.
  assert (Hdid : Z.of_nat (Z.to_nat (s_len st - x_root c))
                 = s_len st - x_root c) by lia.
  assert (Hcid : Z.of_nat (Z.to_nat (s_curr st)) = s_curr st) by lia.
  assert (Hlowb : 0 <= s_low st < 2 ^ (x_root c))
    by (rewrite Hlow2; apply Z.mod_pos_bound; lia).
  assert (Hhqb : 0 <= s_huff st / 2 ^ (x_root c)
                 < 2 ^ (s_len st - x_root c)).
  { split; [apply Z.div_pos; lia|].
    apply Z.div_lt_upper_bound; [lia|].
    rewrite <- Z.pow_add_r by lia.
    replace (x_root c + (s_len st - x_root c)) with (s_len st) by lia.
    lia. }
  assert (Hhq : s_huff st
                = s_low st + (s_huff st / 2 ^ (x_root c)) * 2 ^ (x_root c)).
  { pose proof (Z.div_mod (s_huff st) (2 ^ (x_root c)) ltac:(lia)).
    rewrite Hlow2. lia. }
  (* the position split at the root boundary *)
  pose proof (zrev_split (Z.to_nat (x_root c))
                (Z.to_nat (s_len st - x_root c))
                (s_low st) (s_huff st / 2 ^ (x_root c))) as Hzsplit.
  rewrite Hrid, Hdid in Hzsplit.
  specialize (Hzsplit ltac:(lia)).
  replace (Z.to_nat (x_root c) + Z.to_nat (s_len st - x_root c))%nat
    with (Z.to_nat (s_len st)) in Hzsplit by lia.
  rewrite <- Hhq in Hzsplit.
  assert (Hposplit : Pos (it_mass 15%nat 1 cnt0) st
      = zrev (Z.to_nat (x_root c)) (s_low st) * 2 ^ (15 - x_root c)
        + zrev (Z.to_nat (s_len st - x_root c))
            (s_huff st / 2 ^ (x_root c)) * 2 ^ (15 - s_len st)).
  { rewrite Hpos, Hzsplit.
    rewrite Z.mul_add_distr_r.
    f_equal.
    rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia.
    f_equal. f_equal. lia. }
  pose proof (zrev_nonneg (Z.to_nat (s_len st - x_root c))
                (s_huff st / 2 ^ (x_root c))) as Hqn.
  pose proof (zrev_lt (Z.to_nat (s_len st - x_root c))
                (s_huff st / 2 ^ (x_root c))) as Hql.
  rewrite Hdid in Hql.
  pose proof (zrev_nonneg (Z.to_nat (x_root c)) (s_low st)) as Hzlown.
  assert (Hsplit15r : 2 ^ (15 - s_len st) * 2 ^ (s_len st - x_root c)
                      = 2 ^ (15 - x_root c))
    by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (HPub : Pos (it_mass 15%nat 1 cnt0) st
                 < zrev (Z.to_nat (x_root c)) (s_low st) * 2 ^ (15 - x_root c)
                   + 2 ^ (15 - x_root c)).
  { rewrite Hposplit. clear -Hql Hqn Hp15L Hsplit15r. nia. }
  unfold UnitStart in Hcap.
  (* the sizing fact: this trip's length fits the open window *)
  assert (Hlc : s_len st <= x_root c + s_curr st).
  { destruct (Z.le_gt_cases (s_len st) (x_root c + s_curr st));
      [assumption|exfalso].
    assert (Hwz : wmass (Z.to_nat (x_root c + s_curr st)) 1 (s_count st)
                  = 0).
    { apply wmass_zero_on. intros j Hj.
      rewrite (Hcnt j) by lia.
      destruct (Z.ltb_spec j (s_len st)); [reflexivity|lia]. }
    rewrite Hwz in Hcap. lia. }
  (* normalize the fill term *)
  rewrite Hdrop.
  rewrite !shiftl1 by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite <- Z.pow_sub_r by lia.
  match goal with
  | |- context [it_fill ?n ?t ?b ?i ?h] => set (T1 := it_fill n t b i h)
  end.
  assert (HZid : Z.of_nat (Z.to_nat (2 ^ (s_curr st - (s_len st - x_root c))))
                 = 2 ^ (s_curr st - (s_len st - x_root c))) by lia.
  assert (HDD : 2 ^ (s_curr st - (s_len st - x_root c))
                  * 2 ^ (s_len st - x_root c)
                = 2 ^ (s_curr st))
    by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (Hscale : 2 ^ (15 - s_len st)
                   = 2 ^ (s_curr st - (s_len st - x_root c))
                     * 2 ^ (15 - x_root c - s_curr st))
    by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (HmissBelowNext : forall i, i < s_next st -> T1 i = s_tbl st i).
  { intros i Hi. unfold T1. apply fill_miss_below; [lia|lia]. }
  (* (ii) first: the open window, extended by this trip's chunk *)
  assert (HOpen1 : OwnOpen T1 (x_root c) l1 (ent_of c l1) (s_next st)
                     (s_curr st)
                     (Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st))
                     (s_low st)).
  { unfold OwnOpen.
    rewrite (HmissBelowNext (s_low st) ltac:(lia)).
    split; [exact Ho1|]. split; [exact Ho2|]. split; [exact Ho3|].
    split; [exact Ho4|]. split; [exact Ho5|].
    intros j' Hj' Hg'.
    pose proof (zrev_window_hit (Z.to_nat (s_len st - x_root c))
                  (Z.to_nat (s_curr st)) (s_huff st / 2 ^ (x_root c)) j')
      as Hwh.
    assert (Hddid : Z.of_nat (Z.to_nat (s_curr st)
                              - Z.to_nat (s_len st - x_root c))
                    = s_curr st - (s_len st - x_root c)) by lia.
    rewrite Hdid, Hcid, Hddid in Hwh.
    specialize (Hwh ltac:(lia) ltac:(lia) ltac:(lia)).
    pose proof (zrev_nonneg (Z.to_nat (s_curr st)) j') as Hzj'n.
    pose proof (zrev_lt (Z.to_nat (s_curr st)) j') as Hzj'l.
    rewrite Hcid in Hzj'l.
    destruct (Z_le_gt_dec
                (zrev (Z.to_nat (x_root c)) (s_low st) * 2 ^ (15 - x_root c)
                 + (zrev (Z.to_nat (s_curr st)) j' + 1)
                   * 2 ^ (15 - x_root c - s_curr st))
                (Pos (it_mass 15%nat 1 cnt0) st)) as [HgOld|HgNew].
    - (* OLD child: read preserved, payload transported *)
      assert (Hmk : T1 (s_next st + j') = s_tbl st (s_next st + j')).
      { unfold T1. rewrite it_fill_get by lia.
        destruct (Z.leb_spec (s_next st + s_huff st / 2 ^ (x_root c))
                             (s_next st + j')) as [Hle|]; cbn [andb];
          [|reflexivity].
        destruct (Z.ltb_spec (s_next st + j')
                   (s_next st + s_huff st / 2 ^ (x_root c)
                    + Z.of_nat (Z.to_nat
                        (2 ^ (s_curr st - (s_len st - x_root c))))
                      * 2 ^ (s_len st - x_root c))) as [Hlt|]; cbn [andb];
          [|reflexivity].
        destruct (Z.eqb_spec ((s_next st + j'
                               - (s_next st + s_huff st / 2 ^ (x_root c)))
                              mod 2 ^ (s_len st - x_root c)) 0)
          as [Hmod|]; cbn [andb]; [|reflexivity].
        exfalso.
        assert (Hj'm : j' mod 2 ^ (s_len st - x_root c)
                       = s_huff st / 2 ^ (x_root c)).
        { replace (s_next st + j'
                   - (s_next st + s_huff st / 2 ^ (x_root c)))
            with (j' - s_huff st / 2 ^ (x_root c)) in Hmod by ring.
          apply Z.mod_divide in Hmod; [|lia].
          destruct Hmod as [q Hq].
          replace j' with (s_huff st / 2 ^ (x_root c)
                           + q * 2 ^ (s_len st - x_root c)) by lia.
          rewrite Z.mod_add by lia.
          apply Z.mod_small; lia. }
        apply (proj2 Hwh) in Hj'm.
        destruct Hj'm as [Hlo' Hhi'].
        assert (Hstep : zrev (Z.to_nat (s_len st - x_root c))
                          (s_huff st / 2 ^ (x_root c))
                          * 2 ^ (s_curr st - (s_len st - x_root c))
                          * 2 ^ (15 - x_root c - s_curr st)
                        <= zrev (Z.to_nat (s_curr st)) j'
                           * 2 ^ (15 - x_root c - s_curr st))
          by (apply Z.mul_le_mono_nonneg_r; lia).
        rewrite Hposplit, Hscale in HgOld.
        clear -HgOld Hstep Hp15rc. nia. }
      destruct (Hokids j' Hj' HgOld)
        as (sym' & cw' & K1 & K2 & K3 & K4 & K5).
      exists sym', cw'. rewrite Hmk. tauto.
    - (* NEW child *)
      rewrite Hposplit, Hscale in HgNew, Hg'.
      assert (Hlo' : zrev (Z.to_nat (s_len st - x_root c))
                       (s_huff st / 2 ^ (x_root c))
                       * 2 ^ (s_curr st - (s_len st - x_root c))
                     <= zrev (Z.to_nat (s_curr st)) j')
        by (clear -HgNew Hp15rc; nia).
      assert (Hhi' : zrev (Z.to_nat (s_curr st)) j'
                     < zrev (Z.to_nat (s_len st - x_root c))
                         (s_huff st / 2 ^ (x_root c))
                         * 2 ^ (s_curr st - (s_len st - x_root c))
                       + 2 ^ (s_curr st - (s_len st - x_root c)))
        by (clear -Hg' Hp15rc; nia).
      assert (Hj'm : j' mod 2 ^ (s_len st - x_root c)
                     = s_huff st / 2 ^ (x_root c))
        by (apply (proj1 Hwh); split; assumption).
      pose proof (Z.div_mod j' (2 ^ (s_len st - x_root c)) ltac:(lia))
        as Hdm'.
      assert (Hqb' : 0 <= j' / 2 ^ (s_len st - x_root c)
                     < 2 ^ (s_curr st - (s_len st - x_root c))).
      { split; [apply Z.div_pos; lia|].
        apply Z.div_lt_upper_bound; [lia|].
        rewrite <- Z.pow_add_r by lia.
        replace (s_len st - x_root c
                 + (s_curr st - (s_len st - x_root c)))
          with (s_curr st) by lia. lia. }
      assert (Hhit : T1 (s_next st + j') = it_here c st).
      { unfold T1.
        replace (s_next st + j')
          with ((s_next st + s_huff st / 2 ^ (x_root c))
                + Z.of_nat (Z.to_nat (j' / 2 ^ (s_len st - x_root c)))
                  * 2 ^ (s_len st - x_root c)) by lia.
        apply it_fill_hit; [lia|lia]. }
      exists sym, (write_bits (Z.to_nat (s_len st)) (s_huff st)).
      assert (Hlenw : Z.of_nat (length (write_bits (Z.to_nat (s_len st))
                                          (s_huff st))) = s_len st)
        by (rewrite write_bits_length; lia).
      assert (Hent : ent_of c l1 sym
                     = ZReproQ6K.it_entry c (Z.of_nat sym)
                         (s_len st - x_root c)).
      { unfold ent_of. rewrite Hcf. cbv beta iota.
        rewrite Hlenw.
        destruct (Z.ltb_spec (x_root c) (s_len st)); [reflexivity|lia]. }
      assert (Hhere : it_here c st
                      = ZReproQ6K.it_entry c (Z.of_nat sym)
                          (s_len st - x_root c)).
      { rewrite it_here_entry, Hwsym, Hdrop. reflexivity. }
      split; [exact Hcf|].
      split; [rewrite Hlenw; lia|].
      split; [rewrite Hhit, Hhere, Hent; reflexivity|].
      split.
      + rewrite Hent. rewrite bits_it_entry by lia. now rewrite Hlenw.
      + rewrite write_bits_length.
        rewrite firstn_app.
        rewrite (write_bits_length (Z.to_nat (x_root c)) (s_low st)).
        rewrite firstn_all2 by (rewrite write_bits_length; lia).
        rewrite firstn_write_bits by lia.
        rewrite (write_bits_app_split (Z.to_nat (x_root c))
                   (Z.to_nat (s_len st)) (s_huff st)) by lia.
        rewrite Hrid.
        f_equal.
        * apply write_bits_mod_low.
          rewrite Hrid, Hlow2, Z.mod_mod by lia.
          reflexivity.
        * apply write_bits_mod_low.
          assert (HdLr : Z.of_nat (Z.to_nat (s_len st)
                                   - Z.to_nat (x_root c))
                         = s_len st - x_root c) by lia.
          rewrite HdLr, Hj'm.
          rewrite Z.mod_small by lia.
          reflexivity. }
  (* (i) reads of everything below P are preserved *)
  assert (HBelow1 : OwnBelow (x_root c) l1 (ent_of c l1) T1 (s_next st)
                      (Pos (it_mass 15%nat 1 cnt0) st)).
  { intros j Hj Hg.
    assert (Hmr : T1 j = s_tbl st j) by (apply HmissBelowNext; lia).
    destruct (Hbelow j Hj Hg) as [Hleaf|Hptr].
    - left. unfold OwnLeaf in Hleaf |- *.
      destruct Hleaf as (sym' & cw' & K1 & K2 & K3 & K4 & K5).
      exists sym', cw'. rewrite Hmr. tauto.
    - right. destruct Hptr as (Hb & Hop & Hval & Hreg & Hkids).
      assert (Hpop : 0 < 2 ^ (c_op (s_tbl st j)))
        by (apply pow2_pos_z; lia).
      unfold OwnPtr. rewrite Hmr.
      split; [exact Hb|]. split; [exact Hop|]. split; [exact Hval|].
      split; [exact Hreg|].
      intros k Hk.
      assert (Hmk : T1 (c_val (s_tbl st j) + k)
                    = s_tbl st (c_val (s_tbl st j) + k))
        by (apply HmissBelowNext; lia).
      destruct (Hkids k Hk) as (sym' & cw' & K1 & K2 & K3 & K4 & K5).
      exists sym', cw'. rewrite Hmk. tauto. }
  (* (iii) the boundary upgrade *)
  assert (HPtrBound :
      Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st)
      = UnitStart (x_root c) (s_low st) + 2 ^ (15 - x_root c) ->
      OwnPtr T1 (x_root c) l1 (ent_of c l1)
             (s_next st + 2 ^ (s_curr st)) (s_low st)).
  { intro Hbound. unfold UnitStart in Hbound.
    destruct HOpen1 as (Hb & Hopeq & Hvaleq & Hcb & Hnb & Hkids').
    unfold OwnPtr.
    rewrite Hb, Hopeq, Hvaleq.
    split; [reflexivity|].
    split; [exact Hcb|].
    split; [exact Hnb|].
    split; [lia|].
    unfold zr_ptr_children.
    intros k Hk.
    apply (Hkids' k Hk).
    pose proof (zrev_lt (Z.to_nat (s_curr st)) k) as Hzkl.
    rewrite Hcid in Hzkl.
    pose proof (zrev_nonneg (Z.to_nat (s_curr st)) k) as Hzkn.
    assert (Hcs : 2 ^ (s_curr st) * 2 ^ (15 - x_root c - s_curr st)
                  = 2 ^ (15 - x_root c))
      by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    rewrite Hbound. clear -Hzkl Hzkn Hcs Hp15rc. nia. }
  exact (conj HBelow1 (conj HOpen1 HPtrBound)).
Qed.
