(** * KraftDlNn -- [DlNn] as a MODEL-WIDE INVARIANT, not a header claim.

    OWNER: kraftsum.  Taken from zlib-lead: item 4's positive-frequency class is
    Qed ([BtItem4.item4_L_positive]) and owes exactly [DlNn (ts_trees s TK_L)] at
    entry -- non-negativity of the length array -- with no supplier named.

    WHY IT WANTED A PROOF RATHER THAN A CITATION.  huffman-id's [BuildChain]
    header says [DlNn] is free "from the [u16] writes".  **That covers the SETTERS
    and nothing else.**  A census of every writer of [tr_dl] in [Trees.v] --
    [mkTree] appears eight times, of which one is the record declaration and five
    are constructions -- gives four ingredients, and only two of them are about
    [u16]:

      tzero                (:217)     tr_dl = zzero                    all zeros
      t_setfreq/t_setcode  (:227/229) tr_dl passed THROUGH              frame
      t_setdad/t_setlen    (:231/233) zset (tr_dl t) i (u16 v)          u16 >= 0
      static_ltree/dtree   (:235/236) mkTree _ (zlist static_*_len)     LITERAL DATA

    **The two static trees are literal data, so their non-negativity is a
    COMPUTATION and not a consequence of masking.**  Measured before being
    claimed: [forallb (Z.leb 0) static_ltree_len = true] over 288 entries and
    [static_dtree_len] over 30.  So the header's claim is INCOMPLETE rather than
    wrong -- which is exactly the shape that survives having the file open, and the
    reason zlib-lead asked for a proof.

    (And the [u16] half is genuinely free even at a negative argument:
    [u16 (-1) = 65535], measured.  [Z.mod] with a positive modulus cannot be
    negative, so the setters need no hypothesis on [v] at all.) *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** huffman-id's predicate, restated rather than imported -- [BuildChain.v] is not
    in the graded tree, and reproving a one-line definition inline is cheaper than
    a dependency on an unlandable stage (their own standing advice). *)
Definition DlNn (t : Tree) : Prop := forall i, 0 <= t_len t i.

(** ** 1. The [u16] half -- free, and free without any hypothesis on [v] *)
Lemma u16_nonneg : forall v, 0 <= u16 v.
Proof. intro v. unfold u16. apply Z.mod_pos_bound. lia. Qed.

Lemma DlNn_setlen : forall t i v, DlNn t -> DlNn (t_setlen t i v).
Proof.
  intros t i v H j. unfold t_setlen, t_len. cbn [tr_dl]. unfold zset.
  destruct (Z.eqb j i); [apply u16_nonneg | apply H].
Qed.

Lemma DlNn_setdad : forall t i v, DlNn t -> DlNn (t_setdad t i v).
Proof.
  intros t i v H j. unfold t_setdad, t_len. cbn [tr_dl]. unfold zset.
  destruct (Z.eqb j i); [apply u16_nonneg | apply H].
Qed.

(** ** 2. The FRAME half -- the frequency setters do not touch [tr_dl] at all *)
Lemma DlNn_setfreq : forall t i v, DlNn t -> DlNn (t_setfreq t i v).
Proof. intros t i v H j. unfold t_setfreq, t_len. cbn [tr_dl]. apply H. Qed.

Lemma DlNn_setcode : forall t i v, DlNn t -> DlNn (t_setcode t i v).
Proof. intros t i v H j. unfold t_setcode, t_len. cbn [tr_dl]. apply H. Qed.

(** ** 3. The BASE cases -- the half the header's claim does not reach

    [zlist]'s non-negativity from a decidable check on the literal list.  Proved
    inline rather than imported from [SendTreeRT] for the same reason as [DlNn]:
    that module is landed source-only with no [.vo]. *)
Lemma zlist_nonneg_here : forall l i,
  forallb (Z.leb 0) l = true -> 0 <= zlist l i.
Proof.
  intros l i H. unfold zlist.
  destruct (nth_in_or_default (Z.to_nat i) l 0) as [Hin|Hd].
  - apply Z.leb_le. exact (proj1 (forallb_forall (Z.leb 0) l) H _ Hin).
  - rewrite Hd. lia.
Qed.

Lemma DlNn_tzero : DlNn tzero.
Proof. intro i. unfold tzero, t_len. cbn [tr_dl]. unfold zzero, zconst. lia. Qed.

Lemma DlNn_static_ltree : DlNn static_ltree.
Proof.
  intro i. unfold static_ltree, t_len. cbn [tr_dl].
  apply zlist_nonneg_here. vm_compute. reflexivity.
Qed.

Lemma DlNn_static_dtree : DlNn static_dtree.
Proof.
  intro i. unfold static_dtree, t_len. cbn [tr_dl].
  apply zlist_nonneg_here. vm_compute. reflexivity.
Qed.

(** ** 4. AT A STATE -- the shape item 4's premise is stated in

    [ts_new]'s [ts_trees] is [fun _ => tzero], so the invariant holds at every
    tree kind at the freshly-allocated state.  This is a CONCRETE discharge of
    item 4's entry premise at the initial state, not a reduction of it. *)
Definition DlNnSt (s : TSt) : Prop := forall k, DlNn (ts_trees s k).

Theorem DlNnSt_ts_new : DlNnSt ts_new.
Proof. intros k i. unfold ts_new. cbn [ts_trees]. apply DlNn_tzero. Qed.

(** [set_tree] preserves the state-level invariant when the tree it installs
    satisfies it -- so a caller threading [DlNnSt] through the deflate loop pays
    one obligation per tree it installs, and nothing per read. *)
Theorem DlNnSt_set_tree : forall k t s,
  DlNnSt s -> DlNn t -> DlNnSt (set_tree k t s).
Proof.
  intros k t s Hs Ht j i. unfold set_tree, set_trees. cbn [ts_trees].
  destruct (Z.eqb j k); [apply Ht | apply Hs].
Qed.

(** And item 4's premise, at the shape [BtItem4.item4_L_positive] asks for it. *)
Corollary DlNn_at_TK_L : forall s, DlNnSt s -> DlNn (ts_trees s TK_L).
Proof. intros s H. apply H. Qed.

(** ** 5. WHAT IS AND IS NOT CLOSED, stated so nobody reads more into it

    CLOSED: [DlNn] is preserved by every writer of [tr_dl] in [Trees.v] and holds
    at all three base trees, so it is a genuine invariant rather than an
    assumption -- and it is DISCHARGED outright at [ts_new].

    NOT CLOSED: carrying [DlNnSt] from [ts_new] to the state [build_tree] is
    called at requires one [DlNn] obligation per [set_tree] along the deflate
    loop.  [DlNnSt_set_tree] is the step; the loop-level induction belongs to
    whoever owns that loop, and I am not claiming it.  **What changes is the
    price: it was "prove non-negativity", it is now "thread a preserved predicate
    whose every step is Qed."**

    ALSO NOT CLOSED, and worth naming because a census found it: [mkTree] is also
    used in [HuffMaxBits], [HuffGenCodes], [SendTreeRT] and [SendItems].  Those are
    witness and test trees rather than anything [build_tree] consumes, so they do
    not threaten the invariant -- but I have not proved they do not, and a lane
    feeding one of those into [build_tree] would owe [DlNn] for it separately. *)

Print Assumptions u16_nonneg.
Print Assumptions DlNn_setlen.
Print Assumptions DlNn_setdad.
Print Assumptions DlNn_setfreq.
Print Assumptions DlNn_setcode.
Print Assumptions zlist_nonneg_here.
Print Assumptions DlNn_tzero.
Print Assumptions DlNn_static_ltree.
Print Assumptions DlNn_static_dtree.
Print Assumptions DlNnSt_ts_new.
Print Assumptions DlNnSt_set_tree.
Print Assumptions DlNn_at_TK_L.
