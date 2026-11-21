(** * OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.ItGTblLeafPos — guarded positivity of distance-table values

    huffman-id's remaining case. They need, at [inf_DIST]'s [set_offset]
    ([Inflate.v:1039-1042]), that the entry it is about to use has
    [1 <= c_val] — so a match copy cannot read the cell it is about to write.
    The fixed tables they closed themselves; what is left is the DYNAMIC
    distance table, i.e. [it_model]'s output.

    THE TRAP THEY FLAGGED IS REAL, AND IT DECIDES THE STATEMENT.  A TOTAL
    statement of the form "[op & 64 = 0] implies [1 <= c_val]" is FALSE, and not
    only at the unwritten indices they spotted: it is false of any entry whose
    [op] is 0, because [Z.land 0 64 = 0] satisfies the antecedent and [c_val] is
    then whatever the caller's table held.  Their fix was an index bound; this
    file uses the OTHER exclusion available at the same site, and it costs
    nothing because the consumer already computes it:

      [inf_decode] sends an entry to [inf_fetch2] — never to [set_offset] —
      exactly when [Z.land (c_op h) 240 = 0] ([sub_dist], Inflate.v:1027).

    So the entry that reaches [set_offset] satisfies BOTH [op & 240 <> 0] and
    [op & 64 = 0], and the statement below carries both as antecedents
    ([LeafPosE]).  With the [240] clause the property is TRUE TOTALLY — over
    every index, with no region bound at all — because every entry the
    unwritten region could hold, every pointer, and every invalid marker fails
    one of the two antecedents.  The residue is a single premise on the caller's
    table [t0], which is where the C's unzeroed [ZALLOC] genuinely lives.

    ONE FACT HERE IS LOAD-BEARING FOR THE CONSUMER, NOT JUST FOR THIS PROOF.
    "A sub-table pointer has [op <= 15]" is what makes [sub_dist] classify
    pointers as pointers.  If [it_subsz] could return 16 or more, the decoder
    would read a pointer as a leaf and use a TABLE OFFSET as a distance.  So the
    bound is proved here from [it_subsz]'s own recursion ([it_subsz_le]) rather
    than assumed.

    Relation to [gd/GtDistOffset.v] (delivered earlier today): that file proves
    the IN-RANGE guarded form ([0 <= k < 32]) plus the refutation of the
    unguarded one.  This file needs the ALL-[k] form, because the work symbol's
    range is not available at this layer — and does not need it, since an
    out-of-range [dext] is 0 and the [240] clause excludes it.  Different
    statement, not a copy; the two scratch trees also sit at different logical
    roots, so neither can import the other.

    GTBL-ARMS, 2026-08-18.  Scratch; not landed. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel
  Require Import Base Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import ItGTblRev ItGTblGeom ItGTblSortWin ItGTblCover ItGTblRepl.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Open Scope Z_scope.

(* ######################################################################### *)
(* 1.  The property, and the three entry kinds the antecedents exclude        *)
(* ######################################################################### *)

(** The consumer's own two tests, as antecedents: [240] is [sub_dist]'s (the
    entry is a LEAF, not a sub-table pointer) and [64] is the invalid-code
    rejection [inf_DIST] applies before [set_offset]. *)
Definition LeafPosE (e : Code) : Prop :=
  Z.land (c_op e) 240 <> 0 -> Z.land (c_op e) 64 = 0 -> 1 <= c_val e.

Definition LeafPosT (t : ztbl) : Prop := forall i, LeafPosE (t i).

(* ---- HYPOTHESIS-POSITION CONSTANTS, pinned rather than disclosed ----------
   rt-scout's rule (hours old, from a lane whose premise carried a hand-converted
   constant wrong by 512 while every gate stayed green): every constant in
   hypothesis position needs either an in-tree consumer that DERIVES it or an
   explicit declaration that it is unchecked.  The two that appear in this
   chain's premises are pinned here by computation against the tree's own
   definitions, so neither is a stored value.

   [15] is the model's [MAXBITS] and appears in every width premise
   ([1 <= root0 <= 15], [2 ^ 15]); [32] is the length of the distance arrays and
   bounds the reflection in §2.  The other statement-position literals are 0, 1,
   2, 3 (structural) and 256, which is [u8]'s modulus and is satisfied with slack
   from [x_root c <= 15] — an error THERE could only make the premise harder to
   discharge, never make a false statement provable, which is the one direction
   that needs no pin. *)
Example maxbits_is_15 : MAXBITS = 15.
Proof. reflexivity. Qed.

Example dext_l_length_is_32 : length dext_l = 32%nat.
Proof. reflexivity. Qed.

Example dbase_l_length_is_32 : length dbase_l = 32%nat.
Proof. reflexivity. Qed.

(** Finite ranges by reflection, in ONE lemma used at two widths.  Deliberately
    NOT "[assert (x = 0 \/ ... \/ x = 15) by lia]": a 16- or 32-way disjunction is
    the registered [lia] blowup shape (the search branches per disjunct), and the
    membership route below is linear.  This file also cannot use
    [CbEmit.forallb_zseq'] — that spec file is not in this lane's [-Q] tree, and
    copying it in would be a versionless duplicate. *)
Lemma forallb_range : forall (f : Z -> bool) (n : nat),
  forallb f (map Z.of_nat (seq 0 n)) = true ->
  forall k, 0 <= k < Z.of_nat n -> f k = true.
Proof.
  intros f n Hf k Hk. rewrite forallb_forall in Hf. apply Hf.
  apply in_map_iff. exists (Z.to_nat k). split; [lia|]. apply in_seq. lia.
Qed.

(** Small [op]s carry no bit in [0xF0]. *)
Definition land240_b (x : Z) : bool := Z.eqb (Z.land x 240) 0.

Lemma land240_b_all : forallb land240_b (map Z.of_nat (seq 0 16)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma land_small_240 : forall x, 0 <= x <= 15 -> Z.land x 240 = 0.
Proof.
  intros x Hx. apply Z.eqb_eq.
  exact (forallb_range land240_b 16%nat land240_b_all x ltac:(cbn; lia)).
Qed.

(** A SUB-TABLE POINTER is excluded, and this is the fact the decoder's
    classification depends on. *)
Lemma leafpos_ptr : forall op b v, 0 <= op <= 15 -> LeafPosE (mkCodeT op b v).
Proof.
  intros op b v Hop Hne _. exfalso. apply Hne.
  unfold mkCodeT. cbn [c_op]. rewrite u8_id by lia.
  apply land_small_240. exact Hop.
Qed.

(** A LITERAL/LENGTH entry from the [work]-symbol arm has [op = 0]: excluded by
    the same clause, which is also why the unwritten region is harmless. *)
Lemma leafpos_op_zero : forall b v, LeafPosE (mkCodeT 0 b v).
Proof. intros b v. apply leafpos_ptr. lia. Qed.

(** An INVALID-CODE marker carries bit 64, so it fails the second antecedent. *)
Lemma leafpos_marker : forall op b v, Z.land (u8 op) 64 <> 0 -> LeafPosE (mkCodeT op b v).
Proof.
  intros op b v H _ Hg. exfalso. apply H.
  unfold mkCodeT in Hg. cbn [c_op] in Hg. exact Hg.
Qed.

(* ######################################################################### *)
(* 2.  The distance arrays, at EVERY index                                    *)
(* ######################################################################### *)

(** In range, by reflection over the 32 rows.  The predicate is the guarded
    property itself, so one [vm_compute] settles both the [dext = 64] rows and
    the [u16] fit that a base at or above 65536 would break. *)
Definition dist_leaf_b (k : Z) : bool :=
  Z.eqb (Z.land (u8 (dext k)) 240) 0
  || negb (Z.eqb (Z.land (u8 (dext k)) 64) 0)
  || Z.leb 1 (u16 (dbase k)).

Lemma dist_leaf_b_all : forallb dist_leaf_b (map Z.of_nat (seq 0 32)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dist_leaf_in_range : forall k, 0 <= k < 32 -> dist_leaf_b k = true.
Proof.
  intros k Hk.
  exact (forallb_range dist_leaf_b 32%nat dist_leaf_b_all k ltac:(cbn; lia)).
Qed.

(** Above the table, [zlist] reads its default 0 — and [op = 0] is excluded. *)
Lemma dext_above : forall k, 32 <= k -> dext k = 0.
Proof.
  intros k Hk. unfold dext, zlist. apply nth_overflow.
  change (length dext_l) with 32%nat. lia.
Qed.

(** Below it, [Z.to_nat] clamps to 0, so a negative index aliases index 0 —
    [dext = 16], [dbase = 1] — and the property holds there rather than being
    excluded.  Worth stating explicitly: the natural guess ("out of range reads
    0") is HALF right, and the half that is wrong is the half that would make a
    proof by "excluded everywhere outside" fail. *)
Lemma dext_below : forall k, k <= 0 -> dext k = dext 0.
Proof.
  intros k Hk. unfold dext, zlist.
  assert (H : Z.to_nat k = Z.to_nat 0) by lia.
  rewrite H. reflexivity.
Qed.

Lemma dbase_below : forall k, k <= 0 -> dbase k = dbase 0.
Proof.
  intros k Hk. unfold dbase, zlist.
  assert (H : Z.to_nat k = Z.to_nat 0) by lia.
  rewrite H. reflexivity.
Qed.

(** THE ARITHMETIC, TOTAL IN [k]. *)
Theorem leafpos_dist_entry : forall k b, LeafPosE (mkCodeT (dext k) b (dbase k)).
Proof.
  intros k b.
  destruct (Z_lt_le_dec k 0) as [Hneg | Hnn].
  - rewrite (dext_below k ltac:(lia)), (dbase_below k ltac:(lia)).
    intros _ _.
    (* Reduce the ARGUMENT, never the comparison.  [vm_compute] on [1 <= 1]
       unfolds [Z.le] to its raw [Eq = Gt -> False] and [lia] then reports
       "Cannot find witness" — the trap ItGTblCover's own witness section
       documents, hit here by me, in the next file along. *)
    assert (Hv : c_val (mkCodeT (dext 0) b (dbase 0)) = 1)
      by (vm_compute; reflexivity).
    rewrite Hv. lia.
  - destruct (Z_lt_le_dec k 32) as [Hlt | Hge].
    + pose proof (dist_leaf_in_range k ltac:(lia)) as Hb.
      unfold dist_leaf_b in Hb.
      intros H240 H64. unfold mkCodeT in *. cbn [c_op c_val] in *.
      apply orb_true_iff in Hb. destruct Hb as [Hb | Hv].
      * apply orb_true_iff in Hb. destruct Hb as [H0 | Hm].
        -- exfalso. apply H240. apply Z.eqb_eq. exact H0.
        -- exfalso. apply negb_true_iff, Z.eqb_neq in Hm. exact (Hm H64).
      * apply Z.leb_le. exact Hv.
    + rewrite (dext_above k Hge). apply leafpos_op_zero.
Qed.

(** And [it_here] at a DISTS context: three arms, each excluded or covered. *)
Theorem leafpos_here_dists : forall c st,
  x_match c = 0 -> x_base c = dbase -> x_extra c = dext ->
  LeafPosE (it_here c st).
Proof.
  intros c st Hm Hb He. unfold it_here. cbv zeta.
  destruct (Z.ltb (x_work c (s_sym st) + 1) (x_match c)).
  - apply leafpos_op_zero.
  - destruct (Z.leb (x_match c) (x_work c (s_sym st))).
    + rewrite He, Hb, Hm, Z.sub_0_r. apply leafpos_dist_entry.
    + apply leafpos_marker. vm_compute. discriminate.
Qed.

(* ######################################################################### *)
(* 3.  Sub-table widths are at most 15 — from [it_subsz]'s own recursion       *)
(* ######################################################################### *)

Lemma it_subsz_ge : forall n cnt drop mx curr left,
  curr <= it_subsz n cnt drop mx curr left.
Proof.
  induction n as [|k IH]; intros cnt drop mx curr left;
    cbn [it_subsz]; cbv zeta; [lia|].
  destruct (Z.ltb (curr + drop) mx); [|lia].
  destruct (Z.leb (left - cnt (curr + drop)) 0); [lia|].
  pose proof (IH cnt drop mx (curr + 1) ((left - cnt (curr + drop)) * 2)). lia.
Qed.

Lemma it_subsz_le : forall n cnt drop mx curr left,
  it_subsz n cnt drop mx curr left <= Z.max curr (mx - drop).
Proof.
  induction n as [|k IH]; intros cnt drop mx curr left;
    cbn [it_subsz]; cbv zeta; [lia|].
  destruct (Z.ltb (curr + drop) mx) eqn:Hg; [|lia].
  apply Z.ltb_lt in Hg.
  destruct (Z.leb (left - cnt (curr + drop)) 0); [lia|].
  pose proof (IH cnt drop mx (curr + 1) ((left - cnt (curr + drop)) * 2)). lia.
Qed.

(* ######################################################################### *)
(* 4.  Preservation through the writes                                        *)
(* ######################################################################### *)

Lemma leafpos_tset : forall t i e,
  LeafPosT t -> LeafPosE e -> LeafPosT (tset t i e).
Proof.
  intros t i e Ht He j. unfold tset.
  destruct (Z.eqb j i); [exact He | exact (Ht j)].
Qed.

Lemma leafpos_fill : forall n t bi incr h,
  LeafPosT t -> LeafPosE h -> LeafPosT (it_fill n t bi incr h).
Proof.
  induction n as [|m IH]; intros t bi incr h Ht Hh; cbn [it_fill].
  - exact Ht.
  - apply IH; [apply leafpos_tset; [exact Ht | exact Hh] | exact Hh].
Qed.

(** The step's table, read through the match-valued predicate discipline (never
    [injection]: the [ItCont] records carry [it_subsz] at literal fuel).  The
    right disjunct exposes the pointer's WIDTH with its bounds, because those
    bounds are provable here — where [curr'] is a concrete term — and not later,
    where it is an opaque variable. *)
Definition PtrShape (c : ItCtx) (st : ItSt) (r : ItStep) : Prop :=
  match r with
  | ItCont s =>
      s_tbl s = it_fill (Z.to_nat (Z.shiftl 1 (s_curr st) / Z.shiftl 1 (s_len st - s_drop st)))
                  (s_tbl st) (s_next st + Z.shiftr (s_huff st) (s_drop st))
                  (Z.shiftl 1 (s_len st - s_drop st)) (it_here c st)
      \/ (exists cv nx,
            s_tbl s = tset (it_fill (Z.to_nat (Z.shiftl 1 (s_curr st) / Z.shiftl 1 (s_len st - s_drop st)))
                              (s_tbl st) (s_next st + Z.shiftr (s_huff st) (s_drop st))
                              (Z.shiftl 1 (s_len st - s_drop st)) (it_here c st))
                        (s_low s) (mkCodeT cv (x_root c) nx)
            /\ 1 <= cv <= Z.max (s_len s - s_drop s) (x_max c - s_drop s))
  | ItBreak s =>
      s_tbl s = it_fill (Z.to_nat (Z.shiftl 1 (s_curr st) / Z.shiftl 1 (s_len st - s_drop st)))
                  (s_tbl st) (s_next st + Z.shiftr (s_huff st) (s_drop st))
                  (Z.shiftl 1 (s_len st - s_drop st)) (it_here c st)
  | ItOverflow t =>
      t = it_fill (Z.to_nat (Z.shiftl 1 (s_curr st) / Z.shiftl 1 (s_len st - s_drop st)))
            (s_tbl st) (s_next st + Z.shiftr (s_huff st) (s_drop st))
            (Z.shiftl 1 (s_len st - s_drop st)) (it_here c st)
  end.

Lemma ptr_shape : forall c st,
  0 <= s_drop st <= x_root c -> PtrShape c st (it_step c st).
Proof.
  intros c st Hd. unfold PtrShape, it_step. cbv zeta.
  match goal with |- context [if ?b then _ else _] => destruct b eqn:Hbrk end.
  - cbn [s_tbl]. reflexivity.
  - match goal with |- context [if ?b then _ else _] => destruct b eqn:Hsub end.
    + match goal with |- context [if ?b then _ else _] => destruct b eqn:Hen end.
      * reflexivity.
      * right. cbn [s_tbl s_low s_len s_drop].
        (* witness taken FROM the goal: an [eexists] would reach the bound goal
           with the width still an open metavariable *)
        match goal with
        | |- exists cv nx, tset _ _ (mkCodeT ?CV _ ?NX) = _ /\ _ =>
            exists CV; exists NX
        end.
        split; [reflexivity|].
        assert (Hlt : x_root c
                      < (if Z.eqb (zset (s_count st) (s_len st) (s_count st (s_len st) - 1)
                                     (s_len st)) 0
                         then x_lens c (x_work c (s_sym st + 1)) else s_len st)).
        { apply Z.ltb_lt. destruct (andb_prop _ _ Hsub) as [Hl _]. exact Hl. }
        split.
        -- (* the width is at least the initial [len - drop], which is positive *)
           pose proof (it_subsz_ge 16%nat
             (zset (s_count st) (s_len st) (s_count st (s_len st) - 1))
             (if Z.eqb (s_drop st) 0 then x_root c else s_drop st)
             (x_max c)
             ((if Z.eqb (zset (s_count st) (s_len st) (s_count st (s_len st) - 1)
                           (s_len st)) 0
               then x_lens c (x_work c (s_sym st + 1)) else s_len st)
              - (if Z.eqb (s_drop st) 0 then x_root c else s_drop st))
             (Z.shiftl 1 ((if Z.eqb (zset (s_count st) (s_len st)
                                       (s_count st (s_len st) - 1) (s_len st)) 0
                           then x_lens c (x_work c (s_sym st + 1)) else s_len st)
                          - (if Z.eqb (s_drop st) 0 then x_root c else s_drop st))))
             as Hge.
           destruct (Z.eqb (s_drop st) 0); lia.
        -- apply it_subsz_le.
    + cbn [s_tbl]. left. reflexivity.
Qed.

(** One trip preserves the property.  The pointer's [op <= 15] comes from the
    shape lemma's bound plus the invariant's width facts: in the sub-table phase
    [drop = root >= 1] and [len <= 15], so the width is at most 14. *)
Lemma leafpos_step_cont : forall c cnt0 st st',
  CovCtxOk c cnt0 -> CovInv c cnt0 st -> CovInv c cnt0 st' ->
  x_match c = 0 -> x_base c = dbase -> x_extra c = dext ->
  LeafPosT (s_tbl st) -> it_step c st = ItCont st' -> LeafPosT (s_tbl st').
Proof.
  intros c cnt0 st st' Hctx Hinv Hinv' Hm Hb He Ht Hstep.
  pose proof Hctx as Hctx2.
  destruct Hctx as (Hroot & _ & Hmx & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof Hinv as Hinv2.
  destruct Hinv as (Hlen & _ & _ & _ & _ & _ & _ & Hphase).
  assert (Hdrop : 0 <= s_drop st <= x_root c)
    by (destruct Hphase as [(Hd & _) | (Hd & _)]; lia).
  assert (Hfill : LeafPosT (it_fill
      (Z.to_nat (Z.shiftl 1 (s_curr st) / Z.shiftl 1 (s_len st - s_drop st)))
      (s_tbl st) (s_next st + Z.shiftr (s_huff st) (s_drop st))
      (Z.shiftl 1 (s_len st - s_drop st)) (it_here c st)))
    by (apply leafpos_fill; [exact Ht | exact (leafpos_here_dists c st Hm Hb He)]).
  pose proof (ptr_shape c st Hdrop) as Hsh. rewrite Hstep in Hsh.
  cbn [PtrShape] in Hsh.
  destruct Hsh as [Htbl | (cv & nx & Htbl & Hcv)].
  - rewrite Htbl. exact Hfill.
  - rewrite Htbl. apply leafpos_tset; [exact Hfill|].
    apply leafpos_ptr.
    destruct Hinv' as (Hlen' & _ & _ & _ & _ & _ & _ & Hphase').
    destruct Hphase' as [(Hd' & _) | (Hd' & Hrl' & _)]; lia.
Qed.

Lemma leafpos_step_break : forall c cnt0 st st1,
  CovInv c cnt0 st -> CovCtxOk c cnt0 ->
  x_match c = 0 -> x_base c = dbase -> x_extra c = dext ->
  LeafPosT (s_tbl st) -> it_step c st = ItBreak st1 -> LeafPosT (s_tbl st1).
Proof.
  intros c cnt0 st st1 Hinv Hctx Hm Hb He Ht Hstep.
  destruct Hctx as (Hroot & _).
  destruct Hinv as (Hlen & _ & _ & _ & _ & _ & _ & Hphase).
  assert (Hdrop : 0 <= s_drop st <= x_root c)
    by (destruct Hphase as [(Hd & _) | (Hd & _)]; lia).
  pose proof (ptr_shape c st Hdrop) as Hsh. rewrite Hstep in Hsh.
  cbn [PtrShape] in Hsh. rewrite Hsh.
  apply leafpos_fill; [exact Ht | exact (leafpos_here_dists c st Hm Hb He)].
Qed.

Lemma leafpos_step_over : forall c cnt0 st t,
  CovInv c cnt0 st -> CovCtxOk c cnt0 ->
  x_match c = 0 -> x_base c = dbase -> x_extra c = dext ->
  LeafPosT (s_tbl st) -> it_step c st = ItOverflow t -> LeafPosT t.
Proof.
  intros c cnt0 st t Hinv Hctx Hm Hb He Ht Hstep.
  destruct Hctx as (Hroot & _).
  destruct Hinv as (Hlen & _ & _ & _ & _ & _ & _ & Hphase).
  assert (Hdrop : 0 <= s_drop st <= x_root c)
    by (destruct Hphase as [(Hd & _) | (Hd & _)]; lia).
  pose proof (ptr_shape c st Hdrop) as Hsh. rewrite Hstep in Hsh.
  cbn [PtrShape] in Hsh. rewrite Hsh.
  apply leafpos_fill; [exact Ht | exact (leafpos_here_dists c st Hm Hb He)].
Qed.

(** The loop, threading [CovInv] exactly as the coverage and replication loops
    do — the invariant is needed here only for the width facts. *)
Lemma leafpos_loop : forall n c cnt0 st r,
  CovCtxOk c cnt0 -> CovInv c cnt0 st ->
  x_match c = 0 -> x_base c = dbase -> x_extra c = dext ->
  LeafPosT (s_tbl st) -> it_loop n c st = Some r -> LeafPosT (step_tbl r).
Proof.
  induction n as [|k IH]; intros c cnt0 st r Hctx Hinv Hm Hb He Ht Hloop;
    cbn [it_loop] in Hloop; [discriminate Hloop|].
  destruct (it_step c st) as [st'|st1|t] eqn:Hs.
  - apply (IH c cnt0 st' r Hctx (cov_step_cont c cnt0 st st' Hctx Hinv Hs)
            Hm Hb He
            (leafpos_step_cont c cnt0 st st' Hctx Hinv
               (cov_step_cont c cnt0 st st' Hctx Hinv Hs) Hm Hb He Ht Hs)
            Hloop).
  - injection Hloop as <-. cbn [step_tbl].
    exact (leafpos_step_break c cnt0 st st1 Hinv Hctx Hm Hb He Ht Hs).
  - injection Hloop as <-. cbn [step_tbl].
    exact (leafpos_step_over c cnt0 st t Hinv Hctx Hm Hb He Ht Hs).
Qed.

(** The incomplete-code fix-up writes an invalid marker, which fails the second
    antecedent. *)
Lemma leafpos_finish : forall st, LeafPosT (s_tbl st) -> LeafPosT (it_finish st).
Proof.
  intros st Ht. unfold it_finish.
  destruct (Z.eqb (s_huff st) 0); [exact Ht|].
  apply leafpos_tset; [exact Ht|].
  apply leafpos_marker. vm_compute. discriminate.
Qed.

(* ######################################################################### *)
(* 5.  The DISTS context, and the theorem                                     *)
(* ######################################################################### *)

(** [it_pre]'s three [ty]-dependent fields at a DISTS call.  Same peel as
    [ItGTblRepl.it_pre_go_tbl]: branch booleans destructed without reducing
    them, the constructor inverted by a lemma proved ON VARIABLES. *)
Lemma it_pre_go_dists : forall lens codes root0 t0 c st,
  it_pre CT_DISTS lens codes root0 t0 = PreGo c st ->
  x_match c = 0 /\ x_base c = dbase /\ x_extra c = dext.
Proof.
  intros lens codes root0 t0 c st H.
  unfold it_pre in H. cbv zeta in H.
  destruct (Z.eqb (it_findmax 15%nat MAXBITS (it_count (Z.to_nat codes) 0 lens zzero)) 0);
    [discriminate H|].
  destruct (it_kraft 15%nat 1 1 (it_count (Z.to_nat codes) 0 lens zzero)) as [lft|];
    [|discriminate H].
  destruct (it_incomplete CT_DISTS lft _); [discriminate H|].
  destruct (it_enough CT_DISTS _); [discriminate H|].
  injection H as Hc _. rewrite <- Hc. cbn [x_match x_base x_extra].
  vm_compute (Z.eqb CT_DISTS CT_LENS). vm_compute (Z.eqb CT_DISTS CT_DISTS).
  split; [reflexivity|]. split; reflexivity.
Qed.

(** THE DELIVERABLE.  One premise, on the caller's table, and it is exactly the
    C's unzeroed [ZALLOC] — the honest residue, not a convenience. *)
Theorem it_model_leafpos : forall lens codes root0 t0 out,
  0 <= codes ->
  (forall i, 0 <= i < codes -> 0 <= lens i <= 15) ->
  1 <= root0 <= 15 ->
  LeafPosT t0 ->
  it_model CT_DISTS lens codes root0 t0 = Some out ->
  LeafPosT (o_tbl out).
Proof.
  intros lens codes root0 t0 out Hcodes Hlens Hroot0 Ht0 Hmodel.
  unfold it_model in Hmodel.
  destruct (it_pre CT_DISTS lens codes root0 t0) as [ | temp | | c st] eqn:Hpre.
  - injection Hmodel as <-. cbn [o_tbl]. exact Ht0.
  - rewrite (it_pre_empty_shape CT_DISTS lens codes root0 t0 temp Hpre) in Hmodel.
    injection Hmodel as <-. cbn [o_tbl].
    apply leafpos_tset; [apply leafpos_tset; [exact Ht0|]|];
      apply leafpos_marker; vm_compute; discriminate.
  - injection Hmodel as <-. cbn [o_tbl]. exact Ht0.
  - destruct (cov_pre CT_DISTS lens codes root0 t0 c st Hcodes Hlens Hroot0 Hpre)
      as [Hctx Hinv].
    destruct (it_pre_go_dists lens codes root0 t0 c st Hpre) as (Hm & Hb & He).
    assert (Htbl : LeafPosT (s_tbl st))
      by (rewrite (it_pre_go_tbl CT_DISTS lens codes root0 t0 c st Hpre); exact Ht0).
    destruct (it_loop (S (Z.to_nat codes)) c st) as [[st'|st'|tt]|] eqn:Hloop;
      try discriminate Hmodel; injection Hmodel as <-; cbn [o_tbl].
    + apply leafpos_finish.
      exact (leafpos_loop (S (Z.to_nat codes)) c (sw_cnt lens codes) st
               (ItBreak st') Hctx Hinv Hm Hb He Htbl Hloop).
    + exact (leafpos_loop (S (Z.to_nat codes)) c (sw_cnt lens codes) st
               (ItOverflow tt) Hctx Hinv Hm Hb He Htbl Hloop).
Qed.

(** And the form the call site consumes: standing behind BOTH tests the decoder
    already performs, the value it hands to [set_offset] is positive. *)
Corollary it_model_dist_offset_pos : forall lens codes root0 t0 out i,
  0 <= codes ->
  (forall j, 0 <= j < codes -> 0 <= lens j <= 15) ->
  1 <= root0 <= 15 ->
  LeafPosT t0 ->
  it_model CT_DISTS lens codes root0 t0 = Some out ->
  Z.land (c_op (o_tbl out i)) 240 <> 0 ->
  Z.land (c_op (o_tbl out i)) 64 = 0 ->
  1 <= c_val (o_tbl out i).
Proof.
  intros lens codes root0 t0 out i Hcodes Hlens Hroot0 Ht0 Hmodel H240 H64.
  exact (it_model_leafpos lens codes root0 t0 out Hcodes Hlens Hroot0 Ht0 Hmodel
           i H240 H64).
Qed.

(* ######################################################################### *)
(* 6.  THE PREMISE IS SATISFIABLE, THE CONCLUSION IS NOT VACUOUS, AND THE      *)
(*     GUARD CLAUSE IS NECESSARY                                              *)
(* ######################################################################### *)

(** The premise holds of the table the [makefixed] call sites pass, so it is not
    an unsatisfiable shape. *)
Lemma leafpos_tnone : LeafPosT tnone.
Proof.
  intros i Hne _. exfalso. apply Hne.
  (* [mkCode] is a CONSTRUCTOR, not a definition: [unfold] on it fails with
     "cannot coerce to an evaluable reference".  Project instead. *)
  unfold tnone. cbn [c_op]. reflexivity.
Qed.

Definition lens_dist_122 : zarr := zlist [1;2;2].

(** A real accepted DISTS call where BOTH antecedents HOLD — so the conclusion is
    doing work rather than being excluded.  Measured (probe/LeafWitProbe.v): all
    four root entries have [op = 16], hence [op & 240 = 16 <> 0] and
    [op & 64 = 0], with values [1;2;1;3].  The positivity below is taken FROM the
    theorem, not from that dump. *)
Example it_model_leafpos_instantiated :
  exists out,
    it_model CT_DISTS lens_dist_122 3 2 tnone = Some out
    /\ Z.land (c_op (o_tbl out 0)) 240 <> 0
    /\ Z.land (c_op (o_tbl out 0)) 64 = 0
    /\ 1 <= c_val (o_tbl out 0).
Proof.
  assert (H3 : 0 <= 3) by lia.
  assert (Hr2 : 1 <= 2 <= 15) by lia.
  assert (Hlens : forall i, 0 <= i < 3 -> 0 <= lens_dist_122 i <= 15).
  { intros i Hi. assert (Hd : i = 0 \/ i = 1 \/ i = 2) by lia.
    destruct Hd as [H0 | [H1 | H2]].
    - rewrite H0. assert (E : lens_dist_122 0 = 1) by reflexivity. rewrite E. lia.
    - rewrite H1. assert (E : lens_dist_122 1 = 2) by reflexivity. rewrite E. lia.
    - rewrite H2. assert (E : lens_dist_122 2 = 2) by reflexivity. rewrite E. lia. }
  destruct (it_model CT_DISTS lens_dist_122 3 2 tnone) as [out|] eqn:E;
    [|vm_compute in E; discriminate].
  exists out. split; [reflexivity|].
  assert (Hop : c_op (o_tbl out 0) = 16)
    by (vm_compute in E; injection E as E'; rewrite <- E'; vm_compute; reflexivity).
  assert (H240 : Z.land (c_op (o_tbl out 0)) 240 <> 0)
    by (rewrite Hop; vm_compute; discriminate).
  assert (H64 : Z.land (c_op (o_tbl out 0)) 64 = 0)
    by (rewrite Hop; vm_compute; reflexivity).
  split; [exact H240|]. split; [exact H64|].
  exact (it_model_dist_offset_pos lens_dist_122 3 2 tnone out 0
           H3 Hlens Hr2 leafpos_tnone E H240 H64).
Qed.

(** AND THE [240] CLAUSE IS NOT DECORATION.  Drop it and the statement is false
    of a real accepted call — at any index the call never wrote, where the entry's
    [op] is 0, [op & 64 = 0] holds and [c_val] is 0.  Kept as a Qed'd refutation
    for the same reason [GtDistOffset]'s is: a premise that looks removable is
    exactly the one a later reader removes.  (This is also the general form of
    huffman-id's default-entry trap: their index bound and this clause exclude the
    same entries, and the clause is the one the CONSUMER already computes.) *)
Theorem leaf240_clause_necessary :
  ~ (forall lens codes root0 t0 out,
        LeafPosT t0 ->
        it_model CT_DISTS lens codes root0 t0 = Some out ->
        forall i, Z.land (c_op (o_tbl out i)) 64 = 0 -> 1 <= c_val (o_tbl out i)).
Proof.
  intro H.
  destruct (it_model CT_DISTS lens_dist_122 3 2 tnone) as [out|] eqn:E;
    [|vm_compute in E; discriminate].
  assert (Hop : Z.land (c_op (o_tbl out 100)) 64 = 0)
    by (vm_compute in E; injection E as E'; rewrite <- E'; vm_compute; reflexivity).
  pose proof (H lens_dist_122 3 2 tnone out leafpos_tnone E 100 Hop) as Hpos.
  assert (Hval : c_val (o_tbl out 100) = 0)
    by (vm_compute in E; injection E as E'; rewrite <- E'; vm_compute; reflexivity).
  rewrite Hval in Hpos. lia.
Qed.

Print Assumptions maxbits_is_15.
Print Assumptions dext_l_length_is_32.
Print Assumptions dbase_l_length_is_32.
Print Assumptions forallb_range.
Print Assumptions land240_b_all.
Print Assumptions land_small_240.
Print Assumptions leafpos_ptr.
Print Assumptions leafpos_op_zero.
Print Assumptions leafpos_marker.
Print Assumptions dist_leaf_b_all.
Print Assumptions dist_leaf_in_range.
Print Assumptions dext_above.
Print Assumptions dext_below.
Print Assumptions dbase_below.
Print Assumptions leafpos_dist_entry.
Print Assumptions leafpos_here_dists.
Print Assumptions it_subsz_ge.
Print Assumptions it_subsz_le.
Print Assumptions leafpos_tset.
Print Assumptions leafpos_fill.
Print Assumptions ptr_shape.
Print Assumptions leafpos_step_cont.
Print Assumptions leafpos_step_break.
Print Assumptions leafpos_step_over.
Print Assumptions leafpos_loop.
Print Assumptions leafpos_finish.
Print Assumptions it_pre_go_dists.
Print Assumptions it_model_leafpos.
Print Assumptions it_model_dist_offset_pos.
Print Assumptions leafpos_tnone.
Print Assumptions it_model_leafpos_instantiated.
Print Assumptions leaf240_clause_necessary.
