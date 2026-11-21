(** * OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.GtAdlerLoop — §4 at its CALL SITE: the loop invariant clause the encoder
      lane has to carry, and nothing more

    [GtAdlerChunk] proves the composition law and the multi-chunk fold as facts
    about [Checksum.adler32_z].  Those are general; they say nothing about where
    the encoder actually applies the function.  This file closes that last gap and
    hands the deflate-loop lane a DROP-IN: one conjunct to thread, one step lemma
    that preserves it, and one exit lemma that yields [TrailerMatchesPayload]'s
    equation directly.

    WHY A SEPARATE FILE RATHER THAN A SECTION IN [GtAdlerChunk].  That file is
    DECLARED to rt-scout for a landing slot with digest
    [] and must stay quiescent — a published digest
    plus continued editing is exactly how I landed on a stale token once already.
    The cost is that this file is NOT root-agnostic: it carries one
    [From Gw Require Import GtAdlerChunk] that must be rewritten to the
    destination root at landing.  [probe/landform_s4.sh] ASSERTS root-agnosticism
    and would abort on this file; the rewrite path in [probe/landform_spec.sh] is
    the one that applies to it.  Stated here because a landing script that is
    valid for one file and invalid for another, with no note saying which, is how
    a wrong instrument gets run.

    WHAT THE CALL SITE ADDS, and it is not zero: [read_buf] ([Deflate.v:278-290])
    has an EARLY RETURN.  When the available length is 0 it returns the stream
    UNCHANGED — so [zs_adler] keeps its old value, while the general law would
    have it become [adler32_z a false []].  Those agree only because [AdVal a]
    makes [adler32_z a false [] = a] ([ad_closed_nil]).  **The empty-chunk branch
    is where the fold invariant earns its second conjunct**: with [AdWf] alone the
    two sides differ, since [AdWf] is blind to bits at or above 32.

    GTBL-ARMS, 2026-08-19.  Scratch; not landed; read-only against the graded
    tree. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Checksum Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtAdlerChunk.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ######################################################################### *)
(* 1.  Setter projections, which nothing in the tree had                      *)
(* ######################################################################### *)

(** [setZ_*] are plain [mkZStrm] reconstructions, so each projection is a
    [reflexivity].  Proved SEPARATELY and applied one at a time rather than by
    [rewrite !] over the four-deep setter stack in [read_buf]: a repeated rewrite
    across a self-similar setter tower is a registered OOM shape here, and two
    named rewrites cost nothing. *)
Lemma zs_adler_setZ_adler : forall v s, zs_adler (setZ_adler v s) = v.
Proof. reflexivity. Qed.

Lemma zs_adler_setZ_totalin : forall v s, zs_adler (setZ_totalin v s) = zs_adler s.
Proof. reflexivity. Qed.

Lemma zs_adler_setZ_done : forall v s, zs_adler (setZ_done v s) = zs_adler s.
Proof. reflexivity. Qed.

Lemma zs_adler_setZ_in : forall v s, zs_adler (setZ_in v s) = zs_adler s.
Proof. reflexivity. Qed.

(** and the [zs_done] side, which the history-free clause of section 4 reads.
    Nothing in the tree had either family. *)
Lemma zs_done_setZ_done : forall v s, zs_done (setZ_done v s) = v.
Proof. reflexivity. Qed.

Lemma zs_done_setZ_adler : forall v s, zs_done (setZ_adler v s) = zs_done s.
Proof. reflexivity. Qed.

Lemma zs_done_setZ_totalin : forall v s, zs_done (setZ_totalin v s) = zs_done s.
Proof. reflexivity. Qed.

(* ######################################################################### *)
(* 2.  The step at the call site                                              *)
(* ######################################################################### *)

(** [wrap = 1] is the zlib wrapper, which is the one PNG uses; at [wrap = 2] the
    same field carries a CRC and the adler law does not apply to it at all.  So
    the constant is a real precondition and is written into the statement rather
    than left general. *)
Theorem read_buf_adler_step : forall size st,
  AdVal (zs_adler st) ->
  zs_adler (snd (read_buf 1 size st))
  = adler32_z (zs_adler st) false (fst (read_buf 1 size st)).
Proof.
  intros size st Hav.
  assert (Hnil : ad_wf false (@nil Z))
    by (split; [intros b Hb; cbn in Hb; destruct Hb|discriminate]).
  unfold read_buf. cbv zeta.
  destruct (Z.eqb (if Z.ltb size (zlen (zs_in st)) then size else zlen (zs_in st)) 0)
    eqn:E0; cbn [fst snd].
  - (* THE EARLY RETURN: the stream is handed back untouched, so the equation is
       [a = adler32_z a false []] and holds only under the invariant. *)
    rewrite (adler32_z_closed_form (zs_adler st) [] (proj1 Hav) Hnil).
    symmetry. apply ad_closed_nil. exact Hav.
  - rewrite zs_adler_setZ_totalin, zs_adler_setZ_adler. reflexivity.
Qed.

Corollary read_buf_preserves_adval : forall size st,
  AdVal (zs_adler st) -> AdVal (zs_adler (snd (read_buf 1 size st))).
Proof.
  intros size st Hav.
  rewrite (read_buf_adler_step size st Hav).
  apply adval_step; [exact Hav|apply read_buf_chunk_ad_wf].
Qed.

(** The early return is not a corner case to be waved at: it is REACHED, on every
    call whose input is exhausted.  Pinned as a computation so the branch is known
    to be live rather than assumed dead. *)
Lemma read_buf_early_return_is_reached : forall st,
  zs_in st = [] -> read_buf 1 16 st = ([], st).
Proof.
  intros st Hin. unfold read_buf. rewrite Hin. reflexivity.
Qed.

(* ######################################################################### *)
(* 3.  THE CLAUSE THE LOOP LANE CARRIES                                       *)
(* ######################################################################### *)

(** Two conjuncts.  The second is the interesting one; the first is what makes it
    survive a step, and [adwf_is_not_enough_for_the_fold] shows it cannot be
    weakened to [AdWf]. *)
Definition AdlerTracksChunks (init : Z) (cs : list (list Z)) (st : ZStrm) : Prop :=
  AdVal (zs_adler st) /\ zs_adler st = ad_chunks init cs.

Lemma ad_chunks_snoc : forall cs a c,
  ad_chunks a (cs ++ [c]) = adler32_z (ad_chunks a cs) false c.
Proof.
  induction cs as [|d r IH]; intros a c; cbn [ad_chunks app]; [reflexivity|apply IH].
Qed.

(** ESTABLISHED at [deflate_reset] ([Deflate.v:1138] sets the field to
    [adler32_z 0 true []]), with no chunks consumed. *)
Lemma adler_tracks_init : forall st,
  zs_adler st = adler32_z 0 true [] -> AdlerTracksChunks (adler32_z 0 true []) [] st.
Proof.
  intros st H. split; [rewrite H; exact adval_init|]. cbn [ad_chunks]. exact H.
Qed.

(** PRESERVED by a [read_buf].  The chunk list grows by the chunk [read_buf]
    itself reports, so the lane never has to describe the chunk — it appears in
    the conclusion, taken from the function. *)
Theorem adler_tracks_step : forall init cs size st,
  AdlerTracksChunks init cs st ->
  AdlerTracksChunks init (cs ++ [fst (read_buf 1 size st)]) (snd (read_buf 1 size st)).
Proof.
  intros init cs size st [Hav Heq]. split.
  - apply read_buf_preserves_adval. exact Hav.
  - rewrite (read_buf_adler_step size st Hav), ad_chunks_snoc, Heq. reflexivity.
Qed.

(** AND CONSUMED at loop exit: the field equals the single call over the whole
    payload, which is [DeclIface.TrailerMatchesPayload]'s equation with
    [X = concat cs].  The lane owes the two conjuncts and nothing about adler. *)
Theorem adler_tracks_exit : forall init cs st,
  AdVal init -> (forall c, In c cs -> ad_wf false c) ->
  AdlerTracksChunks init cs st ->
  zs_adler st = adler32_z init false (concat cs).
Proof.
  intros init cs st Hi Hc [_ Heq]. rewrite Heq.
  apply adler32_z_chunks; assumption.
Qed.

(** At the encoder's own init, so the hypothesis [AdVal init] is discharged rather
    than passed on. *)
Corollary adler_tracks_exit_from_reset : forall cs st,
  (forall c, In c cs -> ad_wf false c) ->
  AdlerTracksChunks (adler32_z 0 true []) cs st ->
  zs_adler st = adler32_z (adler32_z 0 true []) false (concat cs).
Proof.
  intros cs st Hc H. apply adler_tracks_exit; [exact adval_init|exact Hc|exact H].
Qed.

(** THE CHUNK-SIDE HYPOTHESIS IS FREE, which is the point of stating the exit
    lemma over [cs] rather than over an abstract payload: every chunk the lane can
    put in [cs] came out of [read_buf], and [read_buf_chunk_ad_wf] gives [ad_wf]
    for those unconditionally ([map u8] normalises).  So a lane that only ever
    appends [fst (read_buf ...)] discharges [Hc] by construction. *)
Lemma ad_wf_of_read_buf_chunks : forall cs,
  (forall c, In c cs -> exists w size st, c = fst (read_buf w size st)) ->
  (forall c, In c cs -> ad_wf false c).
Proof.
  intros cs H c Hin.
  destruct (H c Hin) as [w [size [st ->]]]. apply read_buf_chunk_ad_wf.
Qed.

(* ######################################################################### *)
(* 4.  THE HISTORY-FREE FORM, which is the one a state-indexed invariant wants *)
(* ######################################################################### *)

(** [AdlerTracksChunks] above carries a chunk LIST, and that is a defect for the
    actual consumer.  ld-seams' [LdLoopInv.v:58-74] is a record of clauses indexed
    by the state alone ([dli_inv], [dli_bytes], [dli_len], ...); a clause needing
    an auxiliary history would force the whole record to gain a parameter.

    IT DOES NOT HAVE TO.  [read_buf] appends its chunk to [zs_done]
    ([Deflate.v:289]), so **the state already carries the concatenation** and the
    clause can be stated on [st] alone.  Then the third conjunct IS
    [DeclIface.TrailerMatchesPayload]'s equation, at [X = zs_done st], with no
    exit lemma required at all — the invariant's own clause is the result.

    I built the list form first because the composition law is stated over [xs ++
    ys] and a list was the obvious generalisation.  Reading the consumer's record
    is what showed the list was unnecessary; the fact is the same one, and the
    difference is entirely in what the consumer has to restructure to use it. *)
Definition AdlerTracksDone (init : Z) (st : ZStrm) : Prop :=
  AdVal (zs_adler st)
  /\ ad_wf false (zs_done st)
  /\ zs_adler st = adler32_z init false (zs_done st).

(** [zs_done] grows by exactly the chunk [read_buf] reports — including on the
    early return, where both sides gain nothing. *)
Lemma read_buf_done_app : forall w size st,
  zs_done (snd (read_buf w size st)) = zs_done st ++ fst (read_buf w size st).
Proof.
  intros w size st. unfold read_buf. cbv zeta.
  destruct (Z.eqb (if Z.ltb size (zlen (zs_in st)) then size else zlen (zs_in st)) 0)
    eqn:E0; cbn [fst snd].
  - symmetry. apply app_nil_r.
  - (* the four-deep setter stack projects by CONVERSION; no rewrite is needed and
       none should be used — [rewrite !] across a self-similar setter tower is the
       registered OOM shape.  My first draft here reached for
       [zs_adler_setZ_totalin] on a [zs_done] goal, and the error named the
       PATTERN it could not find rather than the mistake, which was the field. *)
    reflexivity.
Qed.

Theorem read_buf_tracks_done : forall init size st,
  AdWf init -> AdlerTracksDone init st -> AdlerTracksDone init (snd (read_buf 1 size st)).
Proof.
  intros init size st Hi [Hav [Hdw Heq]].
  split; [apply read_buf_preserves_adval; exact Hav|].
  rewrite read_buf_done_app. split.
  - apply ad_wf_app; [exact Hdw|apply read_buf_chunk_ad_wf].
  - rewrite (read_buf_adler_step size st Hav), Heq.
    apply adler32_z_chunk; [exact Hi|exact Hdw|apply read_buf_chunk_ad_wf].
Qed.

Lemma adler_tracks_done_at_reset : forall st,
  zs_adler st = adler32_z 0 true [] -> zs_done st = [] ->
  AdlerTracksDone (adler32_z 0 true []) st.
Proof.
  intros st Ha Hd.
  assert (Hnil : ad_wf false (@nil Z))
    by (split; [intros b Hb; cbn in Hb; destruct Hb|discriminate]).
  split; [rewrite Ha; exact adval_init|]. split; [rewrite Hd; exact Hnil|].
  rewrite Ha, Hd. symmetry.
  rewrite (adler32_z_closed_form (adler32_z 0 true []) [] adwf_init Hnil).
  apply ad_closed_nil. exact adval_init.
Qed.

(** THE WHOLE OF §4 AT THE CALL SITE, in the shape the clause names: the field
    equals one call over the payload accumulated so far.  No chunk list, no fold,
    no adler reasoning left for the loop lane. *)
Corollary adler_field_is_the_trailer : forall st,
  AdlerTracksDone (adler32_z 0 true []) st ->
  zs_adler st = adler32_z (adler32_z 0 true []) false (zs_done st).
Proof. intros st [_ [_ H]]. exact H. Qed.

Print Assumptions AdlerTracksDone.
Print Assumptions read_buf_done_app.
Print Assumptions read_buf_tracks_done.
Print Assumptions adler_tracks_done_at_reset.
Print Assumptions adler_field_is_the_trailer.
Print Assumptions zs_adler_setZ_adler.
Print Assumptions zs_adler_setZ_totalin.
Print Assumptions zs_adler_setZ_done.
Print Assumptions zs_adler_setZ_in.
Print Assumptions zs_done_setZ_done.
Print Assumptions zs_done_setZ_adler.
Print Assumptions zs_done_setZ_totalin.
Print Assumptions read_buf_adler_step.
Print Assumptions read_buf_preserves_adval.
Print Assumptions read_buf_early_return_is_reached.
Print Assumptions ad_chunks_snoc.
Print Assumptions adler_tracks_init.
Print Assumptions adler_tracks_step.
Print Assumptions adler_tracks_exit.
Print Assumptions adler_tracks_exit_from_reset.
Print Assumptions ad_wf_of_read_buf_chunks.
