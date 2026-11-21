(** * B3B5Stmts — Leg B export STATEMENTS, pre-proof per (viii).

    OWNER: an earlier development run (dyn round Leg B; freeze v7 ; ownership
    vocabulary verbatim from legA-proofs/A1StmtsV3.v ).
    Statements as Definitions; proofs locked until the chairs' passes.

    ONE OPEN DESIGN SLOT, flagged for the (viii) round-trip: the [ent]
    WITNESS FORM in the B3 conclusions.  Proposed here: existential,
    composed from the build's own PreGo context ([it_entry cL] at the
    canonical length), so model-rt's ent-packs apply at the named ctx.
    If Leg A or the keystone side wants [ent] universally-premised
    instead, only the two B3 statement heads change.

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff DeflateSpec Inftrees Inflate InflateThy StepReach
  ItGTblCover ItGSubCover DynTblOkHolds.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Q6TblChain ZReproQ6K ZReproQ6P.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import ItGWidth.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
(* Home re-point (q7 freeze v41, homes follow landing order): the
   ownership vocabulary (zr_width_covers / zr_ptr_children /
   zr_no_short_code / zr_no_long_code_at / zr_two_own_v3) now comes from
   its landed homes ItGClassHead (via ItGWidth's import) + ItGWidth; the
   verbatim locals this file carried since the freeze (A1StmtsV3
   spellings) are DROPPED.  A1StmtsV3 itself lands in the final
   train as a CONSUMER of these homes. *)
Local Open Scope Z_scope.

(* Ownership vocabulary — spellings verbatim from A1StmtsV3 ();
   duplicated here only until the round decides that file's landing home,
   then these four become Requires. *)
(* ==========================================================================
   B3 — the ownership inhabitation at installed tables.
   ========================================================================== *)

(** LEN side: from the handover's own payload — premised at [db_acc]
    (v2 of this head, q6 catch: the dispatch deliberately exports db_acc,
    not db_ok, and amb_ok is UNSUPPLIABLE reach-free at the abstract
    dispatch state since it quantifies cells the build never wrote; the
    geometry machinery underneath is acceptance-only — every landed view
    proof destructs Hamb and discards it, and zr_two_own_v3 is
    window-quantified so the census's whole-array falsity never bites).
    Concluding the frozen ownership Prop at SOME ent composed from the
    build's PreGo context. *)
Definition dyn_two_own_len_STMT : Prop :=
  forall d q' (lit dst : list nat),
    db_acc d -> db_installed d q' ->
    db_lens d = zlens (lit ++ dst) ->
    db_nlen d = Z.of_nat (length lit) ->
    db_ndist d = Z.of_nat (length dst) ->
    db_nlen d <= 286 ->
    db_ndist d <= 30 ->
    (* v3 of this head (amendment (a), an earlier development run finding 2026-08-21,
       cleared q7 freeze v32 + q6 INBOX-0911): [PreGo]-at-LENS is
       DISPATCH information (the machine's missing-EOB check), not
       [db_acc]-derivable — [it_pre] accepts the all-zero window as
       [PreEmpty] with [o_ret = 0] at every type, so without this
       premise the conclusion's PreGo conjunct is falsified by the
       empty-window [DynBuild].  Spelling VERBATIM the zr_len_dispatch
       conjunct (Q6TblChain.v:73), so the composite's supply is a
       direct pass. *)
    (exists c1 st1, it_pre CT_LENS (db_lens d) (db_nlen d) 9
                      (fun i => db_cs d (0 + i)) = PreGo c1 st1) ->
    exists (cL : ItCtx) (stL : ItSt) (ent : nat -> Code),
      it_pre CT_LENS (db_lens d) (db_nlen d) 9
        (fun i => db_cs d (0 + i)) = PreGo cL stL
      /\ (forall sym, ent sym = ZReproQ6K.it_entry cL (Z.of_nat sym) (c_bits (ent sym)))
      /\ zr_two_own_v3
           (tbl_of (q_st q') (t_lencode (s_tab (q_st q'))))
           (o_bits (db_o1 d)) lit ent
      (* v3 of this head (scope-chair pins-conjunct ruling, q6 pre-ARM
         finding: the composite cannot tie pins to a witness across
         separate existentials — the fused form is my own single-
         existential-elim invariant made text): *)
      /\ zr_len_ents lit ent.

(** DIST side: the twin at the installed distcode view.  The DIST build's
    pre-state may be PreGo or accepted-EMPTY (the dispatch carries the
    disjunction); at PreEmpty the table is the two-marker pair and the
    ownership Prop holds with the marker arm at both slots and ANY ent. *)
Definition dyn_two_own_dist_STMT : Prop :=
  forall d q' (lit dst : list nat),
    db_acc d -> db_installed d q' ->
    db_lens d = zlens (lit ++ dst) ->
    db_nlen d = Z.of_nat (length lit) ->
    db_ndist d = Z.of_nat (length dst) ->
    db_nlen d <= 286 ->
    db_ndist d <= 30 ->
    exists (ent : nat -> Code),
      zr_two_own_v3
        (tbl_of (q_st q') (t_distcode (s_tab (q_st q'))))
        (o_bits (db_o2 d)) dst ent
      /\ zr_dist_ents dst ent.

(* ==========================================================================
   B5 — pins, validity, and the population bounds as leg-consumable facts.
   ========================================================================== *)

(** The population bounds, read straight off the v5 dispatch record. *)
Definition zr_dispatch_bounds_STMT : Prop :=
  forall c q qL (lit dst : list nat) d,
    zr_len_dispatch c q qL lit dst d ->
    db_nlen d <= 286 /\ db_ndist d <= 30.

(** Declarative validity at the handover: the decoder's own guards. *)
Definition zr_decode_valid_STMT : Prop :=
  forall bits (lit dst : list nat) r,
    decode_dynamic_tables bits = Some (lit, dst, r) ->
    valid_lengths_b lit 15%nat = true
    /\ valid_lengths_b dst 15%nat = true.

(** Length ties at the handover, decoder-side (the machine side's ties
    are dispatch conjuncts already): 257 <= |lit| <= 288, 1 <= |dst|. *)
Definition zr_decode_lens_STMT : Prop :=
  forall bits (lit dst : list nat) r,
    decode_dynamic_tables bits = Some (lit, dst, r) ->
    (257 <= length lit <= 288)%nat /\ (1 <= length dst)%nat.

(** Pins at builds — the range facts PACKAGED at db_acc (v2 of this
    block, q6 residual catch: the previous citation routed through
    dyn_lenbits_holds/dyn_distbits_holds AT db_ok — a dead route by the
    same amb_ok argument; the live route is it_model_bits_range at
    db_acc's own acceptance equations, the exact derivation my v4
    endpoint already uses).  Install equations and view families remain
    citations: StepReach.db_installed clauses 1-5;
    ItGSubPtr.dyn_len_view_* / ItGSubPtrD.dyn_dist_view_* (NOTE those
    views are db_ok-premised; the composite consumes THESE range lemmas
    and the B3 conclusions instead — the views' db_acc rederivation
    happens inside the B3 proofs, not here). *)

Lemma dyn_lenbits_acc : forall d, db_acc d -> 1 <= o_bits (db_o1 d) <= 15.
Proof.
  intros d Hacc.
  destruct Hacc as (Hwf1 & Hm1 & Hr1 & _).
  destruct Hwf1 as (Hc0 & Hlens & Hroot0 & _).
  exact (it_model_bits_range CT_LENS _ (db_nlen d) 9 _ (db_o1 d)
           ltac:(lia) Hlens Hroot0 Hm1 Hr1).
Qed.

Lemma dyn_distbits_acc : forall d, db_acc d -> 1 <= o_bits (db_o2 d) <= 15.
Proof.
  intros d Hacc.
  destruct Hacc as (Hwf1 & Hm1 & Hr1 & Hwf2 & Hm2 & Hr2).
  destruct Hwf2 as (Hc0 & Hlens & Hroot0 & _).
  exact (it_model_bits_range CT_DISTS _ (db_ndist d) 6 _ (db_o2 d)
           ltac:(lia) Hlens Hroot0 Hm2 Hr2).
Qed.

(* Compile witness: the statement set typechecks against the landed tree. *)
Definition B3B5_export_set : Prop :=
  dyn_two_own_len_STMT /\ dyn_two_own_dist_STMT
  /\ zr_dispatch_bounds_STMT /\ zr_decode_valid_STMT /\ zr_decode_lens_STMT.

(* ==========================================================================
   B5 PROOFS (statements FIT-ruled, freeze v9): the bounds are v5 record
   projections; the decoder facts cite/mirror the LANDED
   decode_dynamic_tables_valid / _sizes (DeflateSpec:953/:977).
   ========================================================================== *)

Lemma zr_dispatch_bounds : zr_dispatch_bounds_STMT.
Proof.
  intros c q qL lit dst d H.
  unfold zr_len_dispatch in H.
  destruct H as (_ & _ & _ & _ & _ & _ & Hb1 & Hb2 & _).
  split; [exact Hb1 | exact Hb2].
Qed.

Lemma zr_decode_valid : zr_decode_valid_STMT.
Proof.
  intros bits lit dst r H. unfold decode_dynamic_tables in H.
  destruct (read_bits 5%nat bits) as [[hlit r1]|]; [|discriminate].
  destruct (read_bits 5%nat r1) as [[hdist r2]|]; [|discriminate].
  destruct (read_bits 4%nat r2) as [[hclen r3]|]; [|discriminate].
  destruct (read_cl_lengths (Z.to_nat hclen + 4)%nat r3) as [[cl r4]|];
    [|discriminate].
  destruct (valid_lengths_b cl 7%nat); [|discriminate].
  destruct (read_lengths cl
              ((Z.to_nat hlit + 257) + (Z.to_nat hdist + 1))%nat r4)
    as [[ls r5]|]; [|discriminate].
  destruct (valid_lengths_b (firstn (Z.to_nat hlit + 257)%nat ls) 15%nat
            && valid_lengths_b (skipn (Z.to_nat hlit + 257)%nat ls) 15%nat)
    eqn:Ev; [|discriminate].
  apply andb_true_iff in Ev as [Hl Hd].
  inversion H; subst.
  split; assumption.
Qed.

Lemma zr_decode_lens : zr_decode_lens_STMT.
Proof.
  intros bits lit dst r H.
  destruct (decode_dynamic_tables_sizes _ _ _ _ H) as [Hl Hd].
  split; [exact Hl | lia].
Qed.

(** The composite's remaining db_ok-cited facts, re-premised at db_acc
    (q7 assembly seam finding, crossed with the head repair; same
    measurement: the underlying proofs discard Hamb).  [db_cover1_acc]
    is [it_covers_all] applied at db_acc's own components;
    [dyn_root_opshape_acc] is the wave's endorsed inhabitation with its
    two db_ok-tier citations swapped for the acc-tier siblings. *)

Lemma db_cover1_acc : forall d, db_acc d ->
  2 ^ o_bits (db_o1 d) <= o_used (db_o1 d)
  /\ (forall j, 0 <= j < 2 ^ o_bits (db_o1 d) ->
      RootEntry CT_LENS (o_bits (db_o1 d)) (o_used (db_o1 d))
        (o_tbl (db_o1 d) j))
  /\ (forall i, 2 ^ o_bits (db_o1 d) <= i < o_used (db_o1 d) ->
      SubEntry CT_LENS (o_bits (db_o1 d)) (o_tbl (db_o1 d) i)).
Proof.
  intros d Hacc.
  destruct Hacc as (Hwf1 & Hm1 & Hr1 & _).
  exact (it_covers_all CT_LENS (db_lens d) (db_nlen d) 9 _ (db_o1 d)
           (or_introl eq_refl) Hwf1 Hm1 Hr1).
Qed.

Lemma dyn_root_opshape_acc : forall d q',
  db_acc d -> db_installed d q' ->
  lcode_root_opshape (tbl_of (q_st q') (t_lencode (s_tab (q_st q'))))
    (t_lenbits (s_tab (q_st q'))).
Proof.
  intros d q' Hacc Hin.
  pose proof (db_cover1_acc d Hacc) as (Hc1u & Hroot1 & _).
  pose proof (dyn_lenbits_acc d Hacc) as Hb1.
  pose proof (db_view_len d q' Hin) as HV.
  pose proof Hin as (Hlc & Hlb & _ & _ & _).
  unfold lcode_root_opshape.
  rewrite Hlc, Hlb. cbn [tbl_of]. cbv beta.
  intros x.
  pose proof (land_ones_range x (o_bits (db_o1 d)) ltac:(lia)) as Hvr.
  rewrite (HV (Z.land x (Z.shiftl 1 (o_bits (db_o1 d)) - 1))
             ltac:(lia)).
  intros Hnz H240 H32 H64.
  destruct (Hroot1 (Z.land x (Z.shiftl 1 (o_bits (db_o1 d)) - 1))
              ltac:(lia)) as [HLeaf | HPtr].
  - destruct HLeaf as ((H1 & _) & _).
    destruct H1 as [H0 | [Ha | Ha]];
      [ exact (False_ind _ (Hnz H0)) | exact Ha
      | exact (False_ind _ (Ha H64)) ].
  - destruct HPtr as (Hbits & Hop & _ & _ & _).
    exfalso. apply H240. apply land240_small. lia.
Qed.

Print Assumptions dyn_root_opshape_acc.
Print Assumptions dyn_lenbits_acc.
Print Assumptions dyn_distbits_acc.
Print Assumptions zr_dispatch_bounds.
Print Assumptions zr_decode_valid.
Print Assumptions zr_decode_lens.
