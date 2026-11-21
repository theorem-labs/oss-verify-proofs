(** * EnoughFitsB3 — B-cluster session 3: the window lemma (s3), the
    paid-ghost invariant AJ2 (DESIGN.md §10), and the refutation trio
    against the three named suppliers (g6-bound lane).

    TRIO STATE (headline in the session receipt): the trio's ALGEBRA is
    the target here, proven against gap_zeros / cross_full /
    open_future as named premises (session-4 suppliers); zero admits —
    Section-hypothesis form throughout.

    f1: open_curr remains the sole it_subsz carrier. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Inftrees ItGTblGeom ItGTblCover ItGSubCover.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughDP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughFitsDesign EnoughFitsA12 EnoughFitsB1
  EnoughFitsB2.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  (s3) — the window lemma: it_subsz's extensions keep the fold
       positive.  [szfold] (B2) is the explicit left-trace; the
       correspondence pins it to it_subsz's own recursion.
   ========================================================================== *)

Lemma it_subsz_fold_corr : forall n cnt drop mx curr0 left0,
  0 < left0 ->
  let r := it_subsz n cnt drop mx curr0 left0 in
  forall j, Z.of_nat j < r - curr0 ->
    0 < szfold cnt drop curr0 left0 (S j).
Proof.
  induction n as [|k IH]; intros cnt drop mx curr0 left0 Hl0; cbv zeta.
  - cbn [it_subsz]. intros j Hj. exfalso. clear -Hj; lia.
  - cbn [it_subsz].
    destruct (Z.ltb_spec (curr0 + drop) mx) as [Hlt|Hge].
    2:{ intros j Hj. exfalso. clear -Hj; lia. }
    destruct (Z.leb_spec (left0 - cnt (curr0 + drop)) 0) as [Hle|Hgt].
    { intros j Hj. exfalso. clear -Hj; lia. }
    intros j Hj.
    destruct j as [|j'].
    + (* the first extension: szfold 1 = (left0 - cnt (curr0+drop)) * 2 *)
      cbn [szfold]. rewrite Z.add_0_r. clear -Hgt; lia.
    + (* deeper extensions: shift the window one step *)
      pose proof (it_subsz_ge k cnt drop mx (curr0 + 1)
                    ((left0 - cnt (curr0 + drop)) * 2)) as Hge1.
      assert (Hrec := IH cnt drop mx (curr0 + 1)
                        ((left0 - cnt (curr0 + drop)) * 2)
                        ltac:(clear -Hgt; lia) j').
      cbv zeta in Hrec.
      assert (Hj' : Z.of_nat j'
                    < it_subsz k cnt drop mx (curr0 + 1)
                        ((left0 - cnt (curr0 + drop)) * 2) - (curr0 + 1)).
      { rewrite Nat2Z.inj_succ in Hj. clear -Hj; lia. }
      specialize (Hrec Hj').
      (* szfold at the shifted window equals szfold at the original,
         one deeper *)
      assert (Hshift : forall p,
                 szfold cnt drop (curr0 + 1)
                   ((left0 - cnt (curr0 + drop)) * 2) p
                 = szfold cnt drop curr0 left0 (S p)).
      { induction p as [|p IHp].
        - cbn [szfold]. rewrite Z.add_0_r. reflexivity.
        - cbn [szfold] in *. rewrite IHp.
          replace (curr0 + 1 + Z.of_nat p) with (curr0 + Z.of_nat (S p))
            by (rewrite Nat2Z.inj_succ; clear; lia).
          reflexivity. }
      rewrite Hshift in Hrec. exact Hrec.
Qed.

(** (s3) in the shape the suppliers consume: positivity along the
    lookahead window of an ACTUAL opening (open_curr wrapper form). *)
Lemma open_curr_window : forall c st,
  let curr0 := step_len c st - open_drop c st in
  0 < Z.shiftl 1 curr0 ->
  forall j, Z.of_nat j < open_curr c st - curr0 ->
    0 < szfold (step_cnt st) (open_drop c st) curr0
          (Z.shiftl 1 curr0) (S j).
Proof.
  intros c st curr0 Hpos j Hj.
  unfold open_curr in Hj.
  exact (it_subsz_fold_corr 16%nat (step_cnt st) (open_drop c st)
           (x_max c) curr0 (Z.shiftl 1 curr0) Hpos j Hj).
Qed.

(* ==========================================================================
   2.  AJ2 — the paid-ghost invariant (DESIGN.md §10).
   ========================================================================== *)

Definition AJ2 (cnt0 : zarr) (R0 : Z) (st : ItSt) : Prop :=
  s_drop st = 0 /\ s_used st = 2 ^ R0
  \/ (s_drop st <> 0
      /\ exists paid,
           s_used st <= fst (aj_acct cnt0 R0 st) + 2 ^ s_curr st - paid
           /\ (paid = 0
               \/ paid = 2 ^ Z.min (s_len st - s_drop st) (s_curr st))
           /\ (paid = 0 ->
               snd (aj_acct cnt0 R0 st) = 0
               /\ s_len st - s_drop st <= s_curr st)).

(** Phase-1 preservation (root filling, no sub-table): a no-open trip
    keeps used = 2^R0 and drop = 0. *)
Lemma aj2_phase1_noopen : forall cnt0 R0 c st,
  x_root c = R0 ->
  AJ2 cnt0 R0 st ->
  s_drop st = 0 ->
  (step_hit st && (s_len st =? x_max c))%bool = false ->
  open_guard c st = false ->
  AJ2 cnt0 R0 (step_noopen_st c st).
Proof.
  intros cnt0 R0 c st HR HAJ Hd Hbrk Hop.
  destruct HAJ as [(Hd0 & Hu) | (Hd0 & _)]; [|exfalso; exact (Hd0 Hd)].
  left. cbn [step_noopen_st s_drop s_used]. split; assumption.
Qed.

(* ==========================================================================
   3.  The supplier obligations (session-4 targets, consumed as
       Section hypotheses by the trio below).
   ========================================================================== *)

Section Trio.
  Variable ty : Z.
  Variable c : ItCtx.
  Variable cnt0 : zarr.
  Variable R0 : Z.

  Hypothesis Hty  : x_type c = ty.
  Hypothesis HR0  : x_root c = R0.
  Hypothesis HR0p : 1 <= R0.
  Hypothesis Hband : ty = CT_LENS \/ ty = CT_DISTS.
  (** True at instantiation: cnt0 = it_count over zzero
      (EnoughFitsA12.it_count_nonneg). *)
  Hypothesis Hcnt0nn : forall j, 0 <= cnt0 j.

  (** The session-5 overlay clauses (AJP /\ AJW), carried abstractly:
      the trio only passes them through to [cross_full]. *)
  Variable AJX : ItSt -> Prop.

  (** SUPPLIER 1 (gap_zeros): at a hit trip the counts strictly between
      the old and new lengths vanish, and the new length is in range. *)
  Hypothesis gap_zeros : forall st,
    CovCtxOk c cnt0 -> CovInv c cnt0 st ->
    SubLedger ty c cnt0 st ->
    step_hit st = true ->
    (step_hit st && (s_len st =? x_max c))%bool = false ->
    s_len st < step_len c st <= x_max c
    /\ (forall l, s_len st < l < step_len c st -> cnt0 l = 0).

  (** SUPPLIER 2 (cross_full): at an open trip from an invariant state,
      the accounting's current sub-table is exactly full — rem = 0 at
      the position — and (phase 2) the paid witness is pinned at the
      full charge. *)
  Hypothesis cross_full : forall st,
    CovCtxOk c cnt0 -> CovInv c cnt0 st ->
    SubLedger ty c cnt0 st ->
    AJ2 cnt0 R0 st -> AJX st ->
    (step_hit st && (s_len st =? x_max c))%bool = false ->
    open_guard c st = true ->
    s_drop st <> 0 ->
    s_used st <= fst (aj_acct cnt0 R0 st).

  (** SUPPLIER 3 (open_future): the pristine maximum from the crossing
      juncture dominates the accounting plus the NEW table's full
      lookahead charge (the (s3)-driven completion descent). *)
  Hypothesis open_future : forall st,
    CovCtxOk c cnt0 -> CovInv c cnt0 st ->
    SubLedger ty c cnt0 st ->
    AJ2 cnt0 R0 st -> AJX st ->
    (step_hit st && (s_len st =? x_max c))%bool = false ->
    open_guard c st = true ->
    s_drop st <> 0 ->
    fst (aj_acct cnt0 R0 st) + Z.shiftl 1 (open_curr c st)
      <= dp_max (S (Z.to_nat (x_max c - s_len st))) (x_max c) R0
           (rem_syms cnt0 (s_len st) (x_max c))
           (kleft cnt0 (s_len st)) (s_len st)
           (fst (chain_at cnt0 R0 (s_len st)))
           (snd (chain_at cnt0 R0 (s_len st))).

  (** i2' carried at the boundary form (the step lemmas thread it;
      its own preservation is part of session 4's seed/step work). *)
  Hypothesis Hi2 : forall st,
    CovCtxOk c cnt0 -> CovInv c cnt0 st ->
    SubLedger ty c cnt0 st ->
    AJ2 cnt0 R0 st -> AJX st ->
    s_drop st <> 0 ->
    dp_max (S (Z.to_nat (x_max c - s_len st))) (x_max c) R0
      (rem_syms cnt0 (s_len st) (x_max c))
      (kleft cnt0 (s_len st)) (s_len st)
      (fst (chain_at cnt0 R0 (s_len st)))
      (snd (chain_at cnt0 R0 (s_len st)))
    <= (if ty =? CT_LENS then ENOUGH_LENS else ENOUGH_DISTS).

  (** SUPPLIER 4 (first_open_ok): the very first sub-table cannot
      overflow — used' = 2^R0 + 2^oc with oc capped at mx - R0, and
      the band's constants absorb it (512 + 64 <= 852; 64 + 512 <=
      592).  Discharged at assembly by constant arithmetic; the
      sub-R0 junctures are outside the dp walk's domain, so the dp
      route only serves phase 2. *)
  Hypothesis first_open_ok : forall st,
    CovCtxOk c cnt0 -> CovInv c cnt0 st ->
    SubLedger ty c cnt0 st ->
    AJ2 cnt0 R0 st -> AJX st ->
    (step_hit st && (s_len st =? x_max c))%bool = false ->
    open_guard c st = true ->
    s_drop st = 0 ->
    it_enough (x_type c) (open_used c st) = false.

  (* ------------------------------------------------------------------ *)
  (** T3 — THE GUARD REFUTATION: an opening from an invariant state
      cannot trip it_enough. *)
  Theorem aj_guard : forall st,
    CovCtxOk c cnt0 -> CovInv c cnt0 st ->
    SubLedger ty c cnt0 st ->
    AJ2 cnt0 R0 st -> AJX st ->
    (step_hit st && (s_len st =? x_max c))%bool = false ->
    open_guard c st = true ->
    it_enough (x_type c) (open_used c st) = false.
  Proof.
    intros st Hctx Hinv Hled HAJ HX Hbrk Hop.
    destruct (Z.eq_dec (s_drop st) 0) as [Hd0 | Hd].
    { exact (first_open_ok st Hctx Hinv Hled HAJ HX Hbrk Hop Hd0). }
    (* phase 2: the crossing is fully paid *)
    assert (Hused : s_used st <= fst (aj_acct cnt0 R0 st))
      by (exact (cross_full st Hctx Hinv Hled HAJ HX Hbrk Hop Hd)).
    (* used' = used + 2^curr' <= dp_max <= EN *)
    pose proof (open_future st Hctx Hinv Hled HAJ HX Hbrk Hop Hd) as HF.
    pose proof (Hi2 st Hctx Hinv Hled HAJ HX Hd) as HEN.
    assert (Hchain : fst (aj_acct cnt0 R0 st)
                     <= fst (aj_acct cnt0 R0 st)) by (clear; lia).
    assert (Hused' : open_used c st
                     <= (if ty =? CT_LENS then ENOUGH_LENS
                         else ENOUGH_DISTS)).
    { unfold open_used.
      (* aj_acct's mem sits between chain_at's mem and dp_max via
         open_future; chain the inequalities *)
      assert (Hacct : fst (aj_acct cnt0 R0 st) + Z.shiftl 1 (open_curr c st)
                      <= (if ty =? CT_LENS then ENOUGH_LENS
                          else ENOUGH_DISTS))
        by (clear -HF HEN; lia).
      clear -Hused Hacct; lia. }
    rewrite Hty.
    unfold it_enough.
    destruct Hband as [HB | HB]; rewrite HB in Hused' |- *.
    - change (CT_LENS =? CT_LENS) with true in Hused' |- *.
      change (CT_LENS =? CT_DISTS) with false.
      cbv iota in Hused'. cbn [andb]. rewrite orb_false_r.
      destruct (Z.ltb_spec ENOUGH_LENS (open_used c st)) as [Hlt|Hge2];
        [exfalso; clear -Hlt Hused'; lia | reflexivity].
    - change (CT_DISTS =? CT_LENS) with false in Hused' |- *.
      change (CT_DISTS =? CT_DISTS) with true.
      cbv iota in Hused'. cbn [andb]. rewrite orb_false_l.
      destruct (Z.ltb_spec ENOUGH_DISTS (open_used c st)) as [Hlt|Hge2];
        [exfalso; clear -Hlt Hused'; lia | reflexivity].
  Qed.

  (* ------------------------------------------------------------------ *)
  (** T2 — the open-trip preservation: the crossing lands the fresh
      sub-table with the paid-ghost at 0 (the DP opens at the first
      code), and the used'-charge is exactly the new 2^curr'. *)
  Theorem aj_open : forall st,
    CovCtxOk c cnt0 -> CovInv c cnt0 st ->
    SubLedger ty c cnt0 st ->
    AJ2 cnt0 R0 st -> AJX st ->
    (step_hit st && (s_len st =? x_max c))%bool = false ->
    open_guard c st = true ->
    it_enough (x_type c) (open_used c st) = false ->
    (* supplier-shaped positional facts for the NEW state (session 5
       discharges them: the mem bound from cross_full + the boundary
       accounting in both phases, the rem from AJP at the fresh
       boundary): *)
    s_used st <= fst (aj_acct cnt0 R0 (step_open_st c st)) ->
    snd (aj_acct cnt0 R0 (step_open_st c st)) = 0 ->
    AJ2 cnt0 R0 (step_open_st c st).
  Proof.
    intros st Hctx Hinv Hled HAJ HX Hbrk Hop Hen Hused' Hrem.
    right.
    split.
    { cbn [step_open_st s_drop].
      unfold open_drop.
      destruct (Z.eqb_spec (s_drop st) 0) as [He|He];
        [clear -HR0p HR0; lia | exact He]. }
    exists 0.
    split;
      [| split;
         [left; reflexivity
         | intros _; split;
           [exact Hrem
           | cbn [step_open_st s_len s_drop s_curr];
             unfold open_curr;
             pose proof (it_subsz_ge 16%nat (step_cnt st)
                           (open_drop c st) (x_max c)
                           (step_len c st - open_drop c st)
                           (Z.shiftl 1 (step_len c st - open_drop c st)));
             clear -H; lia]]].
    cbn [step_open_st s_used s_curr].
    assert (Hsh : Z.shiftl 1 (open_curr c st) = 2 ^ open_curr c st)
      by (rewrite Z.shiftl_1_l; reflexivity).
    unfold open_used in *.
    rewrite Hsh in *.
    clear -Hused'; lia.
  Qed.

End Trio.
