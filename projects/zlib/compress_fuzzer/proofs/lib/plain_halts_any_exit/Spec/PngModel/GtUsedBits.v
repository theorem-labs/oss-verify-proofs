

(** * OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.GtUsedBits — the root block fits inside the
      used extent, and an honest NO on the sub-table pointer range

    Written to answer two questions zlib-lead asked for an open window that
    relativises [InflateFast.lcode_len_bounded] to a bound [n].  Their consumer needs
    [n] pinned between [2 ^ lenbits] and [nx], and asked (a) whether
    [2 ^ lenbits <= nx] is available from my side, and (b) whether my coverage chain
    says anything about sub-table pointers above the root region and below [o_used].

    **(a) YES, and it is cheaper than either of us expected: no [it_wf], no
    well-formedness, and TYPE-GENERIC.**  [it_pre] initialises [s_used] to
    [2 ^ root] and [it_step] never decreases it, so the used extent contains a full
    root block on every accepted call.  [used_ge_root_block] below.  **So the window's
    existential has a witness and the interval is non-empty.**

    **(b) NO, and I am naming it rather than assuming it.**  My landed
    [ItGTblCover.CovInv] carries [2 ^ x_root c <= s_next st] in its phase-2 disjunct —
    a lower bound on where the next sub-table starts — and **nothing relating [s_next]
    to [s_used] in either direction.**  The clause the consumer needs is
    [SubTblPointersBelowUsed] below, stated as a Prop-former so it cannot be
    accidentally true, and it is UNPROVED here and unrouted.  It wants the
    "next points into the allocated region" clause of the fill-loop invariant, which
    is a different clause from the two I proved for the width bound.

    GTBL-ARMS, 2026-08-19.  Not declared until built and gate-clean.  Read-only
    against the graded tree. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Inftrees InflateFast.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ######################################################################### *)
(* 1.  [s_used] STARTS AT THE ROOT BLOCK                                      *)
(* ######################################################################### *)

(** Forward form, and TYPE-GENERIC — the initialisation does not look at [ty], so this
    serves the DISTS build too.  Same direction as my [PreLensOk]: a predicate on the
    result, with a consumer rewriting its own equation in, rather than an inversion. *)
Definition PreUsedOk (r : ItPre) : Prop :=
  match r with
  | PreGo c st => s_used st = Z.shiftl 1 (x_root c)
  | _ => True
  end.

Lemma pre_used_ok : forall ty lens codes root0 t0,
  PreUsedOk (it_pre ty lens codes root0 t0).
Proof.
  intros ty lens codes root0 t0. unfold PreUsedOk, it_pre. cbv zeta.
  destruct (Z.eqb (it_findmax 15%nat MAXBITS (it_count (Z.to_nat codes) 0 lens zzero)) 0);
    [exact I|].
  destruct (it_kraft 15%nat 1 1 (it_count (Z.to_nat codes) 0 lens zzero)) as [lft|];
    [|exact I].
  destruct (it_incomplete ty lft _); [exact I|].
  destruct (it_enough ty _); [exact I|].
  cbn [s_used x_root]. reflexivity.
Qed.

Lemma pre_used_go : forall ty lens codes root0 t0 c st,
  it_pre ty lens codes root0 t0 = PreGo c st ->
  s_used st = Z.shiftl 1 (x_root c).
Proof.
  intros ty lens codes root0 t0 c st H.
  pose proof (pre_used_ok ty lens codes root0 t0) as HP. rewrite H in HP. exact HP.
Qed.

(* ######################################################################### *)
(* 2.  AND NEVER DECREASES                                                    *)
(* ######################################################################### *)

(** The state a step carries, FORWARD, because [Inftrees.v:900-905] measures
    [injection] on an [ItStep] equality past 150 s — the record's fields carry whole
    [it_fill] and [it_subsz] calls.  Nothing below inverts a step result. *)
Definition step_st (r : ItStep) (d : ItSt) : ItSt :=
  match r with ItCont s => s | ItBreak s => s | ItOverflow _ => d end.

(** [it_step] either keeps [s_used] or adds [2 ^ curr'] to it, and a shift of 1 is
    never negative — so monotonicity needs NO side condition at all, not even a bound
    on the sub-table width.  That is the one place in this loop where the arbitrary
    width is harmless. *)
Lemma used_mono_step : forall c st, s_used st <= s_used (step_st (it_step c st) st).
Proof.
  intros c st. unfold it_step. cbv zeta.
  destruct (Z.eqb (zset (s_count st) (s_len st) (s_count st (s_len st) - 1) (s_len st)) 0
            && Z.eqb (s_len st) (x_max c)) eqn:Ebrk;
    [cbn [step_st s_used]; lia|].
  destruct ((Z.ltb (x_root c) _) && negb (Z.eqb _ (s_low st))) eqn:Esub.
  - destruct (it_enough (x_type c) _) eqn:Eover; [cbn [step_st s_used]; lia|].
    cbn [step_st s_used].
    (* the added term is [Z.shiftl 1 curr'] whatever [curr'] is; pull it out of the
       GOAL rather than spelling the [it_subsz] application, which no placeholder can
       infer and which would go stale if the let-order changed *)
    match goal with
    | |- _ <= _ + ?x => assert (0 <= x) by (apply Z.shiftl_nonneg; lia)
    end.
    lia.
  - cbn [step_st s_used]. lia.
Qed.

Lemma used_mono_loop_break : forall n c st st',
  it_loop n c st = Some (ItBreak st') -> s_used st <= s_used st'.
Proof.
  induction n as [|n IH]; intros c st st' H; cbn [it_loop] in H; [discriminate|].
  (* [destruct ... eqn:] already substitutes in any hypothesis mentioning the term, so
     the monotonicity fact is posed AFTER the case split and rewritten there — posing it
     first and rewriting fails with "found no subterm", which reads as a missing fact
     rather than as an already-applied substitution. *)
  destruct (it_step c st) as [s|s|t] eqn:E.
  - assert (Hm : s_used st <= s_used s).
    { pose proof (used_mono_step c st) as H0.
      rewrite E in H0. cbn [step_st] in H0. exact H0. }
    apply (Z.le_trans _ (s_used s) _); [exact Hm | exact (IH c s st' H)].
  - assert (Hm : s_used st <= s_used s).
    { pose proof (used_mono_step c st) as H0.
      rewrite E in H0. cbn [step_st] in H0. exact H0. }
    injection H as H. subst s. exact Hm.
  - discriminate H.
Qed.

(* ######################################################################### *)
(* 3.  THE ANSWER TO (a)                                                      *)
(* ######################################################################### *)

(** THE ROOT BLOCK FITS INSIDE THE USED EXTENT, on every accepted call, for every
    table type, with no well-formedness premise.

    [o_bits] is [x_root c] on the loop-exit arm and [1] on the [max = 0] arm (where
    [o_used = 2] and [2 ^ 1 = 2]), so both accepted arms satisfy it and the error arms
    are excluded by [o_ret = 0]. *)
Theorem used_ge_root_block : forall ty lens codes root0 t0 out,
  it_model ty lens codes root0 t0 = Some out ->
  o_ret out = 0 ->
  2 ^ o_bits out <= o_used out.
Proof.
  intros ty lens codes root0 t0 out Hm Hret. unfold it_model in Hm.
  destruct (it_pre ty lens codes root0 t0) as [|t| |c st] eqn:E.
  - injection Hm as <-. cbn in Hret. lia.
  - injection Hm as <-. cbn. lia.
  - injection Hm as <-. cbn in Hret. lia.
  - destruct (it_loop (S (Z.to_nat codes)) c st) as [r|] eqn:Hl; [|discriminate].
    destruct r as [s|s|tt].
    + discriminate Hm.
    + injection Hm as <-. cbn [o_bits o_used].
      pose proof (pre_used_go ty lens codes root0 t0 c st E) as Hu.
      pose proof (used_mono_loop_break (S (Z.to_nat codes)) c st s Hl) as Hmono.
      rewrite Hu in Hmono. rewrite Z.shiftl_1_l in Hmono. exact Hmono.
    + injection Hm as <-. cbn in Hret. lia.
Qed.

(** Restated in the consumer's shape: the window needs an [n] with
    [2 ^ lenbits <= n <= nx].  For the LENS build the write-back offset is 0, so
    [nx = o_used], and this says the interval is non-empty with [2 ^ o_bits] itself as
    a witness. *)
Corollary window_interval_is_nonempty : forall ty lens codes root0 t0 out,
  it_model ty lens codes root0 t0 = Some out ->
  o_ret out = 0 ->
  exists n, 2 ^ o_bits out <= n <= o_used out.
Proof.
  intros ty lens codes root0 t0 out Hm Hret.
  exists (2 ^ o_bits out). split; [lia|].
  exact (used_ge_root_block ty lens codes root0 t0 out Hm Hret).
Qed.

(* ######################################################################### *)
(* 4.  THE ANSWER TO (b) IS NO, AND HERE IS THE CLAUSE                        *)
(* ######################################################################### *)

(** The consumer's second index-range clause, in [Inftrees] vocabulary and stated as a
    **Prop-former so it cannot be accidentally true**.  A sub-table pointer is an entry
    that [InflateFast.lc_chains] classifies as a chain (op nonzero, bit 4 clear, bit 6
    clear); its [c_val] is the index the decode jumps to.

    **UNPROVED HERE AND UNROUTED.**  What it needs is the "next points into the
    allocated region" clause of the fill-loop invariant — [s_next st + 2 ^ s_curr st <=
    s_used st] or similar.  My landed [ItGTblCover.CovInv] carries
    [2 ^ x_root c <= s_next st] in its phase-2 disjunct, which is a LOWER bound on
    [s_next] and says nothing about [s_used] in either direction; and the two clauses I
    proved for the width bound ([DropTwoValued], [Len1Bounded]) are about widths, not
    positions.  **So this is a third clause of the same invariant, not a corollary of
    anything I hold.**  I have not attempted it and am not pricing it. *)
Definition SubTblPointersBelowUsed : Prop :=
  forall ty lens codes root0 t0 out,
    it_model ty lens codes root0 t0 = Some out ->
    o_ret out = 0 ->
    forall i, 0 <= i < o_used out ->
      lc_chains (c_op (o_tbl out i)) = true ->
      0 <= c_val (o_tbl out i) < o_used out.

(** And the shape of the composition it would enable, so the consumer can see exactly
    what the missing clause buys and can cite this rather than re-deriving it.  Note
    the [n = o_used] instantiation: at [n = 2 ^ o_bits] the clause would be FALSE, since
    a pointer's target deliberately points ABOVE the root block — which is the reason
    the consumer's [n] cannot be the root size. *)
Theorem pointers_below_used_gives_the_clause :
  SubTblPointersBelowUsed ->
  forall ty lens codes root0 t0 out,
    it_model ty lens codes root0 t0 = Some out ->
    o_ret out = 0 ->
    forall i, 0 <= i < o_used out ->
      lc_chains (c_op (o_tbl out i)) = true ->
      0 <= c_val (o_tbl out i) < o_used out.
Proof. intros H ty lens codes root0 t0 out. apply H. Qed.

Print Assumptions pre_used_ok.
Print Assumptions pre_used_go.
Print Assumptions used_mono_step.
Print Assumptions used_mono_loop_break.
Print Assumptions used_ge_root_block.
Print Assumptions window_interval_is_nonempty.
Print Assumptions pointers_below_used_gives_the_clause.
