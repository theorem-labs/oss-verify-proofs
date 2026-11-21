(** * EnoughFitsB6 — session 5, part 2: AJW, the window-tightness
    clause (P2's carrier).

    it_subsz's minimality — the fold stays positive at every depth
    short of the returned lookahead — is a fact about the OPENING
    state.  Carried forward it becomes per-state: the fold over the
    CURRENT counts, seeded with the room left in the unit ([aj_left]),
    stays positive below the table's depth.  Preservation is an
    ALGEBRAIC fold identity (a same-length code moves one unit of
    slack from the seed into the first subtracted count; a hit
    composes the gap's doublings), establishment at an open is the
    landed [open_curr_window] verbatim, and consumption at aj_left = 1
    is P2: a table that fills does so at its depth. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Inftrees ItGTblRev ItGTblGeom ItGTblSortWin ItGTblCover ItGSubCover.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7Strict.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughDP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughFitsDesign EnoughFitsA12 EnoughFitsB1
  EnoughFitsB2 EnoughFitsB3 EnoughFitsB4 EnoughFitsB5.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  Fold transport identities.
   ========================================================================== *)

(** Consuming one code at the window's first level: the decrement in
    the count cancels the decrement in the seed. *)
Lemma szfold_step_dec : forall cnt R0 curr0 L ix j,
  ix = curr0 + R0 ->
  szfold (zset cnt ix (cnt ix - 1)) R0 curr0 (L - 1) (S j)
  = szfold cnt R0 curr0 L (S j).
Proof.
  intros cnt R0 curr0 L ix j Hix. subst ix.
  induction j as [|j IH].
  - cbn [szfold].
    rewrite Z.add_0_r, zset_same.
    clear; lia.
  - cbn [szfold] in IH |- *.
    rewrite IH.
    rewrite zset_other by (clear; lia).
    reflexivity.
Qed.

(** Splitting a fold at a depth. *)
Lemma szfold_compose : forall cnt R0 c0 L j1 j2,
  szfold cnt R0 c0 L (j1 + j2)
  = szfold cnt R0 (c0 + Z.of_nat j1) (szfold cnt R0 c0 L j1) j2.
Proof.
  intros cnt R0 c0 L j1 j2.
  induction j2 as [|j2 IH].
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite Nat.add_succ_r. cbn [szfold].
    rewrite IH.
    f_equal. f_equal. f_equal.
    clear; lia.
Qed.

(** A zero-count stretch only doubles the seed. *)
Lemma szfold_zeros : forall cnt R0 c0 L n,
  (forall j, (j < n)%nat -> cnt (c0 + Z.of_nat j + R0) = 0) ->
  szfold cnt R0 c0 L n = L * 2 ^ Z.of_nat n.
Proof.
  intros cnt R0 c0 L n Hz.
  induction n as [|n IH].
  - cbn [szfold]. change (Z.of_nat 0) with 0.
    rewrite Z.pow_0_r, Z.mul_1_r. reflexivity.
  - cbn [szfold].
    rewrite IH by (intros j Hj; apply Hz; clear -Hj; lia).
    rewrite (Hz n ltac:(clear; lia)), Z.sub_0_r.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by (clear; lia).
    ring.
Qed.

(** Folds only read the counts at their own levels. *)
Lemma szfold_ext_on : forall cnt cnt' R0 c0 L n,
  (forall j, (j < n)%nat ->
     cnt' (c0 + Z.of_nat j + R0) = cnt (c0 + Z.of_nat j + R0)) ->
  szfold cnt' R0 c0 L n = szfold cnt R0 c0 L n.
Proof.
  intros cnt cnt' R0 c0 L n He.
  induction n as [|n IH].
  - reflexivity.
  - cbn [szfold].
    rewrite IH by (intros j Hj; apply He; clear -Hj; lia).
    rewrite (He n ltac:(clear; lia)).
    reflexivity.
Qed.

(* ==========================================================================
   2.  AJW — definition, consumption (P2), establishment, preservation.
   ========================================================================== *)

(** In phase 2: at every depth short of the open table's lookahead,
    the window's counts cannot fill the rest of the unit. *)
Definition AJW (R0 : Z) (st : ItSt) : Prop :=
  s_drop st = 0
  \/ (forall j, Z.of_nat j < s_curr st - (s_len st - R0) ->
        0 < szfold (s_count st) R0 (s_len st - R0) (aj_left R0 st) (S j)).

(** P2: a table that fills does so at its depth.  At the completing
    trip the room is one quantum; a spare lookahead level would make
    the fold nonpositive at the very first extension. *)
Lemma ajw_p2 : forall R0 st,
  AJW R0 st ->
  s_drop st <> 0 ->
  aj_left R0 st = 1 ->
  1 <= s_count st (s_len st) ->
  s_curr st <= s_len st - R0.
Proof.
  intros R0 st HW Hd Hleft Hcnt.
  destruct HW as [Habs | HW]; [exfalso; exact (Hd Habs)|].
  destruct (Z.le_gt_cases (s_curr st) (s_len st - R0)) as [Hok|Hbad];
    [exact Hok | exfalso].
  specialize (HW 0%nat ltac:(clear -Hbad; cbn; lia)).
  cbn [szfold] in HW.
  rewrite Hleft in HW.
  replace (s_len st - R0 + Z.of_nat 0 + R0) with (s_len st) in HW
    by (clear; cbn; lia).
  clear -HW Hcnt; lia.
Qed.

(** The new offset at an open trip is zero: the fresh table starts at
    its own unit boundary. *)
Lemma aj_off_zero_at_open : forall c cnt0 R0 st,
  x_root c = R0 ->
  CovCtxOk c cnt0 -> CovInv c cnt0 st ->
  (step_hit st && (s_len st =? x_max c))%bool = false ->
  open_guard c st = true ->
  aj_off R0 (step_open_st c st) = 0.
Proof.
  intros c cnt0 R0 st HR Hctx Hinv Hbrk Hop.
  subst R0.
  pose proof Hctx as Hctx2.
  pose proof Hinv as Hinv2.
  destruct Hctx as (Hroot & Hmask & Hmx & Hmxnz & Hmxz & Hnn & _).
  destruct Hinv as (Hlen & Hhuff & HwinL & HwinU & Hcnt & Hpos & Hcov
                    & Hphase).
  assert (Hb' : 0 <= step_huff st < 2 ^ s_len st)
    by (apply step_huff_bounds; [exact Hlen | exact Hhuff]).
  unfold aj_off.
  cbn [step_open_st s_len s_huff].
  destruct (Z.eq_dec (s_drop st) 0) as [Hd0 | Hd].
  - (* first open: the counter still fits under the root *)
    destruct Hphase as [ (_ & _ & _ & _ & Hlenroot) | (Hdr & _) ];
      [| exfalso; rewrite Hd0 in Hdr; clear -Hdr Hroot; lia].
    assert (Hsh0 : Z.shiftr (step_huff st) (x_root c) = 0).
    { rewrite Z.shiftr_div_pow2 by (clear -Hroot; lia).
      apply Z.div_small.
      split; [clear -Hb'; lia|].
      assert (2 ^ s_len st <= 2 ^ x_root c)
        by (apply Z.pow_le_mono_r; clear -Hlenroot; lia).
      clear -Hb' H; lia. }
    rewrite Hsh0. apply zrev_zero.
  - (* phase 2: the carry lands the offset at zero, then widens *)
    destruct (off_step_facts c cnt0 st Hctx2 Hinv2 Hbrk Hd)
      as (_ & [(Hgf & _) | (_ & _ & Hzero)]);
      [rewrite Hop in Hgf; discriminate Hgf|].
    destruct Hphase as [ (Habs & _) | (Hdr & Hrl & _) ];
      [exfalso; exact (Hd Habs)|].
    assert (Hd1 : 1 <= s_len st - x_root c) by (clear -Hrl; lia).
    destruct (step_hit st) eqn:Hhit.
    + assert (Hbrk2 : (step_hit st && (s_len st =? x_max c))%bool = false)
        by (rewrite Hhit; exact Hbrk).
      destruct (gap_zeros_lem c cnt0 st Hctx2 Hinv2 Hhit Hbrk2)
        as [[Hjl _] _].
      assert (Hwide : Z.to_nat (step_len c st - x_root c)
                      = (Z.to_nat (s_len st - x_root c)
                         + Z.to_nat (step_len c st - s_len st))%nat)
        by (clear -Hjl Hrl; lia).
      rewrite Hwide.
      rewrite (zrev_widen (Z.to_nat (s_len st - x_root c))
                 (Z.to_nat (step_len c st - s_len st))
                 (Z.shiftr (step_huff st) (x_root c))).
      2:{ rewrite Z2Nat.id by (clear -Hd1; lia).
          apply shiftr_range; [clear -Hroot Hrl; lia | exact Hb']. }
      rewrite Hzero. apply Z.mul_0_l.
    + assert (Hsl : step_len c st = s_len st)
        by (unfold step_len; rewrite Hhit; reflexivity).
      rewrite Hsl. exact Hzero.
Qed.

(** Establishment: an open trip hands the fresh table the landed
    lookahead-minimality fact, re-seeded at the full unit. *)
Lemma ajw_open : forall c cnt0 R0 st,
  x_root c = R0 ->
  CovCtxOk c cnt0 -> CovInv c cnt0 st ->
  (step_hit st && (s_len st =? x_max c))%bool = false ->
  open_guard c st = true ->
  AJW R0 (step_open_st c st).
Proof.
  intros c cnt0 R0 st HR Hctx Hinv Hbrk Hop.
  pose proof (aj_off_zero_at_open c cnt0 R0 st HR Hctx Hinv Hbrk Hop)
    as Hoff0.
  subst R0.
  pose proof Hinv as Hinv2.
  destruct Hctx as (Hroot & _).
  destruct Hinv as (Hlen & Hhuff & _ & _ & _ & _ & _ & Hphase).
  assert (HrSL : x_root c < step_len c st).
  { unfold open_guard in Hop.
    apply andb_true_iff in Hop. destruct Hop as [Hltb _].
    apply Z.ltb_lt in Hltb. exact Hltb. }
  (* the open's drop is the root in both phases *)
  assert (Hod : open_drop c st = x_root c).
  { unfold open_drop.
    destruct Hphase as [ (Hd0 & _) | (Hdr & _) ].
    - rewrite Hd0. reflexivity.
    - destruct (Z.eqb_spec (s_drop st) 0) as [He|_];
        [rewrite He in Hdr; rewrite <- Hdr; reflexivity | exact Hdr]. }
  right.
  cbn [step_open_st s_curr s_len s_count s_drop].
  intros j Hj.
  assert (Hleft : aj_left (x_root c) (step_open_st c st)
                  = Z.shiftl 1 (step_len c st - x_root c)).
  { unfold aj_left. rewrite Hoff0, Z.sub_0_r.
    cbn [step_open_st s_len].
    rewrite Z.shiftl_1_l. reflexivity. }
  rewrite Hleft.
  pose proof (open_curr_window c st) as HW.
  cbv zeta in HW.
  rewrite Hod in HW.
  apply HW.
  - rewrite Z.shiftl_1_l.
    apply Z.pow_pos_nonneg; clear -HrSL Hroot; lia.
  - exact Hj.
Qed.

(** Preservation across a closed trip. *)
Lemma ajw_noopen : forall c cnt0 R0 st,
  x_root c = R0 ->
  CovCtxOk c cnt0 -> CovInv c cnt0 st ->
  AJW R0 st ->
  (step_hit st && (s_len st =? x_max c))%bool = false ->
  open_guard c st = false ->
  AJW R0 (step_noopen_st c st).
Proof.
  intros c cnt0 R0 st HR Hctx Hinv HW Hbrk Hop.
  subst R0.
  destruct (Z.eq_dec (s_drop st) 0) as [Hd0 | Hd];
    [left; cbn [step_noopen_st s_drop]; exact Hd0|].
  destruct HW as [Habs | HW]; [exfalso; exact (Hd Habs)|].
  right.
  pose proof Hctx as Hctx2.
  pose proof Hinv as Hinv2.
  destruct Hctx as (Hroot & Hmask & Hmx & Hmxnz & Hmxz & Hnn & _).
  destruct Hinv as (Hlen & Hhuff & HwinL & HwinU & Hcnt & Hpos & Hcov
                    & Hphase).
  destruct Hphase as [ (Habs & _) | (Hdr & Hrl & _) ];
    [exfalso; exact (Hd Habs)|].
  assert (Hd1 : 1 <= s_len st - x_root c) by (clear -Hrl; lia).
  destruct (off_step_facts c cnt0 st Hctx2 Hinv2 Hbrk Hd)
    as (Hb' & [(_ & Hadv) | (Hgt & _ & _)]);
    [| rewrite Hop in Hgt; discriminate Hgt].
  assert (HOFF : 0 <= zrev (Z.to_nat (s_len st - x_root c))
                        (Z.shiftr (s_huff st) (x_root c))
                 < 2 ^ (s_len st - x_root c)).
  { split; [apply zrev_nonneg|].
    pose proof (zrev_lt (Z.to_nat (s_len st - x_root c))
                  (Z.shiftr (s_huff st) (x_root c))) as H.
    rewrite Z2Nat.id in H by (clear -Hd1; lia). exact H. }
  set (OFF := zrev (Z.to_nat (s_len st - x_root c))
                (Z.shiftr (s_huff st) (x_root c))) in *.
  set (OFF' := zrev (Z.to_nat (s_len st - x_root c))
                 (Z.shiftr (step_huff st) (x_root c))) in *.
  destruct (step_hit st) eqn:Hhit.
  - (* hit inside the unit: compose the first level and the gap *)
    assert (Hbrk2 : (step_hit st && (s_len st =? x_max c))%bool = false)
      by (rewrite Hhit; exact Hbrk).
    destruct (gap_zeros_lem c cnt0 st Hctx2 Hinv2 Hhit Hbrk2)
      as [[Hjl Hjmx] Hgz].
    assert (Hone : s_count st (s_len st) = 1).
    { unfold step_hit, step_cnt in Hhit.
      rewrite zset_same in Hhit.
      apply Z.eqb_eq in Hhit. clear -Hhit; lia. }
    assert (Hleft' : aj_left (x_root c) (step_noopen_st c st)
                     = (aj_left (x_root c) st - 1)
                       * 2 ^ (step_len c st - s_len st)).
    { unfold aj_left, aj_off.
      cbn [step_noopen_st s_len s_huff].
      assert (Hwide : Z.to_nat (step_len c st - x_root c)
                      = (Z.to_nat (s_len st - x_root c)
                         + Z.to_nat (step_len c st - s_len st))%nat)
        by (clear -Hjl Hrl; lia).
      rewrite Hwide.
      rewrite (zrev_widen (Z.to_nat (s_len st - x_root c))
                 (Z.to_nat (step_len c st - s_len st))
                 (Z.shiftr (step_huff st) (x_root c))).
      2:{ rewrite Z2Nat.id by (clear -Hd1; lia).
          apply shiftr_range; [clear -Hroot Hrl; lia | exact Hb']. }
      rewrite Z2Nat.id by (clear -Hjl; lia).
      fold OFF'. fold OFF. rewrite Hadv.
      assert (Hpw : 2 ^ (s_len st - x_root c)
                      * 2 ^ (step_len c st - s_len st)
                    = 2 ^ (step_len c st - x_root c)).
      { rewrite <- Z.pow_add_r by (clear -Hd1 Hjl; lia).
        f_equal. clear; lia. }
      rewrite !Z.mul_sub_distr_r, Z.mul_add_distr_r, !Z.mul_1_l, Hpw.
      clear; lia. }
    cbn [step_noopen_st s_curr s_len s_count s_drop].
    intros j Hj.
    rewrite Hleft'.
    set (DN := Z.to_nat (step_len c st - s_len st)).
    assert (HDN : Z.of_nat DN = step_len c st - s_len st)
      by (unfold DN; rewrite Z2Nat.id by (clear -Hjl; lia); reflexivity).
    specialize (HW ((DN - 1) + S j)%nat).
    assert (Hjw : Z.of_nat ((DN - 1) + S j)%nat
                  < s_curr st - (s_len st - x_root c)).
    { rewrite Nat2Z.inj_add.
      rewrite Nat2Z.inj_sub by (unfold DN; clear -Hjl; lia).
      rewrite HDN. clear -Hj HDN Hjl; lia. }
    specialize (HW Hjw).
    replace (S ((DN - 1) + S j))%nat with (DN + S j)%nat in HW
      by (unfold DN; clear -Hjl; lia).
    rewrite szfold_compose in HW.
    assert (Hpref : szfold (s_count st) (x_root c) (s_len st - x_root c)
                      (aj_left (x_root c) st) DN
                    = (aj_left (x_root c) st - 1)
                      * 2 ^ (step_len c st - s_len st)).
    { replace DN with (1 + (DN - 1))%nat by (unfold DN; clear -Hjl; lia).
      rewrite szfold_compose.
      cbn [szfold].
      rewrite Z.add_0_r.
      replace (s_len st - x_root c + x_root c) with (s_len st)
        by (clear; lia).
      rewrite Hone.
      rewrite szfold_zeros.
      2:{ intros i Hi.
          apply Nat2Z.inj_lt in Hi.
          rewrite Nat2Z.inj_sub in Hi by (unfold DN; clear -Hjl; lia).
          rewrite HDN in Hi.
          replace (s_len st - x_root c + Z.of_nat 1 + Z.of_nat i + x_root c)
            with (s_len st + 1 + Z.of_nat i) by (clear; cbn; lia).
          rewrite (Hcnt (s_len st + 1 + Z.of_nat i)
                     ltac:(clear -Hi Hlen Hjl Hjmx Hmx; lia)).
          destruct (Z.ltb_spec (s_len st + 1 + Z.of_nat i) (s_len st))
            as [Habs|_]; [exfalso; clear -Habs; lia|].
          destruct (Z.eqb_spec (s_len st + 1 + Z.of_nat i) (s_len st))
            as [Habs|_]; [exfalso; clear -Habs; lia|].
          apply Hgz.
          clear -Hi; lia. }
      replace (Z.of_nat (DN - 1)%nat)
        with (step_len c st - s_len st - 1)
        by (rewrite Nat2Z.inj_sub by (unfold DN; clear -Hjl; lia);
            rewrite HDN; clear; cbn; lia).
      replace (2 ^ (step_len c st - s_len st))
        with (2 * 2 ^ (step_len c st - s_len st - 1)).
      2:{ rewrite <- Z.pow_succ_r by (clear -Hjl; lia).
          f_equal. clear; lia. }
      ring. }
    rewrite Hpref in HW.
    replace (s_len st - x_root c + Z.of_nat DN)
      with (step_len c st - x_root c) in HW
      by (rewrite HDN; clear; lia).
    rewrite <- (szfold_ext_on (s_count st) (step_cnt st) (x_root c)
                  (step_len c st - x_root c)
                  ((aj_left (x_root c) st - 1)
                     * 2 ^ (step_len c st - s_len st))
                  (S j)) in HW.
    2:{ intros i Hi. unfold step_cnt. apply zset_other.
        clear -Hjl Hroot Hrl; lia. }
    exact HW.
  - (* same length: the seed's decrement cancels the count's *)
    assert (Hsl : step_len c st = s_len st)
      by (unfold step_len; rewrite Hhit; reflexivity).
    assert (Hleft' : aj_left (x_root c) (step_noopen_st c st)
                     = aj_left (x_root c) st - 1).
    { unfold aj_left, aj_off.
      cbn [step_noopen_st s_len s_huff].
      rewrite Hsl.
      fold OFF'. fold OFF. rewrite Hadv. clear; lia. }
    cbn [step_noopen_st s_curr s_len s_count s_drop].
    rewrite Hsl.
    intros j Hj.
    rewrite Hleft'.
    unfold step_cnt.
    rewrite (szfold_step_dec (s_count st) (x_root c)
               (s_len st - x_root c) (aj_left (x_root c) st) (s_len st) j
               ltac:(clear; lia)).
    apply HW. exact Hj.
Qed.
