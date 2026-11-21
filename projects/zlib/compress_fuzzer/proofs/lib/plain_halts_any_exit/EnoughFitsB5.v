(** * EnoughFitsB5 — B-cluster session 5: the zrev wall (w1 + w2).

    (w1) The huff-position geometry.  CovInv's position identity makes
    the reversed counter THE position; under the root split
    (zrev_decomp) its increment either stays inside the unit — the
    intra-unit offset advances by one — or CARRIES: the old offset was
    the unit's last slot, the new offset is zero, and the root prefix
    changed.  So "prefix change" (the open test) IS "position at a
    unit boundary".

    (w2) Consumers: Hgeo (an open table's length has not passed its
    lookahead depth) from SubLedger's guard clause by wmass-vanishing,
    and gap_zeros from the landed sort-window lemmas
    (cov_next_window / cov_exhausted). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Inftrees ItGTblRev ItGTblGeom ItGTblSortWin ItGTblCover ItGSubCover.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7Strict.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughDP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughFitsDesign EnoughFitsA12 EnoughFitsB1
  EnoughFitsB2 EnoughFitsB3 EnoughFitsB4.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  The intra-unit offset and the increment law (w1).
   ========================================================================== *)

(** The reversed intra-unit offset, and the room left in the unit, in
    level-[s_len] quanta.  [aj_left] is the state-local value the AJP
    clause pins the accounting rem to. *)
Definition aj_off (R0 : Z) (st : ItSt) : Z :=
  zrev (Z.to_nat (s_len st - R0)) (Z.shiftr (s_huff st) R0).
Definition aj_left (R0 : Z) (st : ItSt) : Z :=
  2 ^ (s_len st - R0) - aj_off R0 st.

Lemma aj_off_bounds : forall R0 st,
  R0 <= s_len st ->
  0 <= aj_off R0 st < 2 ^ (s_len st - R0).
Proof.
  intros R0 st Hle. unfold aj_off.
  split; [apply zrev_nonneg|].
  pose proof (zrev_lt (Z.to_nat (s_len st - R0)) (Z.shiftr (s_huff st) R0))
    as H.
  rewrite Z2Nat.id in H by (clear -Hle; lia). exact H.
Qed.

(** The increment law under the root split: same prefix advances the
    offset; a prefix change is a carry — the offset was at the unit's
    last slot and lands at zero. *)
Lemma off_incr_split : forall R0 len h h',
  1 <= R0 < len -> len <= 15 ->
  0 <= h < 2 ^ len -> 0 <= h' < 2 ^ len ->
  zrev (Z.to_nat len) h' = zrev (Z.to_nat len) h + 1 ->
  ( h' mod 2 ^ R0 = h mod 2 ^ R0
    /\ zrev (Z.to_nat (len - R0)) (Z.shiftr h' R0)
       = zrev (Z.to_nat (len - R0)) (Z.shiftr h R0) + 1 )
  \/ ( h' mod 2 ^ R0 <> h mod 2 ^ R0
      /\ zrev (Z.to_nat (len - R0)) (Z.shiftr h R0) = 2 ^ (len - R0) - 1
      /\ zrev (Z.to_nat (len - R0)) (Z.shiftr h' R0) = 0 ).
Proof.
  intros R0 len h h' HR Hl Hh Hh' Hinc.
  rewrite (zrev_decomp R0 len h ltac:(clear -HR; lia) ltac:(clear -Hl; lia)
             ltac:(exact Hh)) in Hinc.
  rewrite (zrev_decomp R0 len h' ltac:(clear -HR; lia) ltac:(clear -Hl; lia)
             ltac:(exact Hh')) in Hinc.
  set (P1 := zrev (Z.to_nat R0) (h mod 2 ^ R0)) in *.
  set (P2 := zrev (Z.to_nat R0) (h' mod 2 ^ R0)) in *.
  set (O1 := zrev (Z.to_nat (len - R0)) (Z.shiftr h R0)) in *.
  set (O2 := zrev (Z.to_nat (len - R0)) (Z.shiftr h' R0)) in *.
  assert (HD : 0 < 2 ^ (len - R0))
    by (apply Z.pow_pos_nonneg; clear -HR; lia).
  assert (HO1 : 0 <= O1 < 2 ^ (len - R0)).
  { unfold O1. split; [apply zrev_nonneg|].
    pose proof (zrev_lt (Z.to_nat (len - R0)) (Z.shiftr h R0)) as H.
    rewrite Z2Nat.id in H by (clear -HR; lia). exact H. }
  assert (HO2 : 0 <= O2 < 2 ^ (len - R0)).
  { unfold O2. split; [apply zrev_nonneg|].
    pose proof (zrev_lt (Z.to_nat (len - R0)) (Z.shiftr h' R0)) as H.
    rewrite Z2Nat.id in H by (clear -HR; lia). exact H. }
  destruct (Z.eq_dec (h' mod 2 ^ R0) (h mod 2 ^ R0)) as [He|Hne].
  - left. split; [exact He|].
    assert (HPP : P2 = P1) by (unfold P2, P1; rewrite He; reflexivity).
    rewrite HPP in Hinc. clear -Hinc; lia.
  - right. split; [exact Hne|].
    assert (Hm : 0 <= h mod 2 ^ R0 < 2 ^ R0)
      by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; clear -HR; lia).
    assert (Hm' : 0 <= h' mod 2 ^ R0 < 2 ^ R0)
      by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; clear -HR; lia).
    assert (HPP : P2 <> P1).
    { intro Heq. apply Hne.
      apply (zrev_inj (Z.to_nat R0)).
      - rewrite Z2Nat.id by (clear -HR; lia). exact Hm'.
      - rewrite Z2Nat.id by (clear -HR; lia). exact Hm.
      - exact Heq. }
    destruct (Z.lt_trichotomy P2 P1) as [Hlt | [Heq | Hgt]];
      [| exfalso; exact (HPP Heq) |].
    + exfalso.
      assert (Hle : P2 * 2 ^ (len - R0) <= (P1 - 1) * 2 ^ (len - R0))
        by (apply Z.mul_le_mono_nonneg_r; clear -Hlt HD; lia).
      rewrite Z.mul_sub_distr_r, Z.mul_1_l in Hle.
      clear -Hinc Hle HO1 HO2 HD; lia.
    + assert (Hle : (P1 + 1) * 2 ^ (len - R0) <= P2 * 2 ^ (len - R0))
        by (apply Z.mul_le_mono_nonneg_r; clear -Hgt HD; lia).
      rewrite Z.mul_add_distr_r, Z.mul_1_l in Hle.
      split; clear -Hinc Hle HO1 HO2 HD; lia.
Qed.

(** The wrap case: an all-ones reversed counter sits at the last slot
    of the last unit. *)
Lemma off_wrap_split : forall R0 len h,
  1 <= R0 < len -> len <= 15 ->
  0 <= h < 2 ^ len ->
  zrev (Z.to_nat len) h = 2 ^ len - 1 ->
  h mod 2 ^ R0 = 2 ^ R0 - 1
  /\ zrev (Z.to_nat (len - R0)) (Z.shiftr h R0) = 2 ^ (len - R0) - 1.
Proof.
  intros R0 len h HR Hl Hh Hw.
  rewrite (zrev_decomp R0 len h ltac:(clear -HR; lia) ltac:(clear -Hl; lia)
             ltac:(exact Hh)) in Hw.
  set (P1 := zrev (Z.to_nat R0) (h mod 2 ^ R0)) in *.
  set (O1 := zrev (Z.to_nat (len - R0)) (Z.shiftr h R0)) in *.
  assert (HD : 0 < 2 ^ (len - R0))
    by (apply Z.pow_pos_nonneg; clear -HR; lia).
  assert (HO1 : 0 <= O1 < 2 ^ (len - R0)).
  { unfold O1. split; [apply zrev_nonneg|].
    pose proof (zrev_lt (Z.to_nat (len - R0)) (Z.shiftr h R0)) as H.
    rewrite Z2Nat.id in H by (clear -HR; lia). exact H. }
  assert (Hm : 0 <= h mod 2 ^ R0 < 2 ^ R0)
    by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; clear -HR; lia).
  assert (HP1 : 0 <= P1 < 2 ^ R0).
  { unfold P1. split; [apply zrev_nonneg|].
    pose proof (zrev_lt (Z.to_nat R0) (h mod 2 ^ R0)) as H.
    rewrite Z2Nat.id in H by (clear -HR; lia). exact H. }
  assert (Hsplit : 2 ^ len = 2 ^ R0 * 2 ^ (len - R0)).
  { rewrite <- Z.pow_add_r by (clear -HR; lia).
    f_equal. clear; lia. }
  rewrite Hsplit in Hw.
  (* forced: P1 = 2^R0 - 1 and O1 = D - 1 *)
  assert (HPle : P1 * 2 ^ (len - R0) <= (2 ^ R0 - 1) * 2 ^ (len - R0))
    by (apply Z.mul_le_mono_nonneg_r; clear -HP1 HD; lia).
  rewrite Z.mul_sub_distr_r, Z.mul_1_l in HPle.
  assert (HO1e : O1 = 2 ^ (len - R0) - 1) by (clear -Hw HPle HO1 HD; lia).
  split; [| exact HO1e].
  assert (HP1e : P1 * 2 ^ (len - R0) = (2 ^ R0 - 1) * 2 ^ (len - R0)).
  { rewrite Z.mul_sub_distr_r, Z.mul_1_l. clear -Hw HO1e HD; lia. }
  apply Z.mul_cancel_r in HP1e; [| clear -HD; lia].
  apply (zrev_inj (Z.to_nat R0)).
  - rewrite Z2Nat.id by (clear -HR; lia). exact Hm.
  - rewrite Z2Nat.id by (clear -HR; lia).
    split; [clear -HR HP1 HP1e; lia |].
    assert (0 < 2 ^ R0) by (apply Z.pow_pos_nonneg; clear -HR; lia).
    clear -H; lia.
  - unfold P1 in HP1e. rewrite HP1e.
    pose proof (zrev_ones (Z.to_nat R0)) as H.
    rewrite Z2Nat.id in H by (clear -HR; lia). exact (eq_sym H).
Qed.

(** Prefix extraction: the mask is the low root bits. *)
Lemma land_mask_mod : forall root h,
  0 <= root -> 0 <= h ->
  Z.land h (2 ^ root - 1) = h mod 2 ^ root.
Proof.
  intros root h Hr Hh.
  rewrite Z.sub_1_r, <- Z.ones_equiv.
  apply Z.land_ones. exact Hr.
Qed.

(* ==========================================================================
   2.  w2a — Hgeo: the guard forbids a code deeper than the lookahead.
   ========================================================================== *)

Lemma wmass_zero_on : forall n l cnt,
  (forall i, l <= i < l + Z.of_nat n -> cnt i = 0) ->
  wmass n l cnt = 0.
Proof.
  induction n as [|n IH]; intros l cnt Hz; cbn [wmass].
  - reflexivity.
  - assert (Hl : cnt l = 0) by (apply Hz; clear; lia).
    rewrite Hl, Z.mul_0_l, Z.add_0_l.
    apply IH. intros i Hi. apply Hz. clear -Hi; lia.
Qed.

(** Hgeo, per-state: in phase 2 the current code fits the open
    sub-table's lookahead depth.  If it did not, every level within
    the window would sit strictly below [s_len] where the sweep's
    counts are zero, the window mass would vanish, and SubLedger's
    guard would push the position past its own unit. *)
Lemma geo_of_guard : forall ty c cnt0 st,
  CovCtxOk c cnt0 -> CovInv c cnt0 st -> SubLedger ty c cnt0 st ->
  s_drop st <> 0 ->
  s_len st - s_drop st <= s_curr st.
Proof.
  intros ty c cnt0 st Hctx Hinv Hled Hd.
  destruct Hctx as (Hroot & Hmask & Hmx & Hmxnz & Hmxz & Hnn & Hcodes & Hlens
                    & Hcnt0 & Hwork & Hupper & Hcase & Hrootmx).
  destruct Hinv as (Hlen & Hhuff & HwinL & HwinU & Hcnt & Hpos & Hcov
                    & Hphase).
  destruct Hphase as [ (Hd0 & _) | (Hdr & Hrl & Hnx & Hloweq & _) ];
    [exfalso; exact (Hd Hd0) |].
  destruct Hled as (_ & [ (Hd0 & _)
                        | (_ & Hcw & _ & _ & _ & _ & _ & _ & Hguard) ]);
    [exfalso; exact (Hd Hd0) |].
  destruct (Z.le_gt_cases (s_len st - s_drop st) (s_curr st)) as [Hok|Hbad];
    [exact Hok | exfalso].
  (* the window mass vanishes *)
  assert (Hwz : wmass (Z.to_nat (x_root c + s_curr st)) 1 (s_count st) = 0).
  { apply wmass_zero_on.
    intros i Hi.
    rewrite Z2Nat.id in Hi by (clear -Hroot Hcw; lia).
    rewrite (Hcnt i ltac:(clear -Hi Hcw Hroot; lia)).
    destruct (Z.ltb_spec i (s_len st)) as [_|Habs]; [reflexivity|].
    exfalso. clear -Hi Habs Hbad Hdr; lia. }
  rewrite Hwz, Z.add_0_r in Hguard.
  (* the position sits inside its unit *)
  assert (Hdec := zrev_decomp (x_root c) (s_len st) (s_huff st)
                    ltac:(clear -Hrl Hroot; lia) ltac:(clear -Hlen; lia)
                    ltac:(exact Hhuff)).
  set (P1 := zrev (Z.to_nat (x_root c)) (s_huff st mod 2 ^ x_root c)) in *.
  set (O1 := zrev (Z.to_nat (s_len st - x_root c))
               (Z.shiftr (s_huff st) (x_root c))) in *.
  assert (HO1 : 0 <= O1 < 2 ^ (s_len st - x_root c)).
  { unfold O1. split; [apply zrev_nonneg|].
    pose proof (zrev_lt (Z.to_nat (s_len st - x_root c))
                  (Z.shiftr (s_huff st) (x_root c))) as H.
    rewrite Z2Nat.id in H by (clear -Hrl; lia). exact H. }
  unfold UnitStart in Hguard.
  rewrite Hloweq in Hguard.
  fold P1 in Hguard.
  rewrite Hdec in Hpos.
  (* split the powers to align the two unit scales *)
  assert (Hq : 0 < 2 ^ (15 - s_len st))
    by (apply Z.pow_pos_nonneg; clear -Hlen; lia).
  assert (Hsp : 2 ^ (s_len st - x_root c) * 2 ^ (15 - s_len st)
                = 2 ^ (15 - x_root c)).
  { rewrite <- Z.pow_add_r by (clear -Hrl Hlen; lia).
    f_equal. clear; lia. }
  rewrite Z.mul_add_distr_r in Hpos.
  rewrite <- Z.mul_assoc, Hsp in Hpos.
  (* O1's mass stays strictly inside one unit *)
  assert (HO1m : O1 * 2 ^ (15 - s_len st)
                 <= (2 ^ (s_len st - x_root c) - 1) * 2 ^ (15 - s_len st))
    by (apply Z.mul_le_mono_nonneg_r; clear -HO1 Hq; lia).
  rewrite Z.mul_sub_distr_r, Z.mul_1_l, Hsp in HO1m.
  clear -Hguard Hpos HO1m Hq HO1; lia.
Qed.

(* ==========================================================================
   3.  gap_zeros — from the landed sort-window lemmas.
   ========================================================================== *)

Lemma gap_zeros_lem : forall c cnt0 st,
  CovCtxOk c cnt0 -> CovInv c cnt0 st ->
  step_hit st = true ->
  (step_hit st && (s_len st =? x_max c))%bool = false ->
  s_len st < step_len c st <= x_max c
  /\ (forall l, s_len st < l < step_len c st -> cnt0 l = 0).
Proof.
  intros c cnt0 st Hctx Hinv Hhit Hbrk.
  pose proof Hctx as Hctx2.
  destruct Hctx as (Hroot & Hmask & Hmx & Hmxnz & Hmxz & Hnn & Hcodes & Hlens
                    & Hcnt0 & Hwork & Hupper & Hcase & Hrootmx).
  destruct Hinv as (Hlen & Hhuff & HwinL & HwinU & Hcnt & Hpos & Hcov
                    & Hphase).
  (* the hit exhausts the current length's window *)
  assert (Hend : s_sym st + 1 = sw_offs cnt0 (s_len st) + cnt0 (s_len st)).
  { unfold step_hit, step_cnt in Hhit.
    rewrite zset_same in Hhit.
    apply Z.eqb_eq in Hhit.
    rewrite (Hcnt (s_len st) ltac:(clear -Hlen; lia)) in Hhit.
    rewrite Z.ltb_irrefl, Z.eqb_refl in Hhit.
    clear -Hhit; lia. }
  assert (Hnmx : s_len st <> x_max c).
  { rewrite Hhit in Hbrk. cbn [andb] in Hbrk.
    apply Z.eqb_neq in Hbrk. exact Hbrk. }
  (* there IS a next symbol, or max would be the finished length *)
  destruct (Z.lt_ge_cases (s_sym st + 1) (sw_offs cnt0 15 + cnt0 15))
    as [Hnext|Hgone].
  - destruct (cov_next_window c cnt0 (s_len st) (s_sym st) Hctx2
                ltac:(clear -Hlen; lia)
                ltac:(clear -HwinL HwinU; lia) Hend Hnext)
      as (l1 & Hl1 & Hstart & Hpos1 & Hlens1 & Hzero).
    assert (Hsl : step_len c st = l1)
      by (unfold step_len; rewrite Hhit; exact Hlens1).
    rewrite Hsl.
    split; [| exact Hzero].
    split; [clear -Hl1; lia |].
    (* l1 <= max: its count is positive, counts above max vanish *)
    destruct (Z.le_gt_cases l1 (x_max c)) as [Hle|Hgt]; [exact Hle|].
    exfalso.
    rewrite (Hmxz l1 ltac:(clear -Hgt Hl1; lia)) in Hpos1.
    clear -Hpos1; lia.
  - exfalso.
    destruct (cov_exhausted c cnt0 (s_len st) (s_sym st) Hctx2
                ltac:(clear -Hlen; lia)
                ltac:(clear -HwinL HwinU; lia) Hgone) as [_ Hmxe].
    exact (Hnmx (eq_sym Hmxe)).
Qed.

(* ==========================================================================
   4.  The accounting's step laws, and the ItCont inversion.
   ========================================================================== *)

(** Same length, one more consumed code: the accounting takes exactly
    one [chain_code]. *)
Lemma acct_tail : forall cnt0 R0 (st st' : ItSt),
  s_len st' = s_len st ->
  s_count st' (s_len st') = s_count st (s_len st) - 1 ->
  s_count st (s_len st) <= cnt0 (s_len st) ->
  aj_acct cnt0 R0 st'
  = chain_code (2 ^ (s_len st - R0)) (fst (aj_acct cnt0 R0 st))
      (snd (aj_acct cnt0 R0 st)).
Proof.
  intros cnt0 R0 st st' Hl Hc Hk.
  unfold aj_acct. cbv zeta.
  rewrite Hc, Hl.
  replace (Z.to_nat (cnt0 (s_len st) - (s_count st (s_len st) - 1)))
    with (S (Z.to_nat (cnt0 (s_len st) - s_count st (s_len st))))
    by (clear -Hk; lia).
  apply chain_codes_tail.
Qed.

(** A length jump across a zero-count gap, the old length's last code
    consumed on the way out: one [chain_code], then the descend/gap
    telescoping in closed form. *)
Lemma acct_jump : forall cnt0 R0 (st st' : ItSt),
  R0 + 1 <= s_len st ->
  s_len st < s_len st' ->
  s_count st (s_len st) = 1 ->
  s_count st (s_len st) <= cnt0 (s_len st) ->
  s_count st' (s_len st') = cnt0 (s_len st') ->
  (forall l, s_len st < l < s_len st' -> cnt0 l = 0) ->
  aj_acct cnt0 R0 st'
  = (fst (chain_code (2 ^ (s_len st - R0)) (fst (aj_acct cnt0 R0 st))
            (snd (aj_acct cnt0 R0 st)))
       + (if snd (chain_code (2 ^ (s_len st - R0)) (fst (aj_acct cnt0 R0 st))
                    (snd (aj_acct cnt0 R0 st))) =? 0
          then 0 else 2 ^ (s_len st' - R0) - 2 ^ (s_len st - R0)),
     snd (chain_code (2 ^ (s_len st - R0)) (fst (aj_acct cnt0 R0 st))
            (snd (aj_acct cnt0 R0 st))) * 2 ^ (s_len st' - s_len st)).
Proof.
  intros cnt0 R0 st st' Hphase Hjump Hone Hk Hfresh Hgap.
  set (SB := 2 ^ (s_len st - R0)) in *.
  (* the new accounting is the bare boundary replay *)
  assert (Hacct' : aj_acct cnt0 R0 st' = chain_at cnt0 R0 (s_len st')).
  { unfold aj_acct. cbv zeta.
    rewrite Hfresh, Z.sub_diag.
    change (Z.to_nat 0) with 0%nat.
    cbn [chain_codes].
    destruct (chain_at cnt0 R0 (s_len st')) as [m r]. reflexivity. }
  rewrite Hacct'.
  (* the boundary replay telescopes: step at the old length, gap after *)
  set (CC := chain_code SB (fst (aj_acct cnt0 R0 st))
               (snd (aj_acct cnt0 R0 st))) in *.
  assert (Hstep1 : chain_at cnt0 R0 (s_len st + 1)
                   = chain_descend SB (fst CC) (snd CC)).
  { rewrite chain_at_step by (clear -Hphase; lia).
    cbv zeta. fold SB.
    replace (Z.to_nat (cnt0 (s_len st)))
      with (S (Z.to_nat (cnt0 (s_len st) - s_count st (s_len st))))
      by (clear -Hone Hk; lia).
    rewrite chain_codes_tail.
    unfold CC, aj_acct. cbv zeta. fold SB.
    destruct (chain_code SB
                (fst (chain_codes
                        (Z.to_nat (cnt0 (s_len st) - s_count st (s_len st)))
                        SB (fst (chain_at cnt0 R0 (s_len st)))
                        (snd (chain_at cnt0 R0 (s_len st)))))
                (snd (chain_codes
                        (Z.to_nat (cnt0 (s_len st) - s_count st (s_len st)))
                        SB (fst (chain_at cnt0 R0 (s_len st)))
                        (snd (chain_at cnt0 R0 (s_len st))))))
      as [m2 r2].
    reflexivity. }
  assert (Hg : chain_at cnt0 R0 (s_len st')
               = (fst (chain_at cnt0 R0 (s_len st + 1))
                    + (if snd (chain_at cnt0 R0 (s_len st + 1)) =? 0
                       then 0
                       else 2 ^ (s_len st' - R0) - 2 ^ (s_len st + 1 - R0)),
                  snd (chain_at cnt0 R0 (s_len st + 1))
                    * 2 ^ Z.of_nat (Z.to_nat (s_len st' - (s_len st + 1))))).
  { replace (s_len st')
      with ((s_len st + 1) + Z.of_nat (Z.to_nat (s_len st' - (s_len st + 1))))
      at 1 by (rewrite Z2Nat.id by (clear -Hjump; lia); clear; lia).
    rewrite (chain_gap cnt0 R0 (s_len st + 1) _ ltac:(clear -Hphase; lia)).
    2:{ intros l Hl.
        rewrite Z2Nat.id in Hl by (clear -Hjump; lia).
        apply Hgap. clear -Hl; lia. }
    rewrite Z2Nat.id by (clear -Hjump; lia).
    replace (s_len st + 1 + (s_len st' - (s_len st + 1))) with (s_len st')
      by (clear; lia).
    reflexivity. }
  rewrite Hg, Hstep1.
  unfold chain_descend. cbn [fst snd].
  rewrite Z2Nat.id by (clear -Hjump; lia).
  assert (HSBp : 0 < SB)
    by (unfold SB; apply Z.pow_pos_nonneg; clear -Hphase; lia).
  assert (Hpow : 2 ^ (s_len st + 1 - R0) = 2 * SB).
  { unfold SB.
    replace (s_len st + 1 - R0) with (1 + (s_len st - R0)) by (clear; lia).
    rewrite Z.pow_add_r by (clear -Hphase; lia).
    change (2 ^ 1) with 2. reflexivity. }
  assert (Hpow2 : 2 ^ (s_len st' - s_len st)
                  = 2 * 2 ^ (s_len st' - (s_len st + 1))).
  { replace (s_len st' - s_len st)
      with (1 + (s_len st' - (s_len st + 1))) by (clear; lia).
    rewrite Z.pow_add_r by (clear -Hjump; lia).
    change (2 ^ 1) with 2. reflexivity. }
  destruct (Z.eqb_spec (snd CC) 0) as [Hr0 | Hrne].
  - rewrite Hr0. change (2 * 0) with 0.
    change (0 =? 0) with true. cbv iota.
    rewrite Z.mul_0_l.
    apply (f_equal2 (@pair Z Z)); [clear; lia | clear; lia].
  - destruct (Z.eqb_spec (2 * snd CC) 0) as [Habs | _];
      [exfalso; clear -Habs Hrne; lia|].
    apply (f_equal2 (@pair Z Z)).
    + rewrite Hpow. clear; lia.
    + rewrite Hpow2. clear; lia.
Qed.

(** Inversion of a continuing trip into the two anatomy shapes. *)
Lemma it_step_cont_inv : forall c st st',
  it_step c st = ItCont st' ->
  (step_hit st && (s_len st =? x_max c))%bool = false
  /\ ( (open_guard c st = false /\ st' = step_noopen_st c st)
       \/ (open_guard c st = true
           /\ it_enough (x_type c) (open_used c st) = false
           /\ st' = step_open_st c st) ).
Proof.
  intros c st st' H.
  destruct ((step_hit st && (s_len st =? x_max c))%bool) eqn:Hbrk.
  { apply andb_true_iff in Hbrk. destruct Hbrk as [Hh Hm].
    rewrite (it_step_break_eq c st Hh Hm) in H. discriminate H. }
  split; [reflexivity|].
  destruct (open_guard c st) eqn:Hop.
  - destruct (it_enough (x_type c) (open_used c st)) eqn:Hen.
    + rewrite (it_step_overflow_eq c st Hbrk Hop Hen) in H. discriminate H.
    + rewrite (it_step_opencont_eq c st Hbrk Hop Hen) in H.
      injection H as <-. right. auto.
  - rewrite (it_step_noopen_eq c st Hbrk Hop) in H.
    injection H as <-. left. auto.
Qed.

(* ==========================================================================
   5.  AJP — the rem-position clause, and the offset law at a step.
   ========================================================================== *)

(** The accounting's rem IS the room left in the unit (mod one full
    unit: a fresh boundary reads 0). *)
Definition AJP (cnt0 : zarr) (R0 : Z) (st : ItSt) : Prop :=
  s_drop st = 0
  \/ snd (aj_acct cnt0 R0 st) = aj_left R0 st mod 2 ^ (s_len st - R0).

(** The new length never shrinks, and stays in range. *)
Lemma step_len_range : forall c cnt0 st,
  CovCtxOk c cnt0 -> CovInv c cnt0 st ->
  (step_hit st && (s_len st =? x_max c))%bool = false ->
  s_len st <= step_len c st /\ step_len c st <= 15.
Proof.
  intros c cnt0 st Hctx Hinv Hbrk.
  destruct (step_hit st) eqn:Hhit.
  - destruct (gap_zeros_lem c cnt0 st Hctx Hinv Hhit
                ltac:(rewrite Hhit; exact Hbrk)) as [Hr _].
    destruct Hctx as (_ & _ & Hmx & _).
    clear -Hr Hmx; lia.
  - unfold step_len. rewrite Hhit.
    destruct Hinv as (Hlen & _).
    clear -Hlen; lia.
Qed.

(** The offset law at a phase-2 step, resolved against the open test:
    a closed trip advances the offset inside the unit, an open trip
    carries out of a fully-swept unit. *)
Lemma off_step_facts : forall c cnt0 st,
  CovCtxOk c cnt0 -> CovInv c cnt0 st ->
  (step_hit st && (s_len st =? x_max c))%bool = false ->
  s_drop st <> 0 ->
  0 <= step_huff st < 2 ^ s_len st
  /\ ( (open_guard c st = false
        /\ zrev (Z.to_nat (s_len st - x_root c))
             (Z.shiftr (step_huff st) (x_root c))
           = zrev (Z.to_nat (s_len st - x_root c))
               (Z.shiftr (s_huff st) (x_root c)) + 1)
       \/ (open_guard c st = true
           /\ zrev (Z.to_nat (s_len st - x_root c))
                (Z.shiftr (s_huff st) (x_root c))
              = 2 ^ (s_len st - x_root c) - 1
           /\ zrev (Z.to_nat (s_len st - x_root c))
                (Z.shiftr (step_huff st) (x_root c)) = 0) ).
Proof.
  intros c cnt0 st Hctx Hinv Hbrk Hd.
  pose proof (step_len_range c cnt0 st Hctx Hinv Hbrk) as [Hsl _].
  destruct Hctx as (Hroot & Hmask & Hmx & Hmxnz & Hmxz & Hnn & Hcodes & Hlens
                    & Hcnt0 & Hwork & Hupper & Hcase & Hrootmx).
  destruct Hinv as (Hlen & Hhuff & HwinL & HwinU & Hcnt & Hpos & Hcov
                    & Hphase).
  destruct Hphase as [ (Hd0 & _) | (Hdr & Hrl & Hnx & Hloweq & _) ];
    [exfalso; exact (Hd Hd0) |].
  (* the guard's first conjunct is true in phase 2 *)
  assert (Hltb : (x_root c <? step_len c st) = true)
    by (apply Z.ltb_lt; clear -Hrl Hsl; lia).
  assert (Hgeq : open_guard c st
                 = negb (Z.land (step_huff st) (x_mask c) =? s_low st))
    by (unfold open_guard; rewrite Hltb; cbn [andb]; reflexivity).
  (* the increment law *)
  assert (Hhuff' : 0 <= s_huff st < 2 ^ Z.of_nat (Z.to_nat (s_len st)))
    by (rewrite Z2Nat.id by (clear -Hlen; lia); exact Hhuff).
  pose proof (zrev_it_rev_incr (Z.to_nat (s_len st)) (s_huff st)
                ltac:(clear -Hlen; lia) Hhuff') as Hinc.
  rewrite Z2Nat.id in Hinc by (clear -Hlen; lia).
  assert (Hshb : step_huff st = it_rev_incr (s_huff st) (s_len st))
    by reflexivity.
  destruct Hinc as [[Hw Hz] | [Hb Hgood]].
  - (* wrap: all-ones counter, the last slot of the last unit *)
    destruct (off_wrap_split (x_root c) (s_len st) (s_huff st)
                ltac:(clear -Hroot Hrl; lia) ltac:(clear -Hlen; lia)
                Hhuff Hz) as [Hpre Hoff].
    assert (Hh'0 : step_huff st = 0) by (rewrite Hshb; exact Hw).
    assert (Hp2 : 0 < 2 ^ x_root c)
      by (apply Z.pow_pos_nonneg; clear -Hroot; lia).
    assert (Hgt : open_guard c st = true).
    { rewrite Hgeq, Hh'0, Z.land_0_l, Hloweq, Hpre.
      destruct (Z.eqb_spec 0 (2 ^ x_root c - 1)) as [Habs|_];
        [exfalso; clear -Habs Hp2 Hroot|reflexivity].
      assert (2 ^ 1 <= 2 ^ x_root c)
        by (apply Z.pow_le_mono_r; clear -Hroot; lia).
      clear -Habs H; lia. }
    split.
    { rewrite Hh'0. split; [clear; lia|].
      apply Z.pow_pos_nonneg; clear -Hlen; lia. }
    right. split; [exact Hgt|]. split; [exact Hoff|].
    rewrite Hh'0, Z.shiftr_0_l. apply zrev_zero.
  - (* the counter advanced by one *)
    rewrite <- Hshb in Hb, Hgood.
    destruct (off_incr_split (x_root c) (s_len st) (s_huff st) (step_huff st)
                ltac:(clear -Hroot Hrl; lia) ltac:(clear -Hlen; lia)
                Hhuff Hb Hgood) as [[Hsame Hadv] | (Hne & Hlast & Hzero)].
    + (* same prefix: the guard stays closed *)
      assert (Hgf : open_guard c st = false).
      { rewrite Hgeq, Hmask.
        rewrite (land_mask_mod (x_root c) (step_huff st)
                   ltac:(clear -Hroot; lia) ltac:(clear -Hb; lia)).
        rewrite Hsame, <- Hloweq, Z.eqb_refl. reflexivity. }
      split; [exact Hb|]. left. split; [exact Hgf | exact Hadv].
    + (* carry: the guard opens *)
      assert (Hgt : open_guard c st = true).
      { rewrite Hgeq, Hmask.
        rewrite (land_mask_mod (x_root c) (step_huff st)
                   ltac:(clear -Hroot; lia) ltac:(clear -Hb; lia)).
        rewrite Hloweq.
        destruct (Z.eqb_spec (step_huff st mod 2 ^ x_root c)
                    (s_huff st mod 2 ^ x_root c)) as [Habs|_];
          [exfalso; exact (Hne Habs) | reflexivity]. }
      split; [exact Hb|]. right. auto.
Qed.

Lemma step_huff_bounds : forall st,
  1 <= s_len st <= 15 -> 0 <= s_huff st < 2 ^ s_len st ->
  0 <= step_huff st < 2 ^ s_len st.
Proof.
  intros st Hl Hh.
  assert (Hh' : 0 <= s_huff st < 2 ^ Z.of_nat (Z.to_nat (s_len st)))
    by (rewrite Z2Nat.id by (clear -Hl; lia); exact Hh).
  pose proof (zrev_it_rev_incr (Z.to_nat (s_len st)) (s_huff st)
                ltac:(clear -Hl; lia) Hh') as Hinc.
  rewrite Z2Nat.id in Hinc by (clear -Hl; lia).
  destruct Hinc as [[Hw _] | [Hb _]].
  - change (step_huff st) with (it_rev_incr (s_huff st) (s_len st)).
    rewrite Hw.
    split; [clear; lia | apply Z.pow_pos_nonneg; clear -Hl; lia].
  - exact Hb.
Qed.

(** The accounting rem at a phase-2 open trip: exactly one slot left. *)
Lemma aj_rem_one_at_open : forall c cnt0 R0 st,
  x_root c = R0 ->
  CovCtxOk c cnt0 -> CovInv c cnt0 st ->
  AJP cnt0 R0 st ->
  s_drop st <> 0 ->
  (step_hit st && (s_len st =? x_max c))%bool = false ->
  open_guard c st = true ->
  snd (aj_acct cnt0 R0 st) = 1.
Proof.
  intros c cnt0 R0 st HR Hctx Hinv HAJP Hd Hbrk Hop.
  subst R0.
  destruct HAJP as [Habs | HAJP]; [exfalso; exact (Hd Habs)|].
  destruct (off_step_facts c cnt0 st Hctx Hinv Hbrk Hd)
    as (Hb' & [(Hgf & _) | (_ & Hlast & _)]);
    [rewrite Hop in Hgf; discriminate Hgf|].
  destruct Hinv as (Hlen & Hhuff & _ & _ & _ & _ & _ & Hphase).
  destruct Hphase as [ (Habs & _) | (Hdr & Hrl & _) ];
    [exfalso; exact (Hd Habs)|].
  rewrite HAJP.
  unfold aj_left, aj_off.
  rewrite Hlast.
  replace (2 ^ (s_len st - x_root c) - (2 ^ (s_len st - x_root c) - 1))
    with 1 by (clear; lia).
  apply Z.mod_small.
  assert (2 ^ 1 <= 2 ^ (s_len st - x_root c))
    by (apply Z.pow_le_mono_r; clear -Hrl; lia).
  clear -H; lia.
Qed.

(* ==========================================================================
   6.  AJP preservation across any continuing trip.
   ========================================================================== *)

Theorem ajp_cont : forall c cnt0 R0 st st',
  x_root c = R0 ->
  CovCtxOk c cnt0 -> CovInv c cnt0 st ->
  AJP cnt0 R0 st ->
  it_step c st = ItCont st' ->
  AJP cnt0 R0 st'.
Proof.
  intros c cnt0 R0 st st' HR Hctx Hinv HAJP Hstep.
  subst R0.
  destruct (it_step_cont_inv c st st' Hstep) as [Hbrk Harm].
  pose proof Hctx as Hctx2.
  pose proof Hinv as Hinv2.
  destruct Hctx as (Hroot & Hmask & Hmx & Hmxnz & Hmxz & Hnn & Hcodes & Hlens
                    & Hcnt0 & Hwork & Hupper & Hcase & Hrootmx).
  destruct Hinv as (Hlen & Hhuff & HwinL & HwinU & Hcnt & Hpos & Hcov
                    & Hphase).
  assert (Hk : s_count st (s_len st) <= cnt0 (s_len st)).
  { rewrite (Hcnt (s_len st) ltac:(clear -Hlen; lia)).
    rewrite Z.ltb_irrefl, Z.eqb_refl.
    clear -HwinL; lia. }
  assert (Hb' : 0 <= step_huff st < 2 ^ s_len st)
    by (apply step_huff_bounds; [exact Hlen | exact Hhuff]).
  destruct Harm as [ (Hop & ->) | (Hop & Hen & ->) ].
  - (* ------------------------------ NOOPEN ------------------------------ *)
    destruct (Z.eq_dec (s_drop st) 0) as [Hd0 | Hd].
    + left. cbn [step_noopen_st s_drop]. exact Hd0.
    + right.
      destruct HAJP as [Habs | HAJP]; [exfalso; exact (Hd Habs)|].
      destruct (off_step_facts c cnt0 st Hctx2 Hinv2 Hbrk Hd)
        as (_ & [(_ & Hadv) | (Hgt & _ & _)]);
        [| rewrite Hop in Hgt; discriminate Hgt].
      destruct Hphase as [ (Habs & _) | (Hdr & Hrl & _) ];
        [exfalso; exact (Hd Habs)|].
      assert (Hd1 : 1 <= s_len st - x_root c) by (clear -Hrl; lia).
      assert (H2d : 2 <= 2 ^ (s_len st - x_root c)).
      { pose proof (Z.pow_le_mono_r 2 1 (s_len st - x_root c)
                      ltac:(clear; lia) ltac:(clear -Hd1; lia)) as H.
        clear -H; lia. }
      assert (HOFF : 0 <= zrev (Z.to_nat (s_len st - x_root c))
                            (Z.shiftr (s_huff st) (x_root c))
                     < 2 ^ (s_len st - x_root c)).
      { split; [apply zrev_nonneg|].
        pose proof (zrev_lt (Z.to_nat (s_len st - x_root c))
                      (Z.shiftr (s_huff st) (x_root c))) as H.
        rewrite Z2Nat.id in H by (clear -Hd1; lia). exact H. }
      assert (HOFF' : 0 <= zrev (Z.to_nat (s_len st - x_root c))
                             (Z.shiftr (step_huff st) (x_root c))
                      < 2 ^ (s_len st - x_root c)).
      { split; [apply zrev_nonneg|].
        pose proof (zrev_lt (Z.to_nat (s_len st - x_root c))
                      (Z.shiftr (step_huff st) (x_root c))) as H.
        rewrite Z2Nat.id in H by (clear -Hd1; lia). exact H. }
      unfold aj_left, aj_off in HAJP.
      set (OFF := zrev (Z.to_nat (s_len st - x_root c))
                    (Z.shiftr (s_huff st) (x_root c))) in *.
      set (OFF' := zrev (Z.to_nat (s_len st - x_root c))
                     (Z.shiftr (step_huff st) (x_root c))) in *.
      destruct (step_hit st) eqn:Hhit.
      * (* hit inside the unit: the offset widens by the jump *)
        assert (Hbrk2 : (step_hit st && (s_len st =? x_max c))%bool = false)
          by (rewrite Hhit; exact Hbrk).
        destruct (gap_zeros_lem c cnt0 st Hctx2 Hinv2 Hhit Hbrk2)
          as [[Hjl Hjmx] Hgz].
        assert (Hone : s_count st (s_len st) = 1).
        { unfold step_hit, step_cnt in Hhit.
          rewrite zset_same in Hhit.
          apply Z.eqb_eq in Hhit. clear -Hhit; lia. }
        assert (Hsl' : s_len (step_noopen_st c st) = step_len c st)
          by reflexivity.
        assert (Hfresh : s_count (step_noopen_st c st)
                           (s_len (step_noopen_st c st))
                         = cnt0 (s_len (step_noopen_st c st))).
        { cbn [step_noopen_st s_count s_len].
          unfold step_cnt.
          rewrite zset_other by (clear -Hjl; lia).
          rewrite (Hcnt (step_len c st) ltac:(clear -Hjl Hjmx Hmx Hlen; lia)).
          destruct (Z.ltb_spec (step_len c st) (s_len st)) as [Habs|_];
            [exfalso; clear -Habs Hjl; lia|].
          destruct (Z.eqb_spec (step_len c st) (s_len st)) as [Habs|_];
            [exfalso; clear -Habs Hjl; lia|].
          reflexivity. }
        rewrite (acct_jump cnt0 (x_root c) st (step_noopen_st c st)
                   ltac:(clear -Hrl; lia)
                   ltac:(rewrite Hsl'; exact Hjl)
                   Hone Hk Hfresh
                   ltac:(rewrite Hsl'; exact Hgz)).
        cbn [snd].
        rewrite Hsl'.
        unfold aj_left, aj_off.
        rewrite Hsl'.
        cbn [step_noopen_st s_huff].
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
        fold OFF'.
        rewrite Hadv, HAJP.
        assert (Hpw : 2 ^ (s_len st - x_root c)
                        * 2 ^ (step_len c st - s_len st)
                      = 2 ^ (step_len c st - x_root c)).
        { rewrite <- Z.pow_add_r by (clear -Hd1 Hjl; lia).
          f_equal. clear; lia. }
        assert (HQ : 0 < 2 ^ (step_len c st - s_len st))
          by (apply Z.pow_pos_nonneg; clear -Hjl; lia).
        destruct (Z.eq_dec OFF 0) as [HO0 | HOpos].
        -- (* unit start: the accounting table was exactly full *)
           rewrite HO0, Z.sub_0_r, Z.mod_same by (clear -H2d; lia).
           unfold chain_code.
           change (0 =? 0) with true. cbv iota. cbn [snd].
           rewrite Z.add_0_l, Z.mul_1_l.
           rewrite Z.mul_sub_distr_r, Z.mul_1_l, Hpw.
           assert (H2Q : 2 * 2 ^ (step_len c st - s_len st)
                         <= 2 ^ (s_len st - x_root c)
                            * 2 ^ (step_len c st - s_len st))
             by (apply Z.mul_le_mono_nonneg_r; clear -H2d HQ; lia).
           rewrite Hpw in H2Q.
           rewrite Z.mod_small by (clear -HQ H2Q; lia).
           reflexivity.
        -- (* mid-unit: one slot consumed *)
           rewrite (Z.mod_small (2 ^ (s_len st - x_root c) - OFF)
                      (2 ^ (s_len st - x_root c)))
             by (clear -HOpos HOFF; lia).
           unfold chain_code.
           destruct (Z.eqb_spec (2 ^ (s_len st - x_root c) - OFF) 0)
             as [Habs|_]; [exfalso; clear -Habs HOFF; lia|].
           cbn [snd].
           assert (HB : (OFF + 1) * 2 ^ (step_len c st - s_len st)
                        <= 2 ^ (s_len st - x_root c)
                           * 2 ^ (step_len c st - s_len st))
             by (apply Z.mul_le_mono_nonneg_r; clear -HOFF' Hadv HQ; lia).
           rewrite Z.mul_add_distr_r, Z.mul_1_l in HB.
           rewrite Hpw in HB.
           assert (HOQ : 0 <= OFF * 2 ^ (step_len c st - s_len st))
             by (apply Z.mul_nonneg_nonneg; clear -HOpos HOFF HQ; lia).
           rewrite Z.mul_add_distr_r, Z.mul_1_l.
           rewrite !Z.mul_sub_distr_r, Z.mul_1_l, Hpw.
           rewrite Z.mod_small by (clear -HOQ HB HQ; lia).
           clear; lia.
      * (* same length, same unit: one code consumed *)
        assert (Hsl2 : s_len (step_noopen_st c st) = s_len st)
          by (cbn [step_noopen_st s_len]; unfold step_len;
              rewrite Hhit; reflexivity).
        assert (Hcc : s_count (step_noopen_st c st)
                        (s_len (step_noopen_st c st))
                      = s_count st (s_len st) - 1).
        { rewrite Hsl2. cbn [step_noopen_st s_count].
          unfold step_cnt. apply zset_same. }
        rewrite (acct_tail cnt0 (x_root c) st (step_noopen_st c st)
                   Hsl2 Hcc Hk).
        unfold aj_left, aj_off.
        rewrite Hsl2.
        cbn [step_noopen_st s_huff].
        fold OFF'.
        rewrite Hadv, HAJP.
        destruct (Z.eq_dec OFF 0) as [HO0 | HOpos].
        -- rewrite HO0, Z.sub_0_r, Z.mod_same by (clear -H2d; lia).
           unfold chain_code.
           change (0 =? 0) with true. cbv iota. cbn [snd].
           rewrite Z.mod_small by (clear -H2d; lia).
           clear; lia.
        -- rewrite (Z.mod_small (2 ^ (s_len st - x_root c) - OFF)
                      (2 ^ (s_len st - x_root c)))
             by (clear -HOpos HOFF; lia).
           unfold chain_code.
           destruct (Z.eqb_spec (2 ^ (s_len st - x_root c) - OFF) 0)
             as [Habs|_]; [exfalso; clear -Habs HOFF; lia|].
           cbn [snd].
           rewrite Z.mod_small by (clear -Hadv HOFF' HOFF; lia).
           clear; lia.
  - (* ------------------------------- OPEN ------------------------------- *)
    right.
    destruct (Z.eq_dec (s_drop st) 0) as [Hd0 | Hd].
    + (* first open: a fresh boundary at the first over-root length *)
      destruct Hphase as [ (_ & Hcurr0 & Hnx0 & Hlow0 & Hlenroot)
                         | (Hdr & _) ];
        [| exfalso; rewrite Hd0 in Hdr; clear -Hdr Hroot; lia].
      assert (HrSL : x_root c < step_len c st).
      { unfold open_guard in Hop.
        apply andb_true_iff in Hop. destruct Hop as [Hltb _].
        apply Z.ltb_lt in Hltb. exact Hltb. }
      destruct (step_hit st) eqn:Hhit.
      2:{ exfalso. unfold step_len in HrSL. rewrite Hhit in HrSL.
          cbv iota in HrSL. clear -HrSL Hlenroot; lia. }
      assert (Hbrk2 : (step_hit st && (s_len st =? x_max c))%bool = false)
        by (rewrite Hhit; exact Hbrk).
      destruct (gap_zeros_lem c cnt0 st Hctx2 Hinv2 Hhit Hbrk2)
        as [[Hjl Hjmx] Hgz].
      assert (Hacct' : aj_acct cnt0 (x_root c) (step_open_st c st)
                       = chain_at cnt0 (x_root c) (step_len c st)).
      { unfold aj_acct. cbv zeta.
        cbn [step_open_st s_len s_count].
        unfold step_cnt.
        rewrite zset_other by (clear -Hjl; lia).
        rewrite (Hcnt (step_len c st) ltac:(clear -Hjl Hjmx Hmx Hlen; lia)).
        destruct (Z.ltb_spec (step_len c st) (s_len st)) as [Habs|_];
          [exfalso; clear -Habs Hjl; lia|].
        destruct (Z.eqb_spec (step_len c st) (s_len st)) as [Habs|_];
          [exfalso; clear -Habs Hjl; lia|].
        rewrite Z.sub_diag. change (Z.to_nat 0) with 0%nat.
        cbn [chain_codes].
        destruct (chain_at cnt0 (x_root c) (step_len c st)) as [m r].
        reflexivity. }
      assert (Hseed : snd (chain_at cnt0 (x_root c) (step_len c st)) = 0).
      { replace (step_len c st)
          with ((x_root c + 1)
                + Z.of_nat (Z.to_nat (step_len c st - x_root c - 1)))
          by (rewrite Z2Nat.id by (clear -HrSL; lia); clear; lia).
        rewrite (chain_gap cnt0 (x_root c) (x_root c + 1) _
                   ltac:(clear; lia)).
        2:{ intros l Hl.
            rewrite Z2Nat.id in Hl by (clear -HrSL; lia).
            apply Hgz. clear -Hl Hlenroot; lia. }
        cbn [snd].
        rewrite chain_at_seed by (clear; lia).
        cbn [snd]. apply Z.mul_0_l. }
      rewrite Hacct', Hseed.
      unfold aj_left, aj_off.
      cbn [step_open_st s_len s_huff].
      assert (Hsh0 : Z.shiftr (step_huff st) (x_root c) = 0).
      { rewrite Z.shiftr_div_pow2 by (clear -Hroot; lia).
        apply Z.div_small.
        split; [clear -Hb'; lia|].
        assert (2 ^ s_len st <= 2 ^ x_root c)
          by (apply Z.pow_le_mono_r; clear -Hlenroot; lia).
        clear -Hb' H; lia. }
      rewrite Hsh0, zrev_zero, Z.sub_0_r.
      rewrite Z.mod_same; [reflexivity|].
      assert (0 < 2 ^ (step_len c st - x_root c))
        by (apply Z.pow_pos_nonneg; clear -HrSL; lia).
      clear -H; lia.
    + (* phase-2 open: the unit was fully swept, a fresh one begins *)
      destruct HAJP as [Habs | HAJP]; [exfalso; exact (Hd Habs)|].
      destruct (off_step_facts c cnt0 st Hctx2 Hinv2 Hbrk Hd)
        as (_ & [(Hgf & _) | (_ & Hlast & Hzero)]);
        [rewrite Hop in Hgf; discriminate Hgf|].
      destruct Hphase as [ (Habs & _) | (Hdr & Hrl & _) ];
        [exfalso; exact (Hd Habs)|].
      assert (Hd1 : 1 <= s_len st - x_root c) by (clear -Hrl; lia).
      assert (H2d : 2 <= 2 ^ (s_len st - x_root c)).
      { pose proof (Z.pow_le_mono_r 2 1 (s_len st - x_root c)
                      ltac:(clear; lia) ltac:(clear -Hd1; lia)) as H.
        clear -H; lia. }
      unfold aj_left, aj_off in HAJP.
      rewrite Hlast in HAJP.
      replace (2 ^ (s_len st - x_root c) - (2 ^ (s_len st - x_root c) - 1))
        with 1 in HAJP by (clear; lia).
      rewrite Z.mod_small in HAJP by (clear -H2d; lia).
      destruct (step_hit st) eqn:Hhit.
      * (* hit-open: length jump onto the fresh boundary *)
        assert (Hbrk2 : (step_hit st && (s_len st =? x_max c))%bool = false)
          by (rewrite Hhit; exact Hbrk).
        destruct (gap_zeros_lem c cnt0 st Hctx2 Hinv2 Hhit Hbrk2)
          as [[Hjl Hjmx] Hgz].
        assert (Hone : s_count st (s_len st) = 1).
        { unfold step_hit, step_cnt in Hhit.
          rewrite zset_same in Hhit.
          apply Z.eqb_eq in Hhit. clear -Hhit; lia. }
        assert (Hsl' : s_len (step_open_st c st) = step_len c st)
          by reflexivity.
        assert (Hfresh : s_count (step_open_st c st)
                           (s_len (step_open_st c st))
                         = cnt0 (s_len (step_open_st c st))).
        { cbn [step_open_st s_count s_len].
          unfold step_cnt.
          rewrite zset_other by (clear -Hjl; lia).
          rewrite (Hcnt (step_len c st) ltac:(clear -Hjl Hjmx Hmx Hlen; lia)).
          destruct (Z.ltb_spec (step_len c st) (s_len st)) as [Habs|_];
            [exfalso; clear -Habs Hjl; lia|].
          destruct (Z.eqb_spec (step_len c st) (s_len st)) as [Habs|_];
            [exfalso; clear -Habs Hjl; lia|].
          reflexivity. }
        rewrite (acct_jump cnt0 (x_root c) st (step_open_st c st)
                   ltac:(clear -Hrl; lia)
                   ltac:(rewrite Hsl'; exact Hjl)
                   Hone Hk Hfresh
                   ltac:(rewrite Hsl'; exact Hgz)).
        cbn [snd].
        rewrite HAJP.
        unfold chain_code.
        change (1 =? 0) with false. cbv iota. cbn [snd].
        replace (1 - 1) with 0 by (clear; lia).
        rewrite Z.mul_0_l.
        unfold aj_left, aj_off.
        rewrite Hsl'.
        cbn [step_open_st s_huff].
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
        rewrite Hzero, Z.mul_0_l, Z.sub_0_r.
        rewrite Z.mod_same; [reflexivity|].
        assert (0 < 2 ^ (step_len c st - x_root c))
          by (apply Z.pow_pos_nonneg; clear -Hjl Hrl; lia).
        clear -H; lia.
      * (* mid-run open: same length, the next unit begins *)
        assert (Hsl2 : s_len (step_open_st c st) = s_len st)
          by (cbn [step_open_st s_len]; unfold step_len;
              rewrite Hhit; reflexivity).
        assert (Hcc : s_count (step_open_st c st)
                        (s_len (step_open_st c st))
                      = s_count st (s_len st) - 1).
        { rewrite Hsl2. cbn [step_open_st s_count].
          unfold step_cnt. apply zset_same. }
        rewrite (acct_tail cnt0 (x_root c) st (step_open_st c st)
                   Hsl2 Hcc Hk).
        rewrite HAJP.
        unfold chain_code.
        change (1 =? 0) with false. cbv iota. cbn [snd].
        unfold aj_left, aj_off.
        rewrite Hsl2.
        cbn [step_open_st s_huff].
        rewrite Hzero, Z.sub_0_r.
        rewrite Z.mod_same by (clear -H2d; lia).
        clear; lia.
Qed.
