(** * EnoughFitsB4 — B-cluster session 4: the gap law, no-open
    preservation on AJ2, and the hit-trip telescoping (g6-bound lane).

    The hit lemma consumes two WINDOW-DIGESTED premises (the zrev-wall
    supplier family, session 5): Hgeo (an open table's length has not
    passed its lookahead depth) and P2 (a table that fills does so at
    its depth).  The earlier P3 candidate ("touched-full takes no
    code") proved UNNECESSARY: the accounting telescopes even there —
    the DP opens a parallel table, over-accounting in the safe
    direction.

    f1: open_curr remains the sole it_subsz carrier. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Inftrees ItGTblGeom ItGTblCover ItGSubCover.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7Strict.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughDP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughFitsDesign EnoughFitsA12 EnoughFitsB1
  EnoughFitsB2 EnoughFitsB3.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  The gap law.
   ========================================================================== *)

Lemma chain_gap : forall cnt rt a n,
  rt + 1 <= a ->
  (forall l, a <= l < a + Z.of_nat n -> cnt l = 0) ->
  chain_at cnt rt (a + Z.of_nat n)
  = (fst (chain_at cnt rt a)
       + (if snd (chain_at cnt rt a) =? 0 then 0
          else 2 ^ (a + Z.of_nat n - rt) - 2 ^ (a - rt)),
     snd (chain_at cnt rt a) * 2 ^ Z.of_nat n).
Proof.
  intros cnt rt a n Ha Hz.
  induction n as [|n IH].
  - rewrite Z.add_0_r.
    destruct (chain_at cnt rt a) as [m r]. cbn [fst snd].
    rewrite Z.pow_0_r, Z.mul_1_r.
    destruct (Z.eqb_spec r 0) as [->|Hr].
    + change (0 =? 0) with true. cbv iota.
      f_equal. clear; lia.
    + replace (r =? 0) with false
        by (symmetry; apply Z.eqb_neq; exact Hr).
      cbv iota. f_equal. clear; lia.
  - replace (a + Z.of_nat (S n)) with ((a + Z.of_nat n) + 1)
      by (rewrite Nat2Z.inj_succ; clear; lia).
    rewrite chain_at_step by (clear -Ha; lia).
    cbv zeta.
    rewrite IH by (intros l Hl; apply Hz;
                   rewrite Nat2Z.inj_succ; clear -Hl; lia).
    cbn [fst snd].
    rewrite (Hz (a + Z.of_nat n))
      by (rewrite Nat2Z.inj_succ; clear; lia).
    change (Z.to_nat 0) with O. cbn [chain_codes].
    unfold chain_descend.
    destruct (chain_at cnt rt a) as [m r]. cbn [fst snd].
    assert (Hpn : 0 < 2 ^ Z.of_nat n)
      by (apply Z.pow_pos_nonneg; clear; lia).
    destruct (Z.eqb_spec r 0) as [->|Hr].
    + rewrite Z.mul_0_l.
      change (0 =? 0) with true. cbv iota.
      rewrite Z.mul_0_l.
      apply (f_equal2 (@pair Z Z)); clear; lia.
    + destruct (Z.eqb_spec (r * 2 ^ Z.of_nat n) 0) as [He|Hne].
      { exfalso. clear -He Hpn Hr. nia. }
      assert (Hsplit : 2 ^ (a + Z.of_nat n + 1 - rt)
                       = 2 ^ (a + Z.of_nat n - rt) * 2).
      { replace (a + Z.of_nat n + 1 - rt)
          with ((a + Z.of_nat n - rt) + 1) by (clear; lia).
        rewrite Z.pow_add_r by (clear -Ha; lia). clear; lia. }
      apply (f_equal2 (@pair Z Z)).
      * clear -Hsplit; lia.
      * rewrite Nat2Z.inj_succ.
        rewrite Z.pow_succ_r by (clear; lia). clear; lia.
Qed.

(** rem-nonnegativity of the replay (seed 0; every subsz >= 1). *)
Lemma chain_codes_rem_nonneg : forall k subsz mem rem,
  1 <= subsz -> 0 <= rem ->
  0 <= snd (chain_codes k subsz mem rem).
Proof.
  induction k as [|k IH]; intros subsz mem rem Hs Hr; cbn [chain_codes].
  - cbn [snd]. exact Hr.
  - destruct (chain_code subsz mem rem) as [m' r'] eqn:EC.
    apply IH; [exact Hs|].
    unfold chain_code in EC.
    destruct (Z.eqb_spec rem 0) as [->|Hne]; injection EC as _ <-.
    + clear -Hs; lia.
    + clear -Hr Hne; lia.
Qed.

Lemma chain_at_rem_nonneg : forall cnt rt l,
  rt + 1 <= l ->
  0 <= snd (chain_at cnt rt l).
Proof.
  intros cnt rt l Hl.
  replace l with ((rt + 1) + Z.of_nat (Z.to_nat (l - rt - 1)))
    by (rewrite Z2Nat.id by (clear -Hl; lia); clear; lia).
  induction (Z.to_nat (l - rt - 1)) as [|n IH].
  - rewrite Z.add_0_r. rewrite chain_at_seed by (clear; lia).
    cbn [snd]. clear; lia.
  - replace (rt + 1 + Z.of_nat (S n)) with ((rt + 1 + Z.of_nat n) + 1)
      by (rewrite Nat2Z.inj_succ; clear; lia).
    rewrite chain_at_step by (clear; lia).
    cbv zeta.
    set (SB0 := 2 ^ (rt + 1 + Z.of_nat n - rt)).
    assert (HSB0 : 1 <= SB0).
    { unfold SB0.
      assert (0 < 2 ^ (rt + 1 + Z.of_nat n - rt))
        by (apply Z.pow_pos_nonneg; clear; lia).
      clear -H; lia. }
    pose proof (chain_codes_rem_nonneg
                  (Z.to_nat (cnt (rt + 1 + Z.of_nat n))) SB0
                  (fst (chain_at cnt rt (rt + 1 + Z.of_nat n)))
                  (snd (chain_at cnt rt (rt + 1 + Z.of_nat n)))
                  HSB0 IH) as HK.
    destruct (chain_codes _ SB0 _ _) as [m1 r1].
    cbn [snd] in HK.
    unfold chain_descend. cbn [snd].
    clear -HK; lia.
Qed.

(* ==========================================================================
   2.  No-open (no-hit) preservation on AJ2, phase 2.
   ========================================================================== *)

Lemma aj_noopen_aj2 : forall cnt0 R0 c st,
  1 <= R0 ->
  s_drop st = R0 ->
  s_drop st <> 0 ->
  R0 + 1 <= s_len st ->
  1 <= s_curr st ->
  AJ2 cnt0 R0 st ->
  open_guard c st = false ->
  step_hit st = false ->
  s_count st (s_len st) <= cnt0 (s_len st) ->
  AJ2 cnt0 R0 (step_noopen_st c st).
Proof.
  intros cnt0 R0 c st HR0 Hdrop Hd0 Hlen Hcurr1 HAJ Hop Hhit Hk.
  destruct HAJ as [(Hd & _) | (_ & (paid & Hi1 & Hpw & Hp0))];
    [exfalso; exact (Hd0 Hd)|].
  right.
  split; [cbn [step_noopen_st s_drop]; exact Hd0|].
  unfold aj_acct in *. cbv zeta in *.
  cbn [step_noopen_st s_used s_len s_count s_curr s_drop] in *.
  unfold step_len. rewrite Hhit. cbv iota.
  unfold step_cnt. rewrite zset_same.
  set (SB := 2 ^ (s_len st - R0)) in *.
  assert (HSBp : 0 < SB)
    by (unfold SB; apply Z.pow_pos_nonneg; clear -HR0 Hlen; lia).
  set (B := chain_at cnt0 R0 (s_len st)) in *.
  replace (Z.to_nat (cnt0 (s_len st) - (s_count st (s_len st) - 1)))
    with (S (Z.to_nat (cnt0 (s_len st) - s_count st (s_len st))))
    by (clear -Hk; lia).
  rewrite chain_codes_tail.
  set (CK := chain_codes (Z.to_nat (cnt0 (s_len st) - s_count st (s_len st)))
               SB (fst B) (snd B)) in *.
  destruct Hpw as [Hp | Hp].
  - (* fresh: the DP opens on this code; the witness flips to SB *)
    subst paid.
    destruct (Hp0 eq_refl) as [Hrem Hwin].
    exists SB.
    unfold chain_code. rewrite Hrem.
    change (0 =? 0) with true. cbv iota. cbn [fst snd].
    split; [clear -Hi1; lia | split].
    + right.
      rewrite Z.min_l by (clear -Hwin; lia).
      unfold SB. rewrite Hdrop. reflexivity.
    + intros HSB0. exfalso. clear -HSB0 HSBp; lia.
  - (* touched: keep the witness *)
    exists paid.
    pose proof (chain_code_mem_mono SB (fst CK) (snd CK)
                  ltac:(clear -HSBp; lia)) as HM.
    destruct (chain_code SB (fst CK) (snd CK)) as [m2 r2].
    cbn [fst] in HM |- *.
    split; [clear -Hi1 HM; lia | split].
    + right; exact Hp.
    + intros Hpz. exfalso.
      rewrite Hp in Hpz.
      assert (Hmin0 : 0 <= Z.min (s_len st - s_drop st) (s_curr st))
        by (apply Z.min_glb; [clear -Hlen Hdrop; lia
                             | clear -Hcurr1; lia]).
      pose proof (Z.pow_pos_nonneg 2 _ ltac:(clear; lia) Hmin0) as Hg.
      clear -Hpz Hg; lia.
Qed.

(* ==========================================================================
   3.  The hit-trip telescoping on AJ2 (no open), with the two
       window-digested premises.
   ========================================================================== *)

Lemma aj_hit_aj2 : forall cnt0 R0 c st,
  1 <= R0 ->
  s_drop st = R0 ->
  s_drop st <> 0 ->
  R0 + 1 <= s_len st ->
  1 <= s_curr st ->
  (forall j, 0 <= cnt0 j) ->
  (* Hgeo (window family): an open table's length has not passed its
     lookahead depth *)
  s_len st - s_drop st <= s_curr st ->
  AJ2 cnt0 R0 st ->
  step_hit st = true ->
  s_count st (s_len st) = 1 ->
  s_count st (s_len st) <= cnt0 (s_len st) ->
  (* gap facts (gap_zeros supplier, digested) *)
  s_len st < step_len c st ->
  (forall l, s_len st < l < step_len c st -> cnt0 l = 0) ->
  (* P2 (window family): a table that fills does so at its depth *)
  (snd (chain_code (2 ^ (s_len st - R0))
          (fst (chain_codes
                  (Z.to_nat (cnt0 (s_len st) - s_count st (s_len st)))
                  (2 ^ (s_len st - R0))
                  (fst (chain_at cnt0 R0 (s_len st)))
                  (snd (chain_at cnt0 R0 (s_len st)))))
          (snd (chain_codes
                  (Z.to_nat (cnt0 (s_len st) - s_count st (s_len st)))
                  (2 ^ (s_len st - R0))
                  (fst (chain_at cnt0 R0 (s_len st)))
                  (snd (chain_at cnt0 R0 (s_len st)))))) = 0 ->
   s_curr st <= s_len st - s_drop st) ->
  AJ2 cnt0 R0 (step_noopen_st c st).
Proof.
  intros cnt0 R0 c st HR0 Hdrop Hd0 Hlen Hcurr1 Hnn Hgeo HAJ Hhit Hlast
         Hk Hadv Hgap P2.
  destruct HAJ as [(Hd & _) | (_ & (paid & Hi1 & Hpw & Hp0))];
    [exfalso; exact (Hd0 Hd)|].
  right.
  split; [cbn [step_noopen_st s_drop]; exact Hd0|].
  unfold aj_acct in *. cbv zeta in *.
  cbn [step_noopen_st s_used s_len s_count s_curr s_drop] in *.
  unfold step_len in *. rewrite Hhit in *.
  set (L1 := x_lens c (x_work c (s_sym st + 1))) in *.
  unfold step_cnt.
  rewrite zset_other by (clear -Hadv; lia).
  set (SB := 2 ^ (s_len st - R0)) in *.
  assert (HSBp : 0 < SB)
    by (unfold SB; apply Z.pow_pos_nonneg; clear -HR0 Hlen; lia).
  set (B := chain_at cnt0 R0 (s_len st)) in *.
  set (KPRE := Z.to_nat (cnt0 (s_len st) - s_count st (s_len st))) in *.
  set (CK := chain_codes KPRE SB (fst B) (snd B)) in *.
  (* the full-length count at s_len: one more code closes it *)
  assert (Hfullk : Z.to_nat (cnt0 (s_len st)) = S KPRE).
  { unfold KPRE. rewrite Hlast.
    clear -Hlast Hk; lia. }
  (* the L1 boundary in terms of the post-code accounting *)
  set (CC := chain_code SB (fst CK) (snd CK)) in *.
  assert (Hstep1 : chain_at cnt0 R0 (s_len st + 1)
                   = chain_descend SB (fst CC) (snd CC)).
  { rewrite chain_at_step by (clear -Hlen; lia).
    cbv zeta. fold SB. fold B.
    rewrite Hfullk. rewrite chain_codes_tail. fold CK.
    unfold CC.
    destruct (chain_code SB (fst CK) (snd CK)) as [m2 r2].
    reflexivity. }
  assert (HgapL : chain_at cnt0 R0 L1
                  = (fst (chain_at cnt0 R0 (s_len st + 1))
                       + (if snd (chain_at cnt0 R0 (s_len st + 1)) =? 0
                          then 0
                          else 2 ^ (L1 - R0) - 2 ^ (s_len st + 1 - R0)),
                     snd (chain_at cnt0 R0 (s_len st + 1))
                       * 2 ^ Z.of_nat (Z.to_nat (L1 - (s_len st + 1))))).
  { replace L1 with ((s_len st + 1)
                     + Z.of_nat (Z.to_nat (L1 - (s_len st + 1)))) at 1
      by (rewrite Z2Nat.id by (clear -Hadv; lia); clear; lia).
    rewrite (chain_gap cnt0 R0 (s_len st + 1) _
               ltac:(clear -Hlen; lia)).
    2:{ intros l Hl. apply Hgap.
        rewrite Z2Nat.id in Hl by (clear -Hadv; lia). clear -Hl; lia. }
    rewrite Z2Nat.id by (clear -Hadv; lia).
    replace (s_len st + 1 + (L1 - (s_len st + 1))) with L1
      by (clear; lia).
    reflexivity. }
  (* the K1-position mem dominates the L1 boundary mem *)
  set (K1 := Z.to_nat (cnt0 L1 - s_count st L1)).
  assert (HK1 : fst (chain_at cnt0 R0 L1)
                <= fst (chain_codes K1 (2 ^ (L1 - R0))
                          (fst (chain_at cnt0 R0 L1))
                          (snd (chain_at cnt0 R0 L1)))).
  { apply chain_codes_mem_mono. apply Z.pow_nonneg. clear; lia. }
  (* pow facts *)
  assert (Hpow1 : 2 ^ (s_len st + 1 - R0) = 2 * SB).
  { unfold SB.
    replace (s_len st + 1 - R0) with ((s_len st - R0) + 1)
      by (clear; lia).
    rewrite Z.pow_add_r by (clear -Hlen HR0; lia). clear; lia. }
  assert (HpowL : SB <= 2 ^ (L1 - R0) / 1 \/ True) by (right; exact I).
  assert (HpowLe : 2 * SB <= 2 ^ (L1 - R0)).
  { rewrite <- Hpow1. apply Z.pow_le_mono_r; clear -Hadv; lia. }
  (* the new paid witness: 2^min(L1 - drop, curr) *)
  set (PAID' := 2 ^ Z.min (L1 - s_drop st) (s_curr st)).
  assert (Hmin0 : 0 <= Z.min (L1 - s_drop st) (s_curr st))
    by (apply Z.min_glb; [clear -Hadv Hlen Hdrop; lia
                         | clear -Hcurr1; lia]).
  assert (HPAIDpos : 0 < PAID')
    by (unfold PAID'; apply Z.pow_pos_nonneg; [clear; lia | exact Hmin0]).
  assert (HPAIDle : PAID' <= 2 ^ (L1 - R0)).
  { unfold PAID'. apply Z.pow_le_mono_r; [clear; lia|].
    rewrite Hdrop.
    pose proof (Z.le_min_l (L1 - R0) (s_curr st)). clear -H; lia. }
  (* the old paid value: with Hgeo, min = len - drop, i.e. SB *)
  assert (Hpaidold : paid = 0 \/ paid = SB).
  { destruct Hpw as [Hp|Hp]; [left; exact Hp|right].
    rewrite Hp. rewrite Z.min_l by (clear -Hgeo; lia).
    unfold SB. rewrite Hdrop. reflexivity. }
  exists PAID'.
  split; [| split; [right; reflexivity
                    | intros Hz; exfalso; clear -Hz HPAIDpos; lia]].
  (* CASES on the pre-code rem *)
  destruct (Z.eqb_spec (snd CK) 0) as [Hrem0 | Hremne].
  - (* rem = 0: the code opens a DP table (fresh or touched-full);
       mem grows to fst CK + 2^(L1-R0) at the L1 boundary *)
    assert (HCC : CC = (fst CK + SB, SB - 1)).
    { unfold CC, chain_code. rewrite Hrem0.
      change (0 =? 0) with true. cbv iota. reflexivity. }
    assert (HSB2 : 2 <= SB).
    { unfold SB.
      assert (1 <= s_len st - R0) by (clear -Hlen; lia).
      replace (s_len st - R0) with (1 + (s_len st - R0 - 1))
        by (clear; lia).
      rewrite Z.pow_add_r by (clear -H; lia).
      assert (0 < 2 ^ (s_len st - R0 - 1))
        by (apply Z.pow_pos_nonneg; clear -H; lia).
      clear -H0; lia. }
    assert (HB1 : fst (chain_at cnt0 R0 (s_len st + 1))
                  = fst CK + 2 * SB
                  /\ snd (chain_at cnt0 R0 (s_len st + 1))
                     = 2 * (SB - 1)).
    { rewrite Hstep1, HCC. unfold chain_descend. cbn [fst snd].
      destruct (Z.eqb_spec (SB - 1) 0) as [He|Hne];
        [exfalso; clear -He HSB2; lia|].
      split; [cbn [fst snd]; clear; lia | cbn [fst snd]; clear; lia]. }
    destruct HB1 as [HB1m HB1r].
    assert (HL1m : fst (chain_at cnt0 R0 L1) = fst CK + 2 ^ (L1 - R0)).
    { rewrite HgapL, HB1m, HB1r.
      destruct (Z.eqb_spec (2 * (SB - 1)) 0) as [He|Hne];
        [exfalso; clear -He HSB2; lia|].
      cbn [fst]. rewrite Hpow1. clear; lia. }
    (* used <= fst CK + 2^curr - paid_old; paid_old ∈ {0, SB} *)
    destruct Hpaidold as [-> | ->];
      clear -Hi1 HK1 HL1m HPAIDle HSBp; lia.
  - (* rem >= 1 *)
    destruct (Z.eqb_spec (snd CK - 1) 0) as [Hone | Hmany].
    + (* rem = 1: the code fills the table; P2 pins depth; mem frozen *)
      assert (HCC : CC = (fst CK, 0)).
      { unfold CC, chain_code.
        destruct (Z.eqb_spec (snd CK) 0) as [He|_];
          [exfalso; exact (Hremne He)|].
        f_equal. clear -Hone; lia. }
      specialize (P2 ltac:(fold SB; fold B; fold KPRE; fold CK;
                           change (chain_code SB (fst CK) (snd CK))
                             with CC;
                           rewrite HCC; reflexivity)).
      assert (HB1 : fst (chain_at cnt0 R0 (s_len st + 1)) = fst CK
                    /\ snd (chain_at cnt0 R0 (s_len st + 1)) = 0).
      { rewrite Hstep1, HCC. unfold chain_descend. cbn [fst snd].
        change (0 =? 0) with true. cbv iota.
        split; [cbn [fst snd]; clear; lia | cbn [fst snd]; clear; lia]. }
      destruct HB1 as [HB1m HB1r].
      assert (HL1m : fst (chain_at cnt0 R0 L1) = fst CK).
      { rewrite HgapL, HB1m, HB1r.
        change (0 =? 0) with true. cbv iota.
        rewrite Z.mul_0_l. cbn [fst]. clear; lia. }
      (* depth equality: curr = len - drop; paid_old = SB = 2^curr;
         paid' = 2^min(L1-drop, curr) = 2^curr = SB *)
      assert (Heq : s_curr st = s_len st - s_drop st)
        by (clear -P2 Hgeo; lia).
      assert (HPAID'e : PAID' = SB).
      { unfold PAID'.
        rewrite Z.min_r by (clear -Heq Hadv Hdrop; lia).
        rewrite Heq. unfold SB. rewrite Hdrop. reflexivity. }
      destruct Hpaidold as [-> | ->].
      * (* paid_old = 0 forces rem = 0 (AJ2 ghost), against Hremne *)
        exfalso. destruct (Hp0 eq_refl) as [Hr0 _].
        exact (Hremne Hr0).
      * rewrite HPAID'e.
        clear -Hi1 HK1 HL1m; lia.
    + (* rem >= 2: the table stays open; descends pay through the gap *)
      assert (HremNN : 0 <= snd CK).
      { unfold CK. apply chain_codes_rem_nonneg.
        - clear -HSBp; lia.
        - unfold B. apply chain_at_rem_nonneg. clear -Hlen; lia. }
      assert (Hge2 : 2 <= snd CK) by (clear -Hremne Hmany HremNN; lia).
      assert (HCC : CC = (fst CK, snd CK - 1)).
      { unfold CC, chain_code.
        destruct (Z.eqb_spec (snd CK) 0) as [He|_];
          [exfalso; exact (Hremne He)|reflexivity]. }
      assert (HB1 : fst (chain_at cnt0 R0 (s_len st + 1))
                    = fst CK + SB
                    /\ snd (chain_at cnt0 R0 (s_len st + 1))
                       = 2 * (snd CK - 1)).
      { rewrite Hstep1, HCC. unfold chain_descend. cbn [fst snd].
        destruct (Z.eqb_spec (snd CK - 1) 0) as [He|Hne];
          [exfalso; clear -He Hge2; lia|].
        split; [cbn [fst snd]; clear; lia | cbn [fst snd]; clear; lia]. }
      destruct HB1 as [HB1m HB1r].
      assert (HL1m : fst (chain_at cnt0 R0 L1)
                     = fst CK + SB + (2 ^ (L1 - R0) - 2 * SB)).
      { rewrite HgapL, HB1m, HB1r.
        destruct (Z.eqb_spec (2 * (snd CK - 1)) 0) as [He|Hne];
          [exfalso; clear -He Hge2; lia|].
        cbn [fst]. rewrite Hpow1. clear; lia. }
      destruct Hpaidold as [-> | ->].
      * (* paid_old = 0 forces rem = 0 (AJ2 ghost), against Hremne *)
        exfalso. destruct (Hp0 eq_refl) as [Hr0 _].
        exact (Hremne Hr0).
      * clear -Hi1 HK1 HL1m HPAIDle HpowLe HSBp; lia.
Qed.
