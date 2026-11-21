(** * EnoughFitsB7 — session 5, part 3: cross_full and the positional
    dischargers.

    cross_full (the guard-clause-to-fullness conversion, the former
    zrev wall): at a phase-2 open trip the model's whole allocation is
    covered by the replay's mem alone.  The chain: AJP pins the
    accounting rem at 1, so the AJ2 ghost's paid is live; Hgeo (the
    guard, B5) and P2 (the window clause, B6) pin the paid exponent at
    exactly 2^curr, which cancels the allocation.

    NOTE (statement-level finding, reported to g6-bound): the retired
    session-3 spelling of the cross_full obligation carried a first
    conjunct [snd (aj_acct st) = 0] — that conjunct is FALSE (the rem
    at an open trip is 1: the trip's own code fills the last slot);
    it was also consumed nowhere in the trio.  The B3 hypothesis now
    carries only the live half.  Likewise aj_open's old positional
    premise [fst (acct st') = fst (acct st)] is FALSE at the FIRST
    open whenever codes of length exactly R0 exist (the phase-1
    replay pads mem at subsz 1); the premise is now the fact the
    proof actually uses, discharged per phase by [acct_open_used]. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Inftrees ItGTblRev ItGTblGeom ItGTblSortWin ItGTblCover ItGSubCover.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7Strict.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughDP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughFitsDesign EnoughFitsA12 EnoughFitsB1
  EnoughFitsB2 EnoughFitsB3 EnoughFitsB4 EnoughFitsB5 EnoughFitsB6.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  Small dischargers.
   ========================================================================== *)

Lemma count_coh : forall c cnt0 st,
  CovCtxOk c cnt0 -> CovInv c cnt0 st ->
  1 <= s_count st (s_len st) /\ s_count st (s_len st) <= cnt0 (s_len st).
Proof.
  intros c cnt0 st Hctx Hinv.
  destruct Hinv as (Hlen & _ & HwinL & HwinU & Hcnt & _).
  rewrite (Hcnt (s_len st) ltac:(clear -Hlen; lia)).
  rewrite Z.ltb_irrefl, Z.eqb_refl.
  clear -HwinL HwinU; lia.
Qed.

Lemma curr_ge_one : forall ty c cnt0 st,
  CovCtxOk c cnt0 -> CovInv c cnt0 st -> SubLedger ty c cnt0 st ->
  1 <= s_curr st.
Proof.
  intros ty c cnt0 st Hctx Hinv Hled.
  destruct Hctx as (Hroot & _).
  destruct Hinv as (_ & _ & _ & _ & _ & _ & _ & Hphase).
  destruct Hphase as [ (_ & Hcr & _) | (Hdr & _) ].
  - rewrite Hcr. clear -Hroot; lia.
  - destruct Hled as (_ & [ (Hd0 & _) | (_ & Hcw & _) ]).
    + exfalso. rewrite Hd0 in Hdr. destruct Hroot as [Hroot1 _].
      clear -Hdr Hroot1; lia.
    + clear -Hcw; lia.
Qed.

(* ==========================================================================
   2.  P2's discharge in the hit lemma's spelling.
   ========================================================================== *)

Lemma p2_discharge : forall c cnt0 R0 st,
  x_root c = R0 ->
  CovCtxOk c cnt0 -> CovInv c cnt0 st ->
  AJP cnt0 R0 st -> AJW R0 st ->
  s_drop st <> 0 ->
  snd (chain_code (2 ^ (s_len st - R0))
         (fst (aj_acct cnt0 R0 st)) (snd (aj_acct cnt0 R0 st))) = 0 ->
  s_curr st <= s_len st - s_drop st.
Proof.
  intros c cnt0 R0 st HR Hctx Hinv HP HW Hd Hfull.
  destruct Hctx as (Hroot & _).
  destruct Hinv as (Hlen & _ & HwinL & HwinU & Hcnt & _ & _ & Hphase).
  destruct Hphase as [ (Habs & _) | (Hdr & Hrl & _) ];
    [exfalso; exact (Hd Habs)|].
  destruct HP as [Habs | HP]; [exfalso; exact (Hd Habs)|].
  assert (Hd1 : 1 <= s_len st - R0) by (rewrite <- HR; clear -Hrl; lia).
  assert (H2d : 2 <= 2 ^ (s_len st - R0)).
  { pose proof (Z.pow_le_mono_r 2 1 (s_len st - R0)
                  ltac:(clear; lia) ltac:(clear -Hd1; lia)) as H.
    clear -H; lia. }
  (* the completing code leaves rem 0, so the rem before it was 1 *)
  assert (Hone : snd (aj_acct cnt0 R0 st) = 1).
  { unfold chain_code in Hfull.
    destruct (Z.eqb_spec (snd (aj_acct cnt0 R0 st)) 0) as [He|Hne].
    - cbn [snd] in Hfull. exfalso. clear -Hfull H2d; lia.
    - cbn [snd] in Hfull. clear -Hfull; lia. }
  (* rem 1 pins the room at 1 *)
  assert (Hleft : aj_left R0 st = 1).
  { rewrite HP in Hone.
    pose proof (aj_off_bounds R0 st ltac:(clear -Hd1; lia)) as HO.
    unfold aj_left in *.
    destruct (Z.eq_dec (aj_off R0 st) 0) as [He|Hne].
    - exfalso. rewrite He, Z.sub_0_r, Z.mod_same in Hone
        by (clear -H2d; lia).
      clear -Hone; lia.
    - rewrite Z.mod_small in Hone by (clear -HO Hne; lia).
      clear -Hone; lia. }
  assert (Hcc : 1 <= s_count st (s_len st)).
  { rewrite (Hcnt (s_len st) ltac:(clear -Hlen; lia)).
    rewrite Z.ltb_irrefl, Z.eqb_refl.
    clear -HwinL HwinU; lia. }
  assert (HdR : s_drop st = R0) by (rewrite Hdr, HR; reflexivity).
  pose proof (ajw_p2 R0 st HW Hd Hleft Hcc) as Hp2.
  rewrite HdR. exact Hp2.
Qed.

(* ==========================================================================
   3.  cross_full.
   ========================================================================== *)

Theorem cross_full_lem : forall ty c cnt0 R0 st,
  x_root c = R0 ->
  CovCtxOk c cnt0 -> CovInv c cnt0 st ->
  SubLedger ty c cnt0 st ->
  AJ2 cnt0 R0 st ->
  AJP cnt0 R0 st -> AJW R0 st ->
  (step_hit st && (s_len st =? x_max c))%bool = false ->
  open_guard c st = true ->
  s_drop st <> 0 ->
  s_used st <= fst (aj_acct cnt0 R0 st).
Proof.
  intros ty c cnt0 R0 st HR Hctx Hinv Hled HAJ HP HW Hbrk Hop Hd.
  destruct HAJ as [ (Habs & _) | (_ & (paid & Hi1 & Hpw & Hp0)) ];
    [exfalso; exact (Hd Habs)|].
  (* the rem is 1, so the ghost is live *)
  pose proof (aj_rem_one_at_open c cnt0 R0 st HR Hctx Hinv HP Hd Hbrk Hop)
    as Hone.
  assert (Hpnz : paid <> 0).
  { intro He. destruct (Hp0 He) as [Hr0 _].
    rewrite Hone in Hr0. clear -Hr0; lia. }
  destruct Hpw as [Habs | Hpe]; [exfalso; exact (Hpnz Habs)|].
  (* Hgeo and P2 pin the exponent at curr *)
  pose proof (geo_of_guard ty c cnt0 st Hctx Hinv Hled Hd) as Hgeo.
  assert (Hleft : aj_left R0 st = 1).
  { destruct HP as [Habs | HP]; [exfalso; exact (Hd Habs)|].
    rewrite HP in Hone.
    destruct Hinv as (Hlen & _ & _ & _ & _ & _ & _ & Hphase).
    destruct Hctx as (Hroot & _).
    destruct Hphase as [ (Habs & _) | (Hdr & Hrl & _) ];
      [exfalso; exact (Hd Habs)|].
    assert (Hd1 : 1 <= s_len st - R0) by (rewrite <- HR; clear -Hrl; lia).
    assert (H2d : 2 <= 2 ^ (s_len st - R0)).
    { pose proof (Z.pow_le_mono_r 2 1 (s_len st - R0)
                    ltac:(clear; lia) ltac:(clear -Hd1; lia)) as H.
      clear -H; lia. }
    pose proof (aj_off_bounds R0 st ltac:(clear -Hd1; lia)) as HO.
    unfold aj_left in *.
    destruct (Z.eq_dec (aj_off R0 st) 0) as [He|Hne].
    - exfalso. rewrite He, Z.sub_0_r, Z.mod_same in Hone
        by (clear -H2d; lia).
      clear -Hone; lia.
    - rewrite Z.mod_small in Hone by (clear -HO Hne; lia).
      clear -Hone; lia. }
  assert (Hcc : 1 <= s_count st (s_len st))
    by (destruct (count_coh c cnt0 st Hctx Hinv) as [H1 _]; exact H1).
  assert (HdR : s_drop st = R0).
  { destruct Hinv as (_ & _ & _ & _ & _ & _ & _ & Hphase).
    destruct Hphase as [ (Habs & _) | (Hdr & _) ];
      [exfalso; exact (Hd Habs) | rewrite Hdr, HR; reflexivity]. }
  pose proof (ajw_p2 R0 st HW Hd Hleft Hcc) as Hp2.
  (* min(len - drop, curr) = curr *)
  assert (Hmin : Z.min (s_len st - s_drop st) (s_curr st) = s_curr st).
  { apply Z.min_r. rewrite HdR. clear -Hp2; lia. }
  rewrite Hmin in Hpe.
  rewrite Hpe in Hi1.
  clear -Hi1; lia.
Qed.

(* ==========================================================================
   4.  The aj_open positional dischargers (both phases).
   ========================================================================== *)

(** The fresh boundary's rem is zero. *)
Lemma acct_open_rem : forall c cnt0 R0 st,
  x_root c = R0 ->
  CovCtxOk c cnt0 -> CovInv c cnt0 st ->
  AJP cnt0 R0 st ->
  (step_hit st && (s_len st =? x_max c))%bool = false ->
  open_guard c st = true ->
  it_enough (x_type c) (open_used c st) = false ->
  snd (aj_acct cnt0 R0 (step_open_st c st)) = 0.
Proof.
  intros c cnt0 R0 st HR Hctx Hinv HP Hbrk Hop Hen.
  assert (Hstep : it_step c st = ItCont (step_open_st c st))
    by (apply it_step_opencont_eq; assumption).
  pose proof (ajp_cont c cnt0 R0 st (step_open_st c st) HR Hctx Hinv HP
                Hstep) as HP'.
  pose proof (aj_off_zero_at_open c cnt0 R0 st HR Hctx Hinv Hbrk Hop)
    as Hoff0.
  assert (HrSL : x_root c < step_len c st).
  { unfold open_guard in Hop.
    apply andb_true_iff in Hop. destruct Hop as [Hltb _].
    apply Z.ltb_lt in Hltb. exact Hltb. }
  destruct Hctx as (Hroot & _).
  destruct HP' as [Habs | HP'].
  { exfalso.
    cbn [step_open_st s_drop] in Habs.
    unfold open_drop in Habs.
    destruct (Z.eqb_spec (s_drop st) 0) as [_|Hne].
    - destruct Hroot as [Hroot1 _]. rewrite Habs in Hroot1.
      clear -Hroot1; lia.
    - exact (Hne Habs). }
  rewrite HP'.
  unfold aj_left.
  rewrite Hoff0, Z.sub_0_r.
  apply Z.mod_same.
  cbn [step_open_st s_len].
  assert (0 < 2 ^ (step_len c st - R0))
    by (apply Z.pow_pos_nonneg;
        [clear; lia | rewrite <- HR; clear -HrSL Hroot; lia]).
  clear -H; lia.
Qed.

(** The first open's boundary accounting: the untouched seed. *)
Lemma acct_open_p1 : forall c cnt0 R0 st,
  x_root c = R0 ->
  CovCtxOk c cnt0 -> CovInv c cnt0 st ->
  s_drop st = 0 ->
  (step_hit st && (s_len st =? x_max c))%bool = false ->
  open_guard c st = true ->
  aj_acct cnt0 R0 (step_open_st c st) = (2 ^ R0, 0).
Proof.
  intros c cnt0 R0 st HR Hctx Hinv Hd0 Hbrk Hop.
  subst R0.
  pose proof Hctx as Hctx2.
  pose proof Hinv as Hinv2.
  destruct Hctx as (Hroot & Hmask & Hmx & _).
  destruct Hinv as (Hlen & Hhuff & HwinL & HwinU & Hcnt & Hpos & Hcov
                    & Hphase).
  destruct Hphase as [ (_ & _ & _ & _ & Hlenroot) | (Hdr & _) ];
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
  rewrite Hacct'.
  replace (step_len c st)
    with ((x_root c + 1)
          + Z.of_nat (Z.to_nat (step_len c st - x_root c - 1)))
    by (rewrite Z2Nat.id by (clear -HrSL; lia); clear; lia).
  rewrite (chain_gap cnt0 (x_root c) (x_root c + 1) _ ltac:(clear; lia)).
  2:{ intros l Hl.
      rewrite Z2Nat.id in Hl by (clear -HrSL; lia).
      apply Hgz. clear -Hl Hlenroot; lia. }
  rewrite chain_at_seed by (clear; lia).
  cbn [fst snd].
  change (0 =? 0) with true. cbv iota.
  rewrite Z.add_0_r, Z.mul_0_l.
  reflexivity.
Qed.

(** The phase-2 open keeps the mem: the closing code takes the last
    slot without opening anything on the accounting side. *)
Lemma acct_open_mem_p2 : forall c cnt0 R0 st,
  x_root c = R0 ->
  CovCtxOk c cnt0 -> CovInv c cnt0 st ->
  AJP cnt0 R0 st ->
  s_drop st <> 0 ->
  (step_hit st && (s_len st =? x_max c))%bool = false ->
  open_guard c st = true ->
  fst (aj_acct cnt0 R0 (step_open_st c st)) = fst (aj_acct cnt0 R0 st).
Proof.
  intros c cnt0 R0 st HR Hctx Hinv HP Hd Hbrk Hop.
  pose proof (aj_rem_one_at_open c cnt0 R0 st HR Hctx Hinv HP Hd Hbrk Hop)
    as Hone.
  pose proof Hctx as Hctx2.
  pose proof Hinv as Hinv2.
  destruct Hctx as (Hroot & Hmask & Hmx & _).
  destruct Hinv as (Hlen & Hhuff & HwinL & HwinU & Hcnt & Hpos & Hcov
                    & Hphase).
  destruct Hphase as [ (Habs & _) | (Hdr & Hrl & _) ];
    [exfalso; exact (Hd Habs)|].
  assert (Hk : s_count st (s_len st) <= cnt0 (s_len st)).
  { rewrite (Hcnt (s_len st) ltac:(clear -Hlen; lia)).
    rewrite Z.ltb_irrefl, Z.eqb_refl.
    clear -HwinL; lia. }
  destruct (step_hit st) eqn:Hhit.
  - (* hit-open *)
    assert (Hbrk2 : (step_hit st && (s_len st =? x_max c))%bool = false)
      by (rewrite Hhit; exact Hbrk).
    destruct (gap_zeros_lem c cnt0 st Hctx2 Hinv2 Hhit Hbrk2)
      as [[Hjl Hjmx] Hgz].
    assert (Hone1 : s_count st (s_len st) = 1).
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
    rewrite (acct_jump cnt0 R0 st (step_open_st c st)
               ltac:(rewrite <- HR; clear -Hrl; lia)
               ltac:(rewrite Hsl'; exact Hjl)
               Hone1 Hk Hfresh
               ltac:(rewrite Hsl'; exact Hgz)).
    cbn [fst].
    rewrite Hone.
    unfold chain_code.
    change (1 =? 0) with false. cbv iota. cbn [fst snd].
    replace (1 - 1) with 0 by (clear; lia).
    change (0 =? 0) with true. cbv iota.
    apply Z.add_0_r.
  - (* mid-run open *)
    assert (Hsl2 : s_len (step_open_st c st) = s_len st)
      by (cbn [step_open_st s_len]; unfold step_len;
          rewrite Hhit; reflexivity).
    assert (Hcc : s_count (step_open_st c st) (s_len (step_open_st c st))
                  = s_count st (s_len st) - 1).
    { rewrite Hsl2. cbn [step_open_st s_count].
      unfold step_cnt. apply zset_same. }
    rewrite (acct_tail cnt0 R0 st (step_open_st c st) Hsl2 Hcc Hk).
    rewrite Hone.
    unfold chain_code.
    change (1 =? 0) with false. cbv iota. cbn [fst].
    reflexivity.
Qed.

(** The combined aj_open premise, discharged in both phases. *)
Lemma acct_open_used : forall ty c cnt0 R0 st,
  x_root c = R0 ->
  CovCtxOk c cnt0 -> CovInv c cnt0 st ->
  SubLedger ty c cnt0 st ->
  AJ2 cnt0 R0 st -> AJP cnt0 R0 st -> AJW R0 st ->
  (step_hit st && (s_len st =? x_max c))%bool = false ->
  open_guard c st = true ->
  s_used st <= fst (aj_acct cnt0 R0 (step_open_st c st)).
Proof.
  intros ty c cnt0 R0 st HR Hctx Hinv Hled HAJ HP HW Hbrk Hop.
  destruct (Z.eq_dec (s_drop st) 0) as [Hd0 | Hd].
  - destruct HAJ as [ (_ & Hu) | (Habs & _) ];
      [| exfalso; exact (Habs Hd0)].
    rewrite Hu.
    rewrite (acct_open_p1 c cnt0 R0 st HR Hctx Hinv Hd0 Hbrk Hop).
    cbn [fst]. clear; lia.
  - pose proof (cross_full_lem ty c cnt0 R0 st HR Hctx Hinv Hled HAJ HP HW
                  Hbrk Hop Hd) as Hcf.
    rewrite (acct_open_mem_p2 c cnt0 R0 st HR Hctx Hinv HP Hd Hbrk Hop).
    exact Hcf.
Qed.
