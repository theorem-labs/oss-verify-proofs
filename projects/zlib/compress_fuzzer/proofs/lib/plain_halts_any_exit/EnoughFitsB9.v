(** * EnoughFitsB9 — session 7: THE ASSEMBLY.

    The ledger_loop-mirror walk carrying CovInv /\ SubLedger /\ AJ2 /\
    AJP /\ AJW, with the trio instantiated at the proven suppliers;
    overflow refuted by aj_guard through it_step_overflow_inv; the
    initial tuple from the landed cov_pre/ledger_pre; completeness
    discharged from it_pre's own kraft gate (o3's premise home);
    first_open_ok by the band constants.  Hi2 needs no invariant
    carry: the walk is downward monotone, so every phase-2 juncture
    bounds through the seed juncture (dpm_walk_iter), fuel-aligned by
    monotonicity (the lemma, not the respell).

    ONE hypothesis remains (the session-8 target): [seed_dp30], the
    oracle bound at the seed juncture — dpmax_seed_sound + the
    enough_bound native cells at 852/592. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Inftrees ItGTblRev ItGTblGeom ItGTblSortWin ItGTblCover
  ItGTblLeafPos ItGSubCover.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7Strict
  Gap7BridgeParts.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughDP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughFitsDesign EnoughFitsA12 EnoughFitsB1
  EnoughFitsB2 EnoughFitsB3 EnoughFitsB4 EnoughFitsB5 EnoughFitsB6
  EnoughFitsB7 EnoughFitsB8.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  dp_max fuel monotonicity (the Hi2 alignment lemma).
   ========================================================================== *)

Lemma chain_code_mem_ge : forall s m r,
  0 <= s -> m <= fst (chain_code s m r).
Proof.
  intros s m r Hs. unfold chain_code.
  destruct (r =? 0); cbn [fst]; clear -Hs; lia.
Qed.

Lemma dp_nonneg : forall f mx rt syms left len mem rem,
  0 <= mem ->
  0 <= dp_max f mx rt syms left len mem rem.
Proof.
  intros f mx rt syms left len mem rem Hm.
  destruct f as [|f]; [cbn [dp_max]; clear; lia|].
  cbn [dp_max].
  destruct (syms =? left).
  - destruct (drain (Z.to_nat left + 2) (2 ^ (len - rt)) left mem rem)
      as [[u1 m1] r1] eqn:Hd.
    pose proof (drain_mem_mono (Z.to_nat left + 2) (2 ^ (len - rt))
                  left mem rem ltac:(apply Z.pow_nonneg; clear; lia)) as H.
    rewrite Hd in H. cbn [fst snd] in H. clear -H Hm; lia.
  - destruct (drain (Z.to_nat (dpm_least syms left) + 2) (2 ^ (len - rt))
                (dpm_least syms left) mem rem)
      as [[u1 m1] r1] eqn:Hd.
    eapply Z.le_trans; [| apply dpm_loop_acc_le].
    clear; lia.
Qed.

(** dpm_loop respects a pointwise child bound at nonnegative mems. *)
Lemma dpm_loop_mono : forall child child' subsz n use mem rem acc,
  0 <= subsz -> 0 <= mem ->
  (forall u m r, 0 <= m -> child u m r <= child' u m r) ->
  dpm_loop child subsz n use mem rem acc
  <= dpm_loop child' subsz n use mem rem acc.
Proof.
  intros child child' subsz n.
  induction n as [|n IH]; intros use mem rem acc Hs Hm Hc;
    cbn [dpm_loop].
  - clear; lia.
  - destruct (chain_code subsz mem rem) as [m' r'] eqn:EC.
    assert (Hm' : 0 <= m').
    { pose proof (chain_code_mem_ge subsz mem rem Hs) as H.
      rewrite EC in H. cbn [fst] in H. clear -H Hm; lia. }
    assert (Hacc : forall k u2 m2 r2 a2 b2,
               a2 <= b2 ->
               dpm_loop child' subsz k u2 m2 r2 a2
               <= dpm_loop child' subsz k u2 m2 r2 b2).
    { induction k as [|k IHk]; intros u2 m2 r2 a2 b2 H2;
        cbn [dpm_loop]; [exact H2|].
      destruct (chain_code subsz m2 r2) as [m3 r3].
      apply IHk. clear -H2; lia. }
    eapply Z.le_trans; [apply (IH (use + 1) m' r'); assumption|].
    apply Hacc.
    pose proof (Hc use mem rem Hm) as H.
    clear -H; lia.
Qed.

Lemma dp_fuel_mono : forall f' f mx rt syms left len mem rem,
  (f <= f')%nat -> 0 <= mem ->
  dp_max f mx rt syms left len mem rem
  <= dp_max f' mx rt syms left len mem rem.
Proof.
  induction f' as [|f' IH]; intros f mx rt syms left len mem rem Hf Hm.
  - replace f with 0%nat by (clear -Hf; lia).
    apply Z.le_refl.
  - destruct f as [|f].
    + change (dp_max 0 mx rt syms left len mem rem) with 0.
      apply dp_nonneg. exact Hm.
    + cbn [dp_max].
      destruct (syms =? left); [apply Z.le_refl|].
      destruct (drain (Z.to_nat (dpm_least syms left) + 2) (2 ^ (len - rt))
                  (dpm_least syms left) mem rem)
        as [[u1 m1] r1] eqn:Hd.
      assert (Hm1 : 0 <= m1).
      { pose proof (drain_mem_mono (Z.to_nat (dpm_least syms left) + 2)
                      (2 ^ (len - rt)) (dpm_least syms left) mem rem
                      ltac:(apply Z.pow_nonneg; clear; lia)) as H.
        rewrite Hd in H. cbn [fst snd] in H. clear -H Hm; lia. }
      apply dpm_loop_mono;
        [apply Z.pow_nonneg; clear; lia | exact Hm1 |].
      intros u m r Hm0.
      assert (Hmc : 0 <= m + (if r =? 0 then 0 else 2 ^ (len - rt))).
      { destruct (r =? 0); [clear -Hm0; lia|].
        pose proof (Z.pow_nonneg 2 (len - rt) ltac:(clear; lia)).
        clear -Hm0 H; lia. }
      apply IH; [clear -Hf; lia | exact Hmc].
Qed.

(* ==========================================================================
   2.  THE ASSEMBLY: one problem instance, one remaining hypothesis.
   ========================================================================== *)

Section Assembly7.
  Variable ty : Z.
  Variable l : list nat.
  Variable root0 : Z.
  Variable c : ItCtx.
  Variable st0 : ItSt.
  Hypothesis Hband : band2 ty l root0.
  Hypothesis Hcap : lens_capped l.
  Hypothesis Hpre : it_pre ty (lens_of_list l) (Z.of_nat (length l)) root0
                      tnone = PreGo c st0.
  Hypothesis Hroot : x_root c = root0.

  Let cnt0 : zarr := sw_cnt (lens_of_list l) (Z.of_nat (length l)).

  (* ---- band facts ---- *)
  Lemma band_ty : ty = CT_LENS \/ ty = CT_DISTS.
  Proof.
    destruct Hband as [(H & _)|(H & _)]; [left|right]; exact H.
  Qed.

  Lemma band_root : root0 = 9 \/ root0 = 6.
  Proof.
    destruct Hband as [(_ & _ & H)|(_ & _ & H)]; [left|right]; exact H.
  Qed.

  (* ---- it_pre discharges (the landed pattern) ---- *)
  Lemma Hcodes0 : 0 <= Z.of_nat (length l).
  Proof. clear; lia. Qed.

  Lemma Hroot015 : 1 <= root0 <= 15.
  Proof. destruct band_root as [->| ->]; clear; lia. Qed.

  Lemma Hlens15 : forall i, 0 <= i < Z.of_nat (length l) ->
    0 <= lens_of_list l i <= 15.
  Proof.
    pose proof (zlens_bounded l Hcap) as H.
    exact H.
  Qed.

  Lemma Hctx0 : CovCtxOk c cnt0.
  Proof.
    exact (proj1 (cov_pre ty (lens_of_list l) (Z.of_nat (length l))
                    root0 tnone c st0 Hcodes0 Hlens15 Hroot015 Hpre)).
  Qed.

  Lemma Hinv00 : CovInv c cnt0 st0.
  Proof.
    exact (proj2 (cov_pre ty (lens_of_list l) (Z.of_nat (length l))
                    root0 tnone c st0 Hcodes0 Hlens15 Hroot015 Hpre)).
  Qed.

  Lemma Hled00 : SubLedger ty c cnt0 st0.
  Proof.
    exact (ledger_pre ty (lens_of_list l) (Z.of_nat (length l))
             root0 tnone c st0 Hcodes0 Hlens15 Hroot015 Hpre).
  Qed.

  Lemma Htyc : x_type c = ty.
  Proof.
    exact (it_pre_go_type ty (lens_of_list l) (Z.of_nat (length l))
             root0 tnone c st0 Hpre).
  Qed.

  Lemma Hcnt0nn' : forall j, 0 <= cnt0 j.
  Proof.
    intros j. unfold cnt0, sw_cnt.
    apply it_count_nonneg.
    intros c0. unfold zzero, zconst. clear; lia.
  Qed.

  Lemma Hrootmx' : root0 <= x_max c.
  Proof.
    pose proof Hctx0 as Hctx.
    destruct Hctx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                      & Hrootmx).
    rewrite <- Hroot. exact Hrootmx.
  Qed.

  (* ---- completeness: it_pre's own kraft gate (o3's premise home) ---- *)
  Lemma Hcomp' : wmass 15%nat 1 cnt0 = 2 ^ 15.
  Proof.
    destruct (it_pre_go_fields ty l root0 c st0 Hpre)
      as (_ & _ & Hxmax & _ & _ & _ & _ & _ & (lft & Hk & Hinc)).
    assert (Hpc : pre_cnt l = cnt0) by reflexivity.
    rewrite Hpc in Hk.
    assert (Hmass : lft = 2 ^ 15 - it_mass 15%nat 1 cnt0).
    { pose proof (it_kraft_mass 15%nat 1 1 cnt0 lft Hk) as H.
      replace (Z.of_nat 15) with 15 in H by (clear; cbn; lia).
      clear -H; lia. }
    (* the incomplete gate passes with mx <> 1 and a live band type *)
    assert (Hmx1 : (x_max c =? 1) = false).
    { apply Z.eqb_neq.
      pose proof Hrootmx' as H.
      destruct band_root as [He|He]; rewrite He in H; clear -H; lia. }
    rewrite <- Hxmax in Hinc.
    unfold it_incomplete in Hinc.
    assert (Htyne : (ty =? CT_CODES) = false)
      by (destruct band_ty as [->| ->]; vm_compute; reflexivity).
    rewrite Htyne, Hmx1 in Hinc.
    cbn [orb negb andb] in Hinc.
    destruct (Z.ltb_spec 0 lft) as [Habs|Hle];
      [exfalso; discriminate Hinc |].
    (* nonnegativity from the context's mass cap *)
    pose proof Hctx0 as Hctx.
    destruct Hctx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hupper & _).
    assert (Hlft0 : lft = 0) by (clear -Hle Hmass Hupper; lia).
    rewrite wmass_it_mass by (clear; cbn; lia).
    replace (16 - 1 - Z.of_nat 15) with 0 by (clear; cbn; lia).
    rewrite Z.pow_0_r, Z.mul_1_r.
    clear -Hmass Hlft0; lia.
  Qed.

  (* ---- first_open_ok: the band constants.
     512 + 64 <= 852 and 64 + 512 <= 592 — this is the arithmetic
     reason zlib's root choices work: the root table plus one FULL
     lookahead sub-table always fit under ENOUGH. ---- *)
  Lemma first_open_ok_lem : forall st,
    CovCtxOk c cnt0 -> CovInv c cnt0 st ->
    SubLedger ty c cnt0 st ->
    AJ2 cnt0 root0 st -> (AJP cnt0 root0 st /\ AJW root0 st) ->
    (step_hit st && (s_len st =? x_max c))%bool = false ->
    open_guard c st = true ->
    s_drop st = 0 ->
    it_enough (x_type c) (open_used c st) = false.
  Proof.
    intros st Hctx Hinv Hled HAJ _ Hbrk Hop Hd0.
    (* used = 2^root0 in phase 1 *)
    assert (Hu : s_used st = 2 ^ root0).
    { destruct HAJ as [(_ & Hu) | (Habs & _)];
        [exact Hu | exfalso; exact (Habs Hd0)]. }
    (* the lookahead is capped at mx - root0 *)
    assert (Hod : open_drop c st = root0).
    { unfold open_drop.
      rewrite Hd0.
      change (0 =? 0) with true. cbv iota.
      exact Hroot. }
    pose proof Hinv as Hinv2.
    destruct Hinv as (Hlen & _ & _ & _ & Hcnt & _ & _ & _).
    pose proof (count_coh c cnt0 st Hctx Hinv2) as [Hcc1 Hcck].
    assert (Hlmx : s_len st <= x_max c).
    { destruct Hctx as (_ & _ & Hmx & _ & Hmxz & _).
      destruct (Z.le_gt_cases (s_len st) (x_max c)) as [Hok|Hbad];
        [exact Hok | exfalso].
      rewrite (Hmxz (s_len st) ltac:(clear -Hbad Hlen; lia)) in Hcck.
      clear -Hcc1 Hcck; lia. }
    assert (HSLmx : step_len c st <= x_max c).
    { destruct (step_hit st) eqn:Hhit.
      - destruct (gap_zeros_lem c cnt0 st Hctx Hinv2 Hhit
                    ltac:(rewrite Hhit; exact Hbrk)) as [[_ Hj] _].
        exact Hj.
      - unfold step_len. rewrite Hhit. exact Hlmx. }
    assert (Hmx15 : x_max c <= 15) by (destruct Hctx as (_ & _ & Hmx & _);
                                        clear -Hmx; lia).
    assert (Hocle : open_curr c st <= 15 - root0).
    { unfold open_curr.
      rewrite Hod.
      eapply Z.le_trans;
        [apply (it_subsz_le 16%nat (step_cnt st) root0 (x_max c)
                  (step_len c st - root0)
                  (Z.shiftl 1 (step_len c st - root0)))|].
      apply Z.max_lub; [clear -HSLmx Hmx15; lia | clear -Hmx15; lia]. }
    (* the constant bound *)
    assert (Hused : open_used c st <= 2 ^ root0 + 2 ^ (15 - root0)).
    { unfold open_used.
      rewrite Hu, Z.shiftl_1_l.
      assert (2 ^ open_curr c st <= 2 ^ (15 - root0))
        by (apply Z.pow_le_mono_r; [clear; lia | exact Hocle]).
      clear -H; lia. }
    assert (Hbound : open_used c st
                     <= (if ty =? CT_LENS then ENOUGH_LENS
                         else ENOUGH_DISTS)).
    { assert (H9 : (2:Z) ^ 9 = 512) by (vm_compute; reflexivity).
      assert (H6 : (2:Z) ^ 6 = 64) by (vm_compute; reflexivity).
      destruct band_root as [He|He]; rewrite He in Hused.
      - replace (15 - 9) with 6 in Hused by (clear; lia).
        destruct band_ty as [Hte|Hte]; rewrite Hte.
        + change (CT_LENS =? CT_LENS) with true. cbv iota.
          unfold ENOUGH_LENS. clear -Hused H9 H6; lia.
        + change (CT_DISTS =? CT_LENS) with false. cbv iota.
          unfold ENOUGH_DISTS. clear -Hused H9 H6; lia.
      - replace (15 - 6) with 9 in Hused by (clear; lia).
        destruct band_ty as [Hte|Hte]; rewrite Hte.
        + change (CT_LENS =? CT_LENS) with true. cbv iota.
          unfold ENOUGH_LENS. clear -Hused H9 H6; lia.
        + change (CT_DISTS =? CT_LENS) with false. cbv iota.
          unfold ENOUGH_DISTS. clear -Hused H9 H6; lia. }
    (* run it_enough *)
    rewrite Htyc.
    unfold it_enough.
    destruct band_ty as [HB | HB]; rewrite HB in Hbound |- *.
    - change (CT_LENS =? CT_LENS) with true in Hbound |- *.
      change (CT_LENS =? CT_DISTS) with false.
      cbv iota in Hbound. cbn [andb]. rewrite orb_false_r.
      destruct (Z.ltb_spec ENOUGH_LENS (open_used c st)) as [Hlt|_];
        [exfalso; clear -Hlt Hbound; lia | reflexivity].
    - change (CT_DISTS =? CT_LENS) with false in Hbound |- *.
      change (CT_DISTS =? CT_DISTS) with true in Hbound |- *.
      cbv iota in Hbound. cbn [andb]. rewrite orb_false_l.
      destruct (Z.ltb_spec ENOUGH_DISTS (open_used c st)) as [Hlt|_];
        [exfalso; clear -Hlt Hbound; lia | reflexivity].
  Qed.

  (* ---- THE ONE REMAINING HYPOTHESIS (the session-8 target): the
     oracle bound at the seed juncture — dpmax_seed_sound + the
     enough_bound native cells at 852/592. ---- *)
  Hypothesis seed_dp :
    dp_max (S (Z.to_nat (x_max c - root0 - 1))) (x_max c) root0
      (rem_syms cnt0 (root0 + 1) (x_max c)) (kleft cnt0 (root0 + 1))
      (root0 + 1) (2 ^ root0) 0
    <= (if ty =? CT_LENS then ENOUGH_LENS else ENOUGH_DISTS).

  Lemma HR0p' : 1 <= root0.
  Proof. destruct band_root as [->| ->]; clear; lia. Qed.

  (* ---- Hi2: no invariant carry — every phase-2 juncture bounds
     through the seed juncture (the walk is downward monotone),
     fuel-aligned by dp_fuel_mono. ---- *)
  Lemma hi2_w : forall st,
    CovCtxOk c cnt0 -> CovInv c cnt0 st ->
    SubLedger ty c cnt0 st ->
    AJ2 cnt0 root0 st -> (AJP cnt0 root0 st /\ AJW root0 st) ->
    s_drop st <> 0 ->
    dp_max (S (Z.to_nat (x_max c - s_len st))) (x_max c) root0
      (rem_syms cnt0 (s_len st) (x_max c)) (kleft cnt0 (s_len st))
      (s_len st)
      (fst (chain_at cnt0 root0 (s_len st)))
      (snd (chain_at cnt0 root0 (s_len st)))
    <= (if ty =? CT_LENS then ENOUGH_LENS else ENOUGH_DISTS).
  Proof.
    intros st Hctx Hinv Hled HAJ _ Hd.
    pose proof Hctx as Hctx2.
    destruct Hctx2 as (Hroot15 & _ & Hmx & Hmxnz & Hmxz & _).
    pose proof (count_coh c cnt0 st Hctx Hinv) as [Hcc1 Hcck].
    pose proof Hinv as Hinv2.
    destruct Hinv2 as (Hlen & _ & _ & _ & _ & _ & _ & Hphase).
    destruct Hphase as [ (Habs & _) | (Hdr & Hrl & _) ];
      [exfalso; exact (Hd Habs)|].
    assert (Hlge : root0 + 1 <= s_len st)
      by (rewrite <- Hroot; clear -Hrl; lia).
    assert (Hlmx : s_len st <= x_max c).
    { destruct (Z.le_gt_cases (s_len st) (x_max c)) as [Hok|Hbad];
        [exact Hok | exfalso].
      rewrite (Hmxz (s_len st) ltac:(clear -Hbad Hlen; lia)) in Hcck.
      clear -Hcc1 Hcck; lia. }
    assert (Hmxpos : 1 <= cnt0 (x_max c))
      by (pose proof (Hcnt0nn' (x_max c)); clear -Hmxnz H; lia).
    set (k := Z.to_nat (s_len st - (root0 + 1))).
    pose proof (dpm_walk_iter cnt0 (x_max c) root0 Hcnt0nn'
                  ltac:(clear -Hmx; lia) Hmxz Hmxpos Hcomp' HR0p'
                  k (Z.to_nat (x_max c - root0 - 1))%nat (root0 + 1)
                  ltac:(clear; lia)
                  ltac:(unfold k;
                        rewrite Z2Nat.id by (clear -Hlge; lia);
                        clear -Hlmx; lia)
                  ltac:(unfold k; clear -Hlmx Hlge; lia)) as Hiter.
    replace ((Z.to_nat (x_max c - root0 - 1)) - k)%nat
      with (Z.to_nat (x_max c - s_len st))
      in Hiter by (unfold k; clear -Hlge Hlmx; lia).
    replace ((root0 + 1) + Z.of_nat k) with (s_len st) in Hiter
      by (unfold k; rewrite Z2Nat.id by (clear -Hlge; lia); clear; lia).
    eapply Z.le_trans; [exact Hiter|].
    rewrite chain_at_seed by (clear; lia).
    cbn [fst snd].
    exact seed_dp.
  Qed.

  (* ---- the trio's remaining supplier wrappers ---- *)
  Lemma cross_full_w : forall st,
    CovCtxOk c cnt0 -> CovInv c cnt0 st -> SubLedger ty c cnt0 st ->
    AJ2 cnt0 root0 st -> (AJP cnt0 root0 st /\ AJW root0 st) ->
    (step_hit st && (s_len st =? x_max c))%bool = false ->
    open_guard c st = true -> s_drop st <> 0 ->
    s_used st <= fst (aj_acct cnt0 root0 st).
  Proof.
    intros st Hctx Hinv Hled HAJ [HP HW] Hbrk Hop Hd.
    exact (cross_full_lem ty c cnt0 root0 st Hroot Hctx Hinv Hled HAJ HP HW
             Hbrk Hop Hd).
  Qed.

  Lemma open_future_w : forall st,
    CovCtxOk c cnt0 -> CovInv c cnt0 st -> SubLedger ty c cnt0 st ->
    AJ2 cnt0 root0 st -> (AJP cnt0 root0 st /\ AJW root0 st) ->
    (step_hit st && (s_len st =? x_max c))%bool = false ->
    open_guard c st = true -> s_drop st <> 0 ->
    fst (aj_acct cnt0 root0 st) + Z.shiftl 1 (open_curr c st)
      <= dp_max (S (Z.to_nat (x_max c - s_len st))) (x_max c) root0
           (rem_syms cnt0 (s_len st) (x_max c)) (kleft cnt0 (s_len st))
           (s_len st)
           (fst (chain_at cnt0 root0 (s_len st)))
           (snd (chain_at cnt0 root0 (s_len st))).
  Proof.
    intros st Hctx Hinv Hled HAJ [HP HW] Hbrk Hop Hd.
    exact (open_future_lem ty c cnt0 root0 st Hroot Hctx Hinv Hled HAJ HP HW
             Hcnt0nn' Hcomp' Hbrk Hop Hd).
  Qed.

  Lemma tyor : x_type c = CT_LENS \/ x_type c = CT_DISTS
               \/ x_max c <= x_root c.
  Proof.
    rewrite Htyc.
    destruct band_ty as [H|H]; [left|right; left]; exact H.
  Qed.

  (* ---- LeafShape (the landed pattern) ---- *)
  Lemma band_codes286 : Z.of_nat (length l) <= 286.
  Proof.
    destruct Hband as [(_ & H & _)|(_ & H & _)]; clear -H; lia.
  Qed.

  Lemma here_shape : forall st', LeafShape ty (it_here c st').
  Proof.
    intros st'.
    pose proof (it_pre_go_work ty (lens_of_list l) (Z.of_nat (length l))
                  root0 tnone c st0 Hpre) as Hwk.
    assert (Hpos1 : (1 <= length l)%nat).
    { apply codes_pos.
      destruct (it_pre_go_fields ty l root0 c st0 Hpre)
        as (_ & _ & _ & _ & _ & _ & _ & Hmxnz & _).
      exact Hmxnz. }
    assert (Hwr : forall s, 0 <= x_work c s < Z.of_nat (length l)).
    { intros s. rewrite Hwk. apply sort_work_range.
      clear -Hpos1; lia. }
    destruct Hband as [(HL & Hcap286 & _)|(HD & Hcap30 & _)].
    - pose proof Hpre as Hpre2. rewrite HL in Hpre2.
      destruct (it_pre_go_lens_arrays (lens_of_list l)
                  (Z.of_nat (length l)) root0 tnone c st0 Hpre2)
        as (Hm & Hb & He).
      rewrite HL.
      apply (here_leafshape_lens c st' Hm Hb He).
      intros s. pose proof (Hwr s). clear -H Hcap286; lia.
    - pose proof Hpre as Hpre2. rewrite HD in Hpre2.
      destruct (it_pre_go_dists (lens_of_list l)
                  (Z.of_nat (length l)) root0 tnone c st0 Hpre2)
        as (Hm & Hb & He).
      rewrite HD.
      apply (here_leafshape_dists c st' Hm Hb He).
      intros s. pose proof (Hwr s). clear -H Hcap30; lia.
  Qed.

  (* ---- THE WALK ---- *)
  Definition INVA (st : ItSt) : Prop :=
    CovInv c cnt0 st /\ SubLedger ty c cnt0 st /\ AJ2 cnt0 root0 st
    /\ AJP cnt0 root0 st /\ AJW root0 st.

  Lemma walk_no_overflow : forall n st t,
    INVA st -> it_loop n c st <> Some (ItOverflow t).
  Proof.
    induction n as [|n IH]; intros st t (Hinv & Hled & HAJ & HP & HW);
      cbn [it_loop].
    - discriminate.
    - destruct (it_step c st) as [st'|st'|t'] eqn:Hs.
      + apply IH.
        pose proof (it_step_cont_inv c st st' Hs) as [Hbrk Harm].
        assert (Hinv' : CovInv c cnt0 st')
          by (exact (cov_step_cont c cnt0 st st' Hctx0 Hinv Hs)).
        assert (Hled' : SubLedger ty c cnt0 st')
          by (exact (ledger_step_cont ty c cnt0 st st'
                       (eq_sym Htyc) tyor Hctx0 Hinv Hled
                       (here_shape st) Hs)).
        assert (HP' : AJP cnt0 root0 st')
          by (exact (ajp_cont c cnt0 root0 st st' Hroot Hctx0 Hinv HP Hs)).
        assert (HAJ' : AJ2 cnt0 root0 st').
        { destruct Harm as [(Hop & Heq) | (Hop & Hen & Heq)].
          - subst st'.
            destruct (Z.eq_dec (s_drop st) 0) as [Hd0 | Hd].
            + exact (aj2_phase1_noopen cnt0 root0 c st Hroot HAJ Hd0
                       Hbrk Hop).
            + pose proof Hinv as Hinv2.
              destruct Hinv2 as (Hlen & _ & _ & _ & _ & _ & _ & Hphase).
              destruct Hphase as [ (Habs & _) | (Hdr & Hrl & _) ];
                [exfalso; exact (Hd Habs)|].
              assert (Hdrop : s_drop st = root0)
                by (rewrite Hdr, Hroot; reflexivity).
              assert (Hlge : root0 + 1 <= s_len st)
                by (rewrite <- Hroot; clear -Hrl; lia).
              pose proof (count_coh c cnt0 st Hctx0 Hinv) as [Hcc1 Hcck].
              pose proof (curr_ge_one ty c cnt0 st Hctx0 Hinv Hled) as Hc1.
              destruct (step_hit st) eqn:Hhit.
              * assert (Hbrk2 : (step_hit st
                                 && (s_len st =? x_max c))%bool = false)
                  by (rewrite Hhit; exact Hbrk).
                destruct (gap_zeros_lem c cnt0 st Hctx0 Hinv Hhit Hbrk2)
                  as [[Hjl Hjmx] Hgz].
                assert (Hlast : s_count st (s_len st) = 1).
                { unfold step_hit, step_cnt in Hhit.
                  rewrite zset_same in Hhit.
                  apply Z.eqb_eq in Hhit. clear -Hhit; lia. }
                apply (aj_hit_aj2 cnt0 root0 c st HR0p'
                         Hdrop Hd Hlge Hc1 Hcnt0nn'
                         (geo_of_guard ty c cnt0 st Hctx0 Hinv Hled Hd)
                         HAJ Hhit Hlast Hcck Hjl Hgz).
                intros Hfull.
                apply (p2_discharge c cnt0 root0 st Hroot Hctx0 Hinv
                         HP HW Hd).
                rewrite (aj_acct_eq cnt0 root0 st).
                exact Hfull.
              * exact (aj_noopen_aj2 cnt0 root0 c st HR0p'
                         Hdrop Hd Hlge Hc1 HAJ Hop Hhit Hcck).
          - subst st'.
            apply (aj_open ty c cnt0 root0 Hroot HR0p'
                     (fun st => AJP cnt0 root0 st /\ AJW root0 st) st
                     Hctx0 Hinv Hled HAJ (conj HP HW) Hbrk Hop Hen).
            + exact (acct_open_used ty c cnt0 root0 st Hroot Hctx0 Hinv
                       Hled HAJ HP HW Hbrk Hop).
            + exact (acct_open_rem c cnt0 root0 st Hroot Hctx0 Hinv HP
                       Hbrk Hop Hen). }
        assert (HW' : AJW root0 st').
        { destruct Harm as [(Hop & Heq) | (Hop & Hen & Heq)]; subst st'.
          - exact (ajw_noopen c cnt0 root0 st Hroot Hctx0 Hinv HW
                     Hbrk Hop).
          - exact (ajw_open c cnt0 root0 st Hroot Hctx0 Hinv Hbrk Hop). }
        exact (conj Hinv' (conj Hled' (conj HAJ' (conj HP' HW')))).
      + discriminate.
      + intro Habs.
        destruct (it_step_overflow_inv c st t' Hs) as (Hbrk & Hop & Hen & _).
        rewrite (aj_guard ty c cnt0 root0 Htyc band_ty
                   (fun st => AJP cnt0 root0 st /\ AJW root0 st)
                   cross_full_w open_future_w hi2_w first_open_ok_lem st
                   Hctx0 Hinv Hled HAJ (conj HP HW) Hbrk Hop) in Hen.
        discriminate Hen.
  Qed.

  Lemma inva0 : INVA st0.
  Proof.
    assert (Hd0 : s_drop st0 = 0)
      by (exact (proj1 (it_pre_go_shape ty (lens_of_list l)
                          (Z.of_nat (length l)) root0 tnone c st0 Hpre))).
    split; [exact Hinv00|].
    split; [exact Hled00|].
    split.
    { left. split; [exact Hd0|].
      pose proof Hled00 as HL.
      destruct HL as (_ & [ (_ & Hu & _) | (Habs & _) ]).
      - rewrite Hu, Hroot. reflexivity.
      - exfalso. rewrite Hd0, Hroot in Habs.
        pose proof HR0p'. clear -Habs H; lia. }
    split; [left; exact Hd0 | left; exact Hd0].
  Qed.

  Theorem a3_here : forall n t, it_loop n c st0 <> Some (ItOverflow t).
  Proof.
    intros n t. apply walk_no_overflow. exact inva0.
  Qed.

End Assembly7.

(* ==========================================================================
   3.  A3 and the target, modulo the ONE seed obligation.
   ========================================================================== *)

Definition seed_obligation : Prop :=
  forall ty l root0 c st,
    band2 ty l root0 -> lens_capped l ->
    it_pre ty (lens_of_list l) (Z.of_nat (length l)) root0 tnone
      = PreGo c st ->
    x_root c = root0 ->
    dp_max (S (Z.to_nat (x_max c - root0 - 1))) (x_max c) root0
      (rem_syms (sw_cnt (lens_of_list l) (Z.of_nat (length l)))
         (root0 + 1) (x_max c))
      (kleft (sw_cnt (lens_of_list l) (Z.of_nat (length l))) (root0 + 1))
      (root0 + 1) (2 ^ root0) 0
    <= (if ty =? CT_LENS then ENOUGH_LENS else ENOUGH_DISTS).

Theorem main_arm_mod_seed : seed_obligation -> main_arm_STMT.
Proof.
  intros HS. unfold main_arm_STMT.
  intros ty l root0 c st Hband Hcap Hpre Hroot n t.
  exact (a3_here ty l root0 c st Hband Hcap Hpre Hroot
           (HS ty l root0 c st Hband Hcap Hpre Hroot) n t).
Qed.

Theorem enough_fits_capped_mod_seed :
  seed_obligation -> EnoughFits_STMT.
Proof.
  intros HS.
  exact (enough_fits_capped_mod_A3 (main_arm_mod_seed HS)).
Qed.
