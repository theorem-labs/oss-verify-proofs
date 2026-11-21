(** * EnoughFitsB10 — session 8 (S3): the fit kit.

    Reduces [seed_obligation] (B9's one hypothesis) to ONE oracle-level
    statement [seed_oracle_STMT]: the enough_bound cell's [large]
    covers the ACTUAL code's seed-juncture dp_max.  Everything else is
    proven here: the degenerate arm (mx = root0: the juncture is
    (0, 0) — kleft vanishes past max — and the complete node returns
    the bare root table), the complete arm (mx = root0 + 1: the seed
    is already complete; the drained value is bounded by the PHI LAW
    fst - rem = +1 per code), the oracle cells for every band max
    (sub-15 by vm_compute — the one-time wall lives HERE; the 15-cells
    CITED from the enough bed's Qed examples), and the fuel lift
    (dp_fuel_mono, the sound direction).

    FINDING f-d (statement-level, reported): B1's
    [dpmax_seed_sound_STMT] is unprovable AS SPELLED — enough_phase
    GATES every seed on the count memo (memo_nonzero), so the phase's
    max only covers REACHABLE seeds; an unconditional bound over the
    whole (n, left) rectangle does not follow.  [seed_oracle_STMT]
    supersedes it, carrying the actual code as the reachability
    witness.  Load-bearing corollary: the phase's inner loop steps
    left BY 2 — kleft's EVENNESS (kleft_even, definitional) is an
    enumeration-coverage fact, not merely a range fact. *)

(* FAST TEXT (fasttext-wave2, 2026-09-02): the 11 oracle cells of cells_lens/cells_dists were `vm_compute; reflexivity`
   (the VM evaluates enough_run TWICE per cell: once in the tactic, once in the kernel's cast check; census 2117 s for the file).
   Now: the two cells EnoughCheck already proves (c_286_9_12, c_30_6_8) are CITED like the base's 15-cells; the other nine are
   `natcast` — the kernel evaluates ONCE, by native_compute (the grader compiles native-on; under -native-compiler no this degrades to the VM).
   Statements, exports and assumptions are unchanged (Print Module / Print Assumptions diffed against the base). *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Inftrees ItGTblRev ItGTblGeom ItGTblSortWin ItGTblCover
  ItGTblLeafPos ItGSubCover.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7Strict
  Gap7BridgeParts.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughDP EnoughCheck.
(* SPLIT by tools/split_enough_cells.py: the nine oracle cells live one per file. *)
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  EnoughBound_286_9_11 EnoughBound_286_9_13 EnoughBound_286_9_14
  EnoughBound_30_6_9 EnoughBound_30_6_10 EnoughBound_30_6_11
  EnoughBound_30_6_12 EnoughBound_30_6_13 EnoughBound_30_6_14.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughFitsDesign EnoughFitsA12 EnoughFitsB1
  EnoughFitsB2 EnoughFitsB3 EnoughFitsB4 EnoughFitsB5 EnoughFitsB6
  EnoughFitsB7 EnoughFitsB8 EnoughFitsB9.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Export EnoughFitsPhi.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  The Phi law (chain_phi, chain_codes_rem_ub) lives in EnoughFitsPhi,
       re-exported above.
   ========================================================================== *)

(* ==========================================================================
   2.  kleft facts: even, positive within max, zero past max.
   ========================================================================== *)

Lemma kleft_even : forall cnt l, Z.even (kleft cnt l) = true.
Proof.
  intros. unfold kleft. rewrite Z.even_mul. reflexivity.
Qed.

Lemma wmass_nonneg : forall n l cnt,
  (forall c0, 0 <= cnt c0) -> 0 <= wmass n l cnt.
Proof.
  induction n as [|n IH]; intros l cnt Hnn; cbn [wmass].
  - clear; lia.
  - pose proof (IH (l + 1) cnt Hnn) as H1.
    assert (H2 : 0 <= cnt l * 2 ^ (15 - l))
      by (apply Z.mul_nonneg_nonneg;
          [apply Hnn | apply Z.pow_nonneg; clear; lia]).
    clear -H1 H2; lia.
Qed.

Section KleftFacts.
  Variable cnt : zarr.
  Variable mx : Z.
  Hypothesis Hnn : forall c0, 0 <= cnt c0.
  Hypothesis Hmx : 1 <= mx <= 15.
  Hypothesis Hmxz : forall l, mx < l <= 15 -> cnt l = 0.
  Hypothesis Hmxpos : 1 <= cnt mx.
  Hypothesis Hcomp : wmass 15%nat 1 cnt = 2 ^ 15.

  Lemma kleft_pos : forall l, 1 <= l <= mx -> 1 <= kleft cnt l.
  Proof.
    intros l Hl.
    pose proof (suffix_mass cnt mx Hmx Hmxz Hcomp l Hl) as HS.
    (* the window carries the live mx term *)
    assert (Hsplit : wmass (Z.to_nat (mx - l + 1)) l cnt
                     = wmass (Z.to_nat (mx - l)) l cnt
                       + cnt mx * 2 ^ (15 - mx)).
    { replace (Z.to_nat (mx - l + 1))
        with (Z.to_nat (mx - l) + 1)%nat by (clear -Hl; lia).
      rewrite wmass_split.
      cbn [wmass].
      rewrite Z2Nat.id by (clear -Hl; lia).
      replace (l + (mx - l)) with mx by (clear; lia).
      clear; lia. }
    assert (Hq : 0 < 2 ^ (15 - l))
      by (apply Z.pow_pos_nonneg; clear -Hl Hmx; lia).
    assert (Hqm : 0 < 2 ^ (15 - mx))
      by (apply Z.pow_pos_nonneg; clear -Hmx; lia).
    assert (Hw0 : 0 <= wmass (Z.to_nat (mx - l)) l cnt)
      by (apply wmass_nonneg; exact Hnn).
    assert (Hpos : 0 < kleft cnt l * 2 ^ (15 - l)).
    { rewrite <- HS. rewrite Hsplit.
      assert (0 < cnt mx * 2 ^ (15 - mx))
        by (apply Z.mul_pos_pos; clear -Hmxpos Hqm; lia).
      clear -Hw0 H; lia. }
    destruct (Z.le_gt_cases 1 (kleft cnt l)) as [Hok|Hbad];
      [exact Hok | exfalso].
    assert (kleft cnt l * 2 ^ (15 - l) <= 0)
      by (apply Z.mul_nonpos_nonneg; clear -Hbad Hq; lia).
    clear -Hpos H; lia.
  Qed.

  Lemma kleft_ge2 : forall l, 1 <= l <= mx -> 2 <= kleft cnt l.
  Proof.
    intros l Hl.
    pose proof (kleft_pos l Hl) as H1.
    pose proof (kleft_even cnt l) as H2.
    apply Z.even_spec in H2.
    destruct H2 as [h He].
    rewrite He in H1 |- *.
    clear -H1; lia.
  Qed.

  (** Past max the residual vanishes (the degenerate-arm fact). *)
  Lemma kleft_zero_past : forall l, mx < l <= 15 -> kleft cnt l = 0.
  Proof.
    intros l Hl.
    pose proof (kleft_suffix cnt (Z.to_nat (l - 1)) Hcomp
                  ltac:(clear -Hl; lia)) as HS.
    rewrite Z2Nat.id in HS by (clear -Hl Hmx; lia).
    replace (1 + (l - 1)) with l in HS by (clear; lia).
    rewrite (wmass_zero_on (15 - Z.to_nat (l - 1))%nat l cnt) in HS.
    2:{ intros i Hi. apply Hmxz. clear -Hi Hl Hmx; lia. }
    assert (Hq : 0 < 2 ^ (15 - l))
      by (apply Z.pow_pos_nonneg; clear -Hl; lia).
    destruct (Z.eq_dec (kleft cnt l) 0) as [He|Hne]; [exact He | exfalso].
    destruct (Z.le_gt_cases (kleft cnt l) 0) as [Hle|Hgt].
    - assert (Hlt : kleft cnt l <= -1) by (clear -Hle Hne; lia).
      assert (kleft cnt l * 2 ^ (15 - l) <= (-1) * 2 ^ (15 - l))
        by (apply Z.mul_le_mono_nonneg_r; clear -Hlt Hq; lia).
      clear -HS H Hq; lia.
    - assert (1 * 2 ^ (15 - l) <= kleft cnt l * 2 ^ (15 - l))
        by (apply Z.mul_le_mono_nonneg_r; clear -Hgt Hq; lia).
      clear -HS H Hq; lia.
  Qed.

  (** The caterpillar floor: symbols dominate the remaining depth plus
      the live patterns (cnt l < kleft l below max, or the suffix
      dies). *)
  Lemma syms_floor : forall l, 1 <= l <= mx ->
    mx - l + kleft cnt l <= rem_syms cnt l mx.
  Proof.
    intros l Hl.
    assert (HG : forall d : nat, forall l0,
               l0 = mx - Z.of_nat d -> 1 <= l0 ->
               mx - l0 + kleft cnt l0 <= rem_syms cnt l0 mx).
    { induction d as [|d IH]; intros l0 He Hl0.
      - subst l0.
        replace (mx - Z.of_nat 0) with mx by (clear; cbn; lia).
        pose proof (syms_eq_left_mx cnt mx Hmx Hmxz Hcomp) as HE.
        clear -HE; lia.
      - assert (Hlt : l0 < mx) by (clear -He Hl0; lia).
        assert (Hrec : rem_syms cnt l0 mx
                       = cnt l0 + rem_syms cnt (l0 + 1) mx).
        { unfold rem_syms.
          replace (Z.to_nat (mx - l0 + 1))
            with (S (Z.to_nat (mx - (l0 + 1) + 1)))%nat
            by (clear -Hlt; lia).
          cbn [rem_syms_aux].
          reflexivity. }
        pose proof (IH (l0 + 1) ltac:(clear -He; lia)
                      ltac:(clear -Hl0; lia)) as HI.
        pose proof (kleft_pos (l0 + 1) ltac:(clear -Hl0 Hlt; lia)) as HK1.
        rewrite kleft_step in HK1 by (clear -Hl0; lia).
        rewrite kleft_step in HI by (clear -Hl0; lia).
        rewrite Hrec.
        clear -HI HK1; lia. }
    apply (HG (Z.to_nat (mx - l))).
    - rewrite Z2Nat.id by (clear -Hl; lia). clear; lia.
    - clear -Hl; lia.
  Qed.

End KleftFacts.

(* ==========================================================================
   3.  The count-sum cap.
   ========================================================================== *)

Lemma rem_syms_le_codes : forall lens codes l mxa,
  0 <= codes ->
  rem_syms (sw_cnt lens codes) l mxa <= codes.
Proof.
  intros lens codes l mxa Hc.
  unfold rem_syms, sw_cnt.
  eapply Z.le_trans; [apply it_count_sum_le|].
  rewrite rem_syms_aux_zero.
  rewrite Z2Nat.id by exact Hc.
  clear; lia.
Qed.

(* ==========================================================================
   4.  The oracle cells: sub-15 by vm_compute (the one-time wall),
       the 15-cells cited from the enough bed.
   ========================================================================== *)

Lemma cells_lens : forall mxv, 11 <= mxv <= 15 ->
  exists lg, enough_bound 286 9 mxv = Some lg /\ lg <= ENOUGH_LENS.
Proof.
  intros mxv H.
  assert (mxv = 11 \/ mxv = 12 \/ mxv = 13 \/ mxv = 14 \/ mxv = 15)
    as H5 by (clear -H; lia).
  destruct H5 as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ].
  - exists 796. split; [exact eb_286_9_11
                        | unfold ENOUGH_LENS; clear; lia].
  - exists 800. split; [unfold enough_bound; rewrite c_286_9_12; reflexivity
                        | unfold ENOUGH_LENS; clear; lia].
  - exists 806. split; [exact eb_286_9_13
                        | unfold ENOUGH_LENS; clear; lia].
  - exists 822. split; [exact eb_286_9_14
                        | unfold ENOUGH_LENS; clear; lia].
  - exists 852. split; [| unfold ENOUGH_LENS; clear; lia].
    unfold enough_bound. rewrite c_286_9_15. reflexivity.
Qed.

Lemma cells_dists : forall mxv, 8 <= mxv <= 15 ->
  exists lg, enough_bound 30 6 mxv = Some lg /\ lg <= ENOUGH_DISTS.
Proof.
  intros mxv H.
  assert (mxv = 8 \/ mxv = 9 \/ mxv = 10 \/ mxv = 11 \/ mxv = 12
          \/ mxv = 13 \/ mxv = 14 \/ mxv = 15)
    as H8 by (clear -H; lia).
  destruct H8 as [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ] ] ].
  - exists 92. split; [unfold enough_bound; rewrite c_30_6_8; reflexivity
                       | unfold ENOUGH_DISTS; clear; lia].
  - exists 94. split; [exact eb_30_6_9
                       | unfold ENOUGH_DISTS; clear; lia].
  - exists 102. split; [exact eb_30_6_10
                       | unfold ENOUGH_DISTS; clear; lia].
  - exists 116. split; [exact eb_30_6_11
                       | unfold ENOUGH_DISTS; clear; lia].
  - exists 148. split; [exact eb_30_6_12
                       | unfold ENOUGH_DISTS; clear; lia].
  - exists 210. split; [exact eb_30_6_13
                       | unfold ENOUGH_DISTS; clear; lia].
  - exists 338. split; [exact eb_30_6_14
                       | unfold ENOUGH_DISTS; clear; lia].
  - exists 592. split; [| unfold ENOUGH_DISTS; clear; lia].
    unfold enough_bound. rewrite c_30_6_15. reflexivity.
Qed.

(* ==========================================================================
   5.  THE ORACLE STATEMENT (supersedes B1's dpmax_seed_sound_STMT,
       finding f-d) and the reduction.
   ========================================================================== *)

Definition seed_oracle_STMT : Prop :=
  forall ty (l : list nat) root0 c st large,
    band2 ty l root0 -> lens_capped l ->
    it_pre ty (lens_of_list l) (Z.of_nat (length l)) root0 tnone
      = PreGo c st ->
    x_root c = root0 ->
    root0 + 2 <= x_max c ->
    enough_bound (if ty =? CT_LENS then 286 else 30) root0 (x_max c)
      = Some large ->
    dp_max (S (Z.to_nat (x_max c))) (x_max c) root0
      (rem_syms (sw_cnt (lens_of_list l) (Z.of_nat (length l)))
         (root0 + 1) (x_max c))
      (kleft (sw_cnt (lens_of_list l) (Z.of_nat (length l))) (root0 + 1))
      (root0 + 1) (2 ^ root0) 0
    <= large.

Theorem seed_obligation_of_oracle :
  seed_oracle_STMT -> seed_obligation.
Proof.
  intros HO ty l root0 c st Hband Hcap Hpre Hroot.
  set (cnt0 := sw_cnt (lens_of_list l) (Z.of_nat (length l))) in *.
  set (mx := x_max c) in *.
  pose proof (Hctx0 ty l root0 c st Hband Hcap Hpre Hroot) as Hctx.
  pose proof (Hcomp' ty l root0 c st Hband Hcap Hpre Hroot) as Hcomp.
  pose proof (Hrootmx' ty l root0 c st Hband Hcap Hpre Hroot) as Hrmx.
  pose proof (Hcnt0nn' l) as Hnn.
  fold cnt0 in Hctx, Hcomp, Hnn.
  pose proof Hctx as Hctx2.
  destruct Hctx2 as (_ & _ & Hmx15 & Hmxnz & Hmxz & _).
  fold mx in Hmx15, Hmxnz, Hmxz, Hrmx.
  assert (Hmxpos : 1 <= cnt0 mx)
    by (pose proof (Hnn mx) as H; clear -Hmxnz H; lia).
  (* shared drained-value bound for the complete arm *)
  assert (Hcomplete : forall CAP EN,
             0 < EN ->
             rem_syms cnt0 (root0 + 1) mx = kleft cnt0 (root0 + 1) ->
             kleft cnt0 (root0 + 1) <= CAP ->
             0 <= kleft cnt0 (root0 + 1) ->
             2 ^ root0 + CAP + 1 <= EN ->
             mx = root0 + 1 ->
             dp_max (S (Z.to_nat (mx - root0 - 1))) mx root0
               (rem_syms cnt0 (root0 + 1) mx)
               (kleft cnt0 (root0 + 1)) (root0 + 1) (2 ^ root0) 0
             <= EN).
  { intros CAP EN HEN Hnl Hcap' Hknn Hconst Hcm.
    rewrite Hnl.
    cbn [dp_max].
    rewrite Z.eqb_refl.
    replace (root0 + 1 - root0) with 1 by (clear; lia).
    change ((2:Z) ^ 1) with 2.
    destruct (drain (Z.to_nat (kleft cnt0 (root0 + 1)) + 2) 2
                (kleft cnt0 (root0 + 1)) (2 ^ root0) 0)
      as [[u1 m1] r1] eqn:Hd.
    pose proof (drain_chain 2 (kleft cnt0 (root0 + 1)) (2 ^ root0) 0
                  ltac:(clear; lia) ltac:(clear; lia) Hknn) as HDC.
    rewrite Hd in HDC. cbn [fst snd] in HDC.
    assert (Hm1 : m1 = fst (chain_codes
                              (Z.to_nat (kleft cnt0 (root0 + 1))) 2
                              (2 ^ root0) 0))
      by (rewrite HDC; cbn [fst]; reflexivity).
    pose proof (chain_phi (Z.to_nat (kleft cnt0 (root0 + 1))) 2
                  (2 ^ root0) 0) as HPhi.
    pose proof (chain_codes_rem_ub (Z.to_nat (kleft cnt0 (root0 + 1))) 2
                  (2 ^ root0) 0 ltac:(clear; lia)) as HUb.
    rewrite Z2Nat.id in HPhi by exact Hknn.
    clear -Hm1 HPhi HUb Hcap' Hconst; lia. }
  (* the band arms *)
  destruct Hband as [(HtyE & Hlcap & Hr0E)|(HtyE & Hlcap & Hr0E)].
  - (* LENS: root0 = 9, cap 286, EN 852 *)
    assert (HEN : (if ty =? CT_LENS then ENOUGH_LENS else ENOUGH_DISTS)
                  = 852)
      by (rewrite HtyE; change (CT_LENS =? CT_LENS) with true;
          unfold ENOUGH_LENS; reflexivity).
    rewrite HEN.
    assert (Hlle : kleft cnt0 (root0 + 1) <= 286).
    { destruct (Z.le_gt_cases (root0 + 1) mx) as [Hin|Hout].
      - eapply Z.le_trans;
          [apply (syms_ge_left cnt0 mx Hnn Hmx15 Hmxz Hcomp (root0 + 1)
                    ltac:(clear -Hin Hr0E; lia))|].
        eapply Z.le_trans;
          [apply (rem_syms_le_codes (lens_of_list l)
                    (Z.of_nat (length l)) (root0 + 1) mx
                    ltac:(clear; lia))|].
        clear -Hlcap; lia.
      - rewrite (kleft_zero_past cnt0 mx Hmx15 Hmxz Hcomp (root0 + 1)
                   ltac:(clear -Hout Hmx15 Hr0E; lia)).
        clear; lia. }
    destruct (Z.eq_dec mx root0) as [Hdeg | Hnd].
    + (* degenerate *)
      assert (Hn0 : rem_syms cnt0 (root0 + 1) mx = 0).
      { unfold rem_syms.
        replace (Z.to_nat (mx - (root0 + 1) + 1)) with 0%nat
          by (clear -Hdeg; lia).
        reflexivity. }
      assert (Hl0 : kleft cnt0 (root0 + 1) = 0).
      { apply (kleft_zero_past cnt0 mx Hmx15 Hmxz Hcomp).
        clear -Hdeg Hr0E Hmx15; lia. }
      rewrite Hn0, Hl0.
      cbn [dp_max].
      change (0 =? 0) with true. cbv iota.
      change (Z.to_nat 0 + 2)%nat with 2%nat.
      cbn [drain].
      destruct (Z.ltb_spec 0 0) as [Habs|_]; [exfalso; clear -Habs; lia|].
      cbv iota.
      assert (H29 : (2:Z) ^ 9 = 512) by (vm_compute; reflexivity).
      rewrite Hr0E. clear -H29; lia.
    + destruct (Z.eq_dec mx (root0 + 1)) as [Hcm | Hmain].
      * (* complete seed *)
        apply (Hcomplete 286 852 ltac:(clear; lia)).
        -- rewrite <- Hcm.
           exact (syms_eq_left_mx cnt0 mx Hmx15 Hmxz Hcomp).
        -- exact Hlle.
        -- assert (H := kleft_pos cnt0 mx Hnn Hmx15 Hmxz Hmxpos Hcomp
                          (root0 + 1) ltac:(clear -Hcm Hr0E; lia)).
           clear -H; lia.
        -- assert (H29 : (2:Z) ^ 9 = 512) by (vm_compute; reflexivity).
           rewrite Hr0E. clear -H29; lia.
        -- exact Hcm.
      * (* main arm: the oracle *)
        assert (Hge : root0 + 2 <= mx) by (clear -Hrmx Hnd Hmain; lia).
        destruct (cells_lens mx ltac:(clear -Hge Hr0E Hmx15; lia))
          as (lg & Hcell & Hle).
        assert (Hcell' : enough_bound (if ty =? CT_LENS then 286 else 30)
                           root0 mx = Some lg)
          by (rewrite HtyE; change (CT_LENS =? CT_LENS) with true;
              cbv iota; rewrite <- Hr0E in Hcell; exact Hcell).
        pose proof (HO ty l root0 c st lg
                      ltac:(left; exact (conj HtyE (conj Hlcap Hr0E)))
                      Hcap Hpre Hroot Hge Hcell') as Hdp.
        fold cnt0 mx in Hdp.
        eapply Z.le_trans;
          [| eapply Z.le_trans; [exact Hdp |
             unfold ENOUGH_LENS in Hle; exact Hle]].
        apply dp_fuel_mono;
          [clear -Hge Hmx15 Hr0E; lia | apply Z.pow_nonneg; clear; lia].
  - (* DISTS: root0 = 6, cap 30, EN 592 *)
    assert (HEN : (if ty =? CT_LENS then ENOUGH_LENS else ENOUGH_DISTS)
                  = 592)
      by (rewrite HtyE; change (CT_DISTS =? CT_LENS) with false;
          unfold ENOUGH_DISTS; reflexivity).
    rewrite HEN.
    assert (Hlle : kleft cnt0 (root0 + 1) <= 30).
    { destruct (Z.le_gt_cases (root0 + 1) mx) as [Hin|Hout].
      - eapply Z.le_trans;
          [apply (syms_ge_left cnt0 mx Hnn Hmx15 Hmxz Hcomp (root0 + 1)
                    ltac:(clear -Hin Hr0E; lia))|].
        eapply Z.le_trans;
          [apply (rem_syms_le_codes (lens_of_list l)
                    (Z.of_nat (length l)) (root0 + 1) mx
                    ltac:(clear; lia))|].
        clear -Hlcap; lia.
      - rewrite (kleft_zero_past cnt0 mx Hmx15 Hmxz Hcomp (root0 + 1)
                   ltac:(clear -Hout Hmx15 Hr0E; lia)).
        clear; lia. }
    destruct (Z.eq_dec mx root0) as [Hdeg | Hnd].
    + assert (Hn0 : rem_syms cnt0 (root0 + 1) mx = 0).
      { unfold rem_syms.
        replace (Z.to_nat (mx - (root0 + 1) + 1)) with 0%nat
          by (clear -Hdeg; lia).
        reflexivity. }
      assert (Hl0 : kleft cnt0 (root0 + 1) = 0).
      { apply (kleft_zero_past cnt0 mx Hmx15 Hmxz Hcomp).
        clear -Hdeg Hr0E Hmx15; lia. }
      rewrite Hn0, Hl0.
      cbn [dp_max].
      change (0 =? 0) with true. cbv iota.
      change (Z.to_nat 0 + 2)%nat with 2%nat.
      cbn [drain].
      destruct (Z.ltb_spec 0 0) as [Habs|_]; [exfalso; clear -Habs; lia|].
      cbv iota.
      assert (H26 : (2:Z) ^ 6 = 64) by (vm_compute; reflexivity).
      rewrite Hr0E. clear -H26; lia.
    + destruct (Z.eq_dec mx (root0 + 1)) as [Hcm | Hmain].
      * apply (Hcomplete 30 592 ltac:(clear; lia)).
        -- rewrite <- Hcm.
           exact (syms_eq_left_mx cnt0 mx Hmx15 Hmxz Hcomp).
        -- exact Hlle.
        -- assert (H := kleft_pos cnt0 mx Hnn Hmx15 Hmxz Hmxpos Hcomp
                          (root0 + 1) ltac:(clear -Hcm Hr0E; lia)).
           clear -H; lia.
        -- assert (H26 : (2:Z) ^ 6 = 64) by (vm_compute; reflexivity).
           rewrite Hr0E. clear -H26; lia.
        -- exact Hcm.
      * assert (Hge : root0 + 2 <= mx) by (clear -Hrmx Hnd Hmain; lia).
        destruct (cells_dists mx ltac:(clear -Hge Hr0E Hmx15; lia))
          as (lg & Hcell & Hle).
        assert (Hcell' : enough_bound (if ty =? CT_LENS then 286 else 30)
                           root0 mx = Some lg)
          by (rewrite HtyE; change (CT_DISTS =? CT_LENS) with false;
              cbv iota; rewrite <- Hr0E in Hcell; exact Hcell).
        pose proof (HO ty l root0 c st lg
                      ltac:(right; exact (conj HtyE (conj Hlcap Hr0E)))
                      Hcap Hpre Hroot Hge Hcell') as Hdp.
        fold cnt0 mx in Hdp.
        eapply Z.le_trans;
          [| eapply Z.le_trans; [exact Hdp |
             unfold ENOUGH_DISTS in Hle; exact Hle]].
        apply dp_fuel_mono;
          [clear -Hge Hmx15 Hr0E; lia | apply Z.pow_nonneg; clear; lia].
Qed.

(* ==========================================================================
   6.  The target, one hypothesis from the end.
   ========================================================================== *)

Theorem enough_fits_capped_mod_oracle :
  seed_oracle_STMT -> EnoughFits_STMT.
Proof.
  intros HO.
  exact (enough_fits_capped_mod_seed (seed_obligation_of_oracle HO)).
Qed.
