(** * EnoughFitsA12 — A1 (regime_split) + A2 (regime_b), proved AS FROZEN
    (a5 fit-check pass at EnoughFitsDesign.v ; Tier-A statements
    consumed verbatim from that file — no respells).

    Shared work-integrity lemmas (A3's future diet) are factored
    standalone: [it_pre_go_fields], [it_findmax_le/zero_above/hit],
    [it_findmin_spec], [it_count_ge/nonneg/hit/sum_le],
    [it_sort_range], [codes_pos], [work_lens_le_max],
    [it_mass_drop_zeros], [it_mass_le_sum2], [complete_min_small].

    f1 COMPLIANCE: no it_subsz fact enters any context (A1/A2 never
    reach the opening's sizing); every lia is need-set clear-guarded;
    no backtracking fallbacks.

    A2 took NO band2 narrowing: [codes >= 1] comes from PreGo itself
    (findmax <> 0 forces a nonzero count, impossible at codes = 0), so
    the frozen premise set sufficed. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Inftrees ItGTblGeom.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7Strict.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughFitsDesign.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   0.  Abbreviations for it_pre's internal terms (proof-side names; the
       frozen statements are untouched).
   ========================================================================== *)

Definition pre_cnt (l : list nat) : zarr :=
  it_count (Z.to_nat (Z.of_nat (length l))) 0 (lens_of_list l) zzero.
Definition pre_mx (l : list nat) : Z :=
  it_findmax 15%nat MAXBITS (pre_cnt l).
Definition pre_mn (l : list nat) : Z :=
  it_findmin 16%nat 1 (pre_mx l) (pre_cnt l).
Definition pre_r (l : list nat) (root0 : Z) : Z :=
  let r1 := if pre_mx l <? root0 then pre_mx l else root0 in
  if r1 <? pre_mn l then pre_mn l else r1.
Definition pre_work (l : list nat) : zarr :=
  snd (it_sort (Z.to_nat (Z.of_nat (length l))) 0 (lens_of_list l)
        (it_offs 14%nat 1 (pre_cnt l) (zset zzero 1 0)) zzero).

(* ==========================================================================
   1.  it_pre inversion (PreGo fields).
   ========================================================================== *)

Lemma it_pre_go_fields : forall ty (l : list nat) root0 c st,
  it_pre ty (lens_of_list l) (Z.of_nat (length l)) root0 tnone
    = PreGo c st ->
  x_type c = ty
  /\ x_root c = pre_r l root0
  /\ x_max c = pre_mx l
  /\ x_lens c = lens_of_list l
  /\ x_work c = pre_work l
  /\ s_len st = pre_mn l
  /\ s_count st = pre_cnt l
  /\ pre_mx l <> 0
  /\ (exists lft, it_kraft 15%nat 1 1 (pre_cnt l) = Some lft
        /\ it_incomplete ty lft (pre_mx l) = false).
Proof.
  intros ty l root0 c st H.
  unfold it_pre in H. cbv zeta in H.
  lazymatch type of H with
  | (if ?b then _ else _) = _ => destruct b eqn:Emx
  end; [discriminate H|].
  lazymatch type of H with
  | (match ?x with _ => _ end) = _ => destruct x as [lft|] eqn:Ek
  end; [|discriminate H].
  lazymatch type of H with
  | (if ?b then _ else _) = _ => destruct b eqn:Einc
  end; [discriminate H|].
  lazymatch type of H with
  | (if ?b then _ else _) = _ => destruct b eqn:Een
  end; [discriminate H|].
  injection H as Hc Hst. subst c st.
  unfold pre_r, pre_mn, pre_mx, pre_cnt, pre_work.
  cbn [x_type x_root x_max x_lens x_work s_len s_count].
  repeat split; try reflexivity.
  - apply Z.eqb_neq. exact Emx.
  - exists lft. split; [exact Ek | exact Einc].
Qed.

(* ==========================================================================
   2.  it_findmax / it_findmin characterizations.
   ========================================================================== *)

Lemma it_findmax_le : forall n m cnt,
  0 <= m -> Z.of_nat n <= m + 1 -> 0 <= it_findmax n m cnt <= m.
Proof.
  induction n as [|k IH]; intros m cnt Hm Hw; cbn [it_findmax].
  - clear -Hm; lia.
  - destruct (Z.eqb_spec (cnt m) 0) as [Hz|Hz].
    + destruct k as [|k'].
      * cbn [it_findmax]. clear -Hm; lia.
      * assert (Hm1 : 0 <= m - 1)
          by (rewrite !Nat2Z.inj_succ in Hw; clear -Hw; lia).
        assert (Hw1 : Z.of_nat (S k') <= (m - 1) + 1)
          by (rewrite !Nat2Z.inj_succ in *; clear -Hw; lia).
        pose proof (IH (m - 1) cnt Hm1 Hw1) as HI. clear -HI; lia.
    + clear -Hm; lia.
Qed.

Lemma it_findmax_zero_above : forall n m cnt j,
  m - Z.of_nat n < j <= m ->
  it_findmax n m cnt < j ->
  cnt j = 0.
Proof.
  induction n as [|k IH]; intros m cnt j Hw Hr.
  - cbn [it_findmax] in *. clear -Hw; lia.
  - cbn [it_findmax] in Hr.
    destruct (Z.eqb_spec (cnt m) 0) as [Hz|Hz].
    + destruct (Z.eqb_spec j m) as [He|He].
      * subst j. exact Hz.
      * apply (IH (m - 1) cnt j).
        { rewrite Nat2Z.inj_succ in Hw. clear -Hw He; lia. }
        { exact Hr. }
    + (* returned m; j <= m and m < j contradict *)
      clear -Hw Hr; lia.
Qed.

Lemma it_findmax_hit : forall n m cnt,
  it_findmax n m cnt <> 0 -> cnt (it_findmax n m cnt) <> 0.
Proof.
  induction n as [|k IH]; intros m cnt Hne; cbn [it_findmax] in *.
  - exfalso; apply Hne; reflexivity.
  - destruct (Z.eqb_spec (cnt m) 0) as [Hz|Hz].
    + apply IH. exact Hne.
    + exact Hz.
Qed.

(** Any present length in the scan window is <= the findmax result. *)
Lemma it_findmax_present_le : forall n m cnt j,
  m - Z.of_nat n < j <= m ->
  cnt j <> 0 ->
  j <= it_findmax n m cnt.
Proof.
  intros n m cnt j Hw Hne.
  destruct (Z.le_gt_cases j (it_findmax n m cnt)) as [Hle|Hgt];
    [exact Hle|].
  exfalso. apply Hne. exact (it_findmax_zero_above n m cnt j Hw Hgt).
Qed.

Lemma it_findmin_spec : forall n m mx cnt,
  0 <= m <= mx -> mx <= m + Z.of_nat n ->
  m <= it_findmin n m mx cnt <= mx
  /\ (forall j, m <= j < it_findmin n m mx cnt -> cnt j = 0).
Proof.
  induction n as [|k IH]; intros m mx cnt Hm Hfuel; cbn [it_findmin].
  - assert (He : m = mx) by (clear -Hm Hfuel; lia). subst mx.
    split; [clear -Hm; lia | intros j Hj; exfalso; clear -Hj; lia].
  - destruct (Z.geb_spec m mx) as [Hge|Hlt].
    + assert (He : m = mx) by (clear -Hm Hge; lia). subst mx.
      split; [clear -Hm; lia | intros j Hj; exfalso; clear -Hj; lia].
    + destruct (Z.eqb_spec (cnt m) 0) as [Hz|Hz].
      * destruct (IH (m + 1) mx cnt
                    ltac:(clear -Hm Hlt; lia)
                    ltac:(rewrite Nat2Z.inj_succ in Hfuel;
                          clear -Hfuel; lia)) as [HB HZ].
        split; [clear -HB; lia|].
        intros j Hj.
        destruct (Z.eqb_spec j m) as [He|He].
        -- subst j. exact Hz.
        -- apply HZ. clear -Hj He; lia.
      * split; [clear -Hm; lia | intros j Hj; exfalso; clear -Hj; lia].
Qed.

(* ==========================================================================
   3.  it_count characterizations.
   ========================================================================== *)

Lemma it_count_ge : forall k i lens cnt cell,
  cnt cell <= it_count k i lens cnt cell.
Proof.
  induction k as [|k IH]; intros i lens cnt cell; cbn [it_count].
  - clear; lia.
  - eapply Z.le_trans; [|apply IH].
    unfold zset. destruct (Z.eqb_spec cell (lens i)) as [He|He].
    + subst cell. clear; lia.
    + clear; lia.
Qed.

Lemma it_count_nonneg : forall k i lens cnt,
  (forall c0, 0 <= cnt c0) ->
  forall cell, 0 <= it_count k i lens cnt cell.
Proof.
  induction k as [|k IH]; intros i lens cnt Hnn cell; cbn [it_count].
  - apply Hnn.
  - apply IH. intros c0. unfold zset.
    destruct (Z.eqb_spec c0 (lens i)) as [He|He].
    + pose proof (Hnn (lens i)). clear -H; lia.
    + apply Hnn.
Qed.

Lemma it_count_hit : forall k i lens cnt j,
  0 <= j < Z.of_nat k ->
  (forall c0, 0 <= cnt c0) ->
  1 <= it_count k i lens cnt (lens (i + j)).
Proof.
  induction k as [|k IH]; intros i lens cnt j Hj Hnn.
  - exfalso. clear -Hj; lia.
  - cbn [it_count].
    destruct (Z.eqb_spec j 0) as [He|He].
    + subst j. rewrite Z.add_0_r.
      eapply Z.le_trans; [|apply it_count_ge].
      rewrite zset_same. pose proof (Hnn (lens i)). clear -H; lia.
    + replace (i + j) with ((i + 1) + (j - 1)) by (clear; lia).
      apply IH.
      * rewrite Nat2Z.inj_succ in Hj. clear -Hj He; lia.
      * intros c0. unfold zset.
        destruct (Z.eqb_spec c0 (lens i)) as [Hc|Hc].
        -- pose proof (Hnn (lens i)). clear -H; lia.
        -- apply Hnn.
Qed.

(** Range-sum bookkeeping over [rem_syms_aux] (EnoughFitsDesign). *)

Lemma rem_syms_aux_ext : forall n a b l,
  (forall j, l <= j < l + Z.of_nat n -> a j = b j) ->
  rem_syms_aux n a l = rem_syms_aux n b l.
Proof.
  induction n as [|k IH]; intros a b l H; cbn [rem_syms_aux];
    [reflexivity|].
  rewrite (H l) by (clear; lia).
  f_equal. apply IH. intros j Hj. apply H.
  rewrite Nat2Z.inj_succ. clear -Hj; lia.
Qed.

Lemma rem_syms_aux_zero : forall n l, rem_syms_aux n zzero l = 0.
Proof.
  induction n as [|k IH]; intros l; cbn [rem_syms_aux]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma rem_syms_aux_nonneg : forall n cnt l,
  (forall c0, 0 <= cnt c0) -> 0 <= rem_syms_aux n cnt l.
Proof.
  induction n as [|k IH]; intros cnt l Hnn; cbn [rem_syms_aux];
    [clear; lia|].
  pose proof (Hnn l). pose proof (IH cnt (l + 1) Hnn). clear -H H0; lia.
Qed.

Lemma rem_syms_aux_zset_le : forall n cnt x v l,
  cnt x <= v ->
  rem_syms_aux n (zset cnt x v) l <= rem_syms_aux n cnt l + (v - cnt x).
Proof.
  induction n as [|k IH]; intros cnt x v l Hle; cbn [rem_syms_aux].
  - clear -Hle; lia.
  - unfold zset at 1. destruct (Z.eqb_spec l x) as [He|He].
    + subst l.
      rewrite (rem_syms_aux_ext k (zset cnt x v) cnt (x + 1));
        [clear -Hle; lia|].
      intros j Hj. unfold zset.
      destruct (Z.eqb_spec j x) as [Hjx|Hjx];
        [exfalso; clear -Hj Hjx; lia | reflexivity].
    + pose proof (IH cnt x v (l + 1) Hle) as HI. clear -HI; lia.
Qed.

Lemma it_count_sum_le : forall k i lens cnt n l,
  rem_syms_aux n (it_count k i lens cnt) l
    <= rem_syms_aux n cnt l + Z.of_nat k.
Proof.
  induction k as [|k IH]; intros i lens cnt n l; cbn [it_count].
  - clear; lia.
  - eapply Z.le_trans; [apply IH|].
    pose proof (rem_syms_aux_zset_le n cnt (lens i)
                  (cnt (lens i) + 1) l ltac:(clear; lia)) as HZ.
    rewrite Nat2Z.inj_succ. clear -HZ; lia.
Qed.

(* ==========================================================================
   4.  it_sort range integrity + codes positivity.
   ========================================================================== *)

Lemma it_sort_range : forall k i lens offs work cmax,
  0 <= i -> i + Z.of_nat k <= cmax ->
  (forall s, 0 <= work s < cmax) ->
  forall s, 0 <= snd (it_sort k i lens offs work) s < cmax.
Proof.
  induction k as [|k IH]; intros i lens offs work cmax Hi Hk Hw s;
    cbn [it_sort].
  - apply Hw.
  - rewrite Nat2Z.inj_succ in Hk.
    destruct (Z.eqb_spec (lens i) 0) as [Hz|Hz].
    + apply (IH (i + 1) lens offs work cmax
               ltac:(clear -Hi; lia) ltac:(clear -Hk; lia) Hw).
    + apply (IH (i + 1) lens _ _ cmax
               ltac:(clear -Hi; lia) ltac:(clear -Hk; lia)).
      intros s0. unfold zset.
      destruct (Z.eqb_spec s0 (offs (lens i))) as [He|He].
      * split; [clear -Hi; lia | clear -Hi Hk; lia].
      * apply Hw.
Qed.

Lemma codes_pos : forall (l : list nat),
  pre_mx l <> 0 -> (1 <= length l)%nat.
Proof.
  intros l Hmx.
  destruct l as [|x l']; [|cbn [length]; clear; lia].
  exfalso. apply Hmx.
  reflexivity.
Qed.

(* ==========================================================================
   5.  W1' — every work-slot's length is <= the findmax result.
   ========================================================================== *)

Lemma work_lens_le_max : forall (l : list nat),
  lens_capped l ->
  pre_mx l <> 0 ->
  forall s, lens_of_list l (pre_work l s) <= pre_mx l.
Proof.
  intros l CAP Hmx s.
  assert (Hmx1 : 1 <= pre_mx l <= 15).
  { pose proof (it_findmax_le 15%nat MAXBITS (pre_cnt l)
                  ltac:(unfold MAXBITS; clear; lia)
                  ltac:(unfold MAXBITS; clear; lia)) as HB.
    unfold pre_mx, MAXBITS in *. clear -HB Hmx; lia. }
  assert (Hcodes : (1 <= length l)%nat) by (apply codes_pos; exact Hmx).
  (* the slot value is a symbol index in [0, codes) *)
  assert (Hw : 0 <= pre_work l s < Z.of_nat (length l)).
  { unfold pre_work.
    rewrite Nat2Z.id.
    apply it_sort_range.
    - clear; lia.
    - clear; lia.
    - intros s0. unfold zzero, zconst. clear -Hcodes; lia. }
  set (w := pre_work l s) in *.
  (* its length entry *)
  unfold lens_of_list, zlens.
  destruct (Nat.eq_dec (nth (Z.to_nat w) l 0%nat) 0%nat) as [He|He].
  - rewrite He. change (Z.of_nat 0%nat) with 0. clear -Hmx1; lia.
  - assert (Hin : In (nth (Z.to_nat w) l 0%nat) l).
    { apply nth_In. clear -Hw; lia. }
    pose proof (CAP _ Hin) as Hcap.
    set (L := Z.of_nat (nth (Z.to_nat w) l 0%nat)) in *.
    assert (HL : 1 <= L <= 15) by (unfold L; clear -He Hcap; lia).
    (* the counted cell at L is >= 1 *)
    assert (Hcnt : 1 <= pre_cnt l L).
    { unfold pre_cnt. rewrite Nat2Z.id.
      replace L with (lens_of_list l (0 + w)).
      2:{ rewrite Z.add_0_l. unfold lens_of_list, zlens, L. reflexivity. }
      apply it_count_hit.
      - clear -Hw; lia.
      - intros c0. unfold zzero, zconst. clear; lia. }
    (* present lengths are <= findmax *)
    apply (it_findmax_present_le 15%nat MAXBITS (pre_cnt l) L).
    + unfold MAXBITS. clear -HL; lia.
    + clear -Hcnt; lia.
Qed.

(* ==========================================================================
   6.  Kraft-mass corollary: complete codes have small min length.
   ========================================================================== *)

Lemma it_mass_drop_zeros : forall a n l cnt,
  (forall j, l <= j < l + Z.of_nat a -> cnt j = 0) ->
  it_mass (a + n) l cnt = it_mass n (l + Z.of_nat a) cnt.
Proof.
  induction a as [|a IH]; intros n l cnt Hz.
  - cbn [Nat.add]. rewrite Z.add_0_r. reflexivity.
  - cbn [Nat.add it_mass].
    rewrite (Hz l) by (rewrite Nat2Z.inj_succ; clear; lia).
    rewrite (IH n (l + 1)).
    2:{ intros j Hj. apply Hz. rewrite Nat2Z.inj_succ in *.
        clear -Hj; lia. }
    rewrite Nat2Z.inj_succ.
    replace (l + 1 + Z.of_nat a) with (l + Z.succ (Z.of_nat a))
      by (clear; lia).
    clear; lia.
Qed.

Lemma it_mass_le_sum2 : forall n l cnt,
  (forall c0, 0 <= cnt c0) ->
  2 * it_mass n l cnt <= 2 ^ Z.of_nat n * rem_syms_aux n cnt l.
Proof.
  induction n as [|k IH]; intros l cnt Hnn; cbn [it_mass rem_syms_aux].
  - clear; lia.
  - pose proof (IH (l + 1) cnt Hnn) as HI.
    pose proof (rem_syms_aux_nonneg k cnt (l + 1) Hnn) as HS.
    pose proof (Hnn l) as Hc.
    assert (Hp : 0 < 2 ^ Z.of_nat k)
      by (apply Z.pow_pos_nonneg; clear; lia).
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by (clear; lia).
    clear -HI HS Hc Hp. nia.
Qed.

(** PreGo + complete (kraft residual 0) at symbol budget N forces
    2 ^ min <= N — the mass argument. *)
Lemma complete_min_small : forall (l : list nat),
  pre_mx l <> 0 ->
  it_kraft 15%nat 1 1 (pre_cnt l) = Some 0 ->
  2 ^ pre_mn l <= Z.of_nat (length l).
Proof.
  intros l Hmx Hk.
  assert (Hnn : forall c0, 0 <= pre_cnt l c0).
  { intros c0. unfold pre_cnt. apply it_count_nonneg.
    intros c1. unfold zzero, zconst. clear; lia. }
  assert (Hmx15 : 1 <= pre_mx l <= 15).
  { pose proof (it_findmax_le 15%nat MAXBITS (pre_cnt l)
                  ltac:(unfold MAXBITS; clear; lia)
                  ltac:(unfold MAXBITS; clear; lia)) as HB.
    unfold pre_mx, MAXBITS in *. clear -HB Hmx; lia. }
  destruct (it_findmin_spec 16%nat 1 (pre_mx l) (pre_cnt l)
              ltac:(clear -Hmx15; lia) ltac:(clear -Hmx15; lia))
    as [Hmn Hzb].
  fold (pre_mn l) in Hmn, Hzb.
  (* mass = 2^15 *)
  pose proof (it_kraft_mass 15%nat 1 1 (pre_cnt l) 0 Hk) as Hm.
  cbn [Z.of_nat] in Hm.
  assert (Hmass : it_mass 15 1 (pre_cnt l) = 2 ^ 15)
    by (clear -Hm; lia).
  (* drop the zero prefix below mn *)
  set (mn := pre_mn l) in *.
  assert (Hsplit : (15 = Z.to_nat (mn - 1) + Z.to_nat (16 - mn))%nat)
    by (clear -Hmn Hmx15; lia).
  rewrite Hsplit in Hmass.
  rewrite (it_mass_drop_zeros (Z.to_nat (mn - 1)) (Z.to_nat (16 - mn))
             1 (pre_cnt l)) in Hmass.
  2:{ intros j Hj. apply Hzb.
      rewrite Z2Nat.id in Hj by (clear -Hmn Hmx15; lia).
      clear -Hj; lia. }
  rewrite Z2Nat.id in Hmass by (clear -Hmn Hmx15; lia).
  replace (1 + (mn - 1)) with mn in Hmass by (clear; lia).
  (* bound the tail mass by the tail sum *)
  pose proof (it_mass_le_sum2 (Z.to_nat (16 - mn)) mn (pre_cnt l) Hnn)
    as Hle.
  rewrite Hmass in Hle.
  rewrite Z2Nat.id in Hle by (clear -Hmn Hmx15; lia).
  (* tail sum <= codes *)
  assert (Hsum : rem_syms_aux (Z.to_nat (16 - mn)) (pre_cnt l) mn
                   <= Z.of_nat (length l)).
  { unfold pre_cnt. rewrite Nat2Z.id.
    eapply Z.le_trans;
      [apply (it_count_sum_le (length l) 0 (lens_of_list l) zzero)|].
    rewrite rem_syms_aux_zero. clear; lia. }
  (* 2^16 <= 2^(16-mn) * N  ==>  2^mn <= N *)
  assert (Hpos : 0 < 2 ^ (16 - mn))
    by (apply Z.pow_pos_nonneg; clear -Hmn Hmx15; lia).
  assert (H16 : 2 ^ 16 <= 2 ^ (16 - mn) * Z.of_nat (length l)).
  { assert (HsumNN : 0 <= rem_syms_aux (Z.to_nat (16 - mn))
                            (pre_cnt l) mn)
      by (apply rem_syms_aux_nonneg; exact Hnn).
    clear -Hle Hsum Hpos HsumNN. nia. }
  assert (Hsplitp : 2 ^ (16 - mn) * 2 ^ mn = 2 ^ 16).
  { rewrite <- Z.pow_add_r by (clear -Hmn Hmx15; lia).
    f_equal. clear; lia. }
  clear -H16 Hsplitp Hpos. nia.
Qed.

(* ==========================================================================
   7.  A1 — regime_split (frozen statement, EnoughFitsDesign).
   ========================================================================== *)

Theorem regime_split : regime_split_STMT.
Proof.
  unfold regime_split_STMT.
  intros ty l root0 c st BAND CAP HP.
  destruct (it_pre_go_fields ty l root0 c st HP)
    as (Hty & Hroot & Hmax & _ & _ & _ & _ & Hmx & (lft & Hk & Hinc)).
  assert (Hmx15 : 1 <= pre_mx l <= 15).
  { pose proof (it_findmax_le 15%nat MAXBITS (pre_cnt l)
                  ltac:(unfold MAXBITS; clear; lia)
                  ltac:(unfold MAXBITS; clear; lia)) as HB.
    unfold pre_mx, MAXBITS in *. clear -HB Hmx; lia. }
  destruct (it_findmin_spec 16%nat 1 (pre_mx l) (pre_cnt l)
              ltac:(clear -Hmx15; lia) ltac:(clear -Hmx15; lia))
    as [Hmn _].
  fold (pre_mn l) in Hmn.
  (* the band's root0 and symbol budget *)
  assert (HB : (root0 = 9 /\ Z.of_nat (length l) <= 286 /\ ty = CT_LENS)
            \/ (root0 = 6 /\ Z.of_nat (length l) <= 30 /\ ty = CT_DISTS)).
  { unfold band2 in BAND.
    destruct BAND as [(H1 & H2 & H3) | (H1 & H2 & H3)];
      [left | right]; (split; [exact H3|]);
      (split; [clear -H2; lia | exact H1]). }
  unfold pre_r in Hroot.
  destruct (Z.ltb_spec (pre_mx l) root0) as [Hlt|Hge].
  - (* r1 = mx; mn <= mx forces r = mx *)
    right.
    rewrite Hroot, Hmax.
    destruct (Z.ltb_spec (pre_mx l) (pre_mn l)) as [Hc2|Hc2];
      [exfalso; clear -Hmn Hc2; lia | reflexivity].
  - (* r1 = root0; completeness forces mn <= root0 *)
    left.
    (* incomplete = false and mx >= root0 >= 6 > 1 force lft = 0 *)
    assert (Hroot06 : root0 = 9 \/ root0 = 6)
      by (destruct HB as [(H1 & _)|(H1 & _)]; [left|right]; exact H1).
    assert (Hlft0 : lft = 0).
    { unfold it_incomplete in Hinc.
      apply andb_false_iff in Hinc.
      destruct Hinc as [Hl|Hr].
      - pose proof (it_kraft_nonneg 15%nat 1 1 (pre_cnt l) lft
                      ltac:(clear; lia) Hk) as Hnn.
        apply Z.ltb_ge in Hl. clear -Hl Hnn; lia.
      - exfalso.
        apply orb_false_iff in Hr. destruct Hr as [_ Hr2].
        apply negb_false_iff, Z.eqb_eq in Hr2.
        clear -Hr2 Hge Hroot06; lia. }
    subst lft.
    pose proof (complete_min_small l Hmx Hk) as Hpow.
    assert (Hmn_small : pre_mn l <= root0).
    { destruct (Z.le_gt_cases (pre_mn l) root0) as [Hok|Hbad];
        [exact Hok|exfalso].
      assert (Hstep : 2 ^ (root0 + 1) <= 2 ^ pre_mn l)
        by (apply Z.pow_le_mono_r; clear -Hbad Hroot06; lia).
      destruct HB as [(H1 & H2 & _)|(H1 & H2 & _)]; subst root0.
      - change (2 ^ (9 + 1)) with 1024 in Hstep.
        clear -Hstep Hpow H2; lia.
      - change (2 ^ (6 + 1)) with 128 in Hstep.
        clear -Hstep Hpow H2; lia. }
    rewrite Hroot.
    destruct (Z.ltb_spec root0 (pre_mn l)) as [Hc2|Hc2];
      [exfalso; clear -Hmn_small Hc2; lia | reflexivity].
Qed.

(* ==========================================================================
   8.  A2 — regime_b (frozen statement; NO band2 narrowing needed).
   ========================================================================== *)

Lemma no_open_step : forall c st,
  (forall s, x_lens c (x_work c s) <= x_max c) ->
  x_root c = x_max c ->
  s_len st <= x_max c ->
  (exists st', it_step c st = ItCont st' /\ s_len st' <= x_max c)
  \/ (exists st', it_step c st = ItBreak st').
Proof.
  intros c st HW HR HL.
  unfold it_step. cbv zeta.
  destruct ((zset (s_count st) (s_len st) (s_count st (s_len st) - 1)
               (s_len st) =? 0)%Z) eqn:Hhit.
  - (* count for this length exhausted *)
    destruct ((s_len st =? x_max c)%Z) eqn:Hbrk; cbn [andb].
    + right. eexists. reflexivity.
    + (* len1 = lens (work (sym+1)) <= max = root: no opening *)
      pose proof (HW (s_sym st + 1)) as HL1.
      destruct (Z.ltb_spec (x_root c)
                  (x_lens c (x_work c (s_sym st + 1)))) as [Hop|Hop].
      * exfalso. clear -Hop HL1 HR; lia.
      * cbn [andb].
        left. eexists. split; [reflexivity|]. cbn [s_len].
        exact HL1.
  - (* same length continues *)
    cbn [andb].
    destruct (Z.ltb_spec (x_root c) (s_len st)) as [Hop|Hop].
    + exfalso. clear -Hop HL HR; lia.
    + cbn [andb].
      left. eexists. split; [reflexivity|]. cbn [s_len].
      exact HL.
Qed.

Lemma no_open_loop : forall c,
  (forall s, x_lens c (x_work c s) <= x_max c) ->
  x_root c = x_max c ->
  forall n st t,
    s_len st <= x_max c ->
    it_loop n c st <> Some (ItOverflow t).
Proof.
  intros c HW HR.
  induction n as [|k IH]; intros st t HL; cbn [it_loop];
    [discriminate|].
  destruct (no_open_step c st HW HR HL)
    as [(st' & HS & HL') | (st' & HS)]; rewrite HS.
  - apply IH. exact HL'.
  - discriminate.
Qed.

Theorem regime_b : regime_b_STMT.
Proof.
  unfold regime_b_STMT.
  intros ty l root0 c st CAP HP HRM n t.
  destruct (it_pre_go_fields ty l root0 c st HP)
    as (_ & _ & Hmax & Hlens & Hwork & Hslen & _ & Hmx & _).
  assert (Hmx15 : 1 <= pre_mx l <= 15).
  { pose proof (it_findmax_le 15%nat MAXBITS (pre_cnt l)
                  ltac:(unfold MAXBITS; clear; lia)
                  ltac:(unfold MAXBITS; clear; lia)) as HB.
    unfold pre_mx, MAXBITS in *. clear -HB Hmx; lia. }
  destruct (it_findmin_spec 16%nat 1 (pre_mx l) (pre_cnt l)
              ltac:(clear -Hmx15; lia) ltac:(clear -Hmx15; lia))
    as [Hmn _].
  fold (pre_mn l) in Hmn.
  apply no_open_loop.
  - intros s. rewrite Hlens, Hwork, Hmax.
    apply work_lens_le_max; [exact CAP | exact Hmx].
  - exact HRM.
  - rewrite Hslen, Hmax. clear -Hmn; lia.
Qed.

(* ==========================================================================
   9.  The assembly instantiation check: with A1/A2 proven, the capped
       target reduces to the ONE remaining hypothesis (A3, the
       B-cluster's theorem).  Kept as the honest Section form.
   ========================================================================== *)

Section AssemblyCheck.
  Hypothesis A3 : main_arm_STMT.

  Theorem enough_fits_capped_mod_A3 : EnoughFits_STMT.
  Proof.
    exact (enough_fits_capped regime_split regime_b A3).
  Qed.
End AssemblyCheck.
