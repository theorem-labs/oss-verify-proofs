(** * OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.GtItTotal — T5: [it_model] never hits
      its fuel (Q4, zlib-rt, 2026-08-19)

    [Inftrees.v]'s own note (:442-454) states the split: [it_step_decreases]
    gives "every fall-through trip does [sym++], so [S codes] bounds the trip
    count", and names the OPEN half — "[sym] cannot reach [codes] without the
    loop having taken [ItBreak]" — as needing the Kraft/count facts, with no
    home.  This file is that home.

    The count facts were already Qed in [ItGTblSortWin] (checked before
    pricing): [sw_places] (each offs-window of the sorted work array holds
    exactly the symbols of its length), [sw_window_exists] (the windows tile
    [[0, N)]), the offs step/monotonicity algebra, and the findmax/findmin
    scan specs.  What this file adds is the LOOP-side invariant: the trip
    cursor [s_sym] walks the windows left to right, [s_count] is the suffix
    histogram, and the walk's last trip — position [N-1], which sits in
    [max]'s window because the windows above [max] are empty — fires the
    [ItBreak] condition.  Fuel [S (Z.to_nat codes)] then suffices because
    [N <= codes] (each counted symbol is one of the [codes] inputs).

    PREMISE: [0 <= lens i <= 15] on the [codes] inputs — [sw_places]'s own
    premise.  Every caller has it structurally: [inflate.c]'s three call
    sites build [lens] from 3-bit reads (LENLENS), decoded code-lengths
    clamped at 15 (CODELENS), or fixed tables.  No [it_wf] is needed. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ItGTblSortWin.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

Definition LensBounded (lens : zarr) (codes : Z) : Prop :=
  forall i, 0 <= i < codes -> 0 <= lens i <= 15.

(* ######################################################################### *)
(* 1.  The histogram sums to at most [codes]                                  *)
(* ######################################################################### *)

Definition sumc (cnt : zarr) : Z :=
  cnt 1 + cnt 2 + cnt 3 + cnt 4 + cnt 5 + cnt 6 + cnt 7 + cnt 8
  + cnt 9 + cnt 10 + cnt 11 + cnt 12 + cnt 13 + cnt 14 + cnt 15.

Lemma sumc_zset_out : forall cnt k v,
  ~ (1 <= k <= 15) -> sumc (zset cnt k v) = sumc cnt.
Proof.
  intros cnt k v Hk. unfold sumc, zset.
  repeat match goal with
         | |- context[if Z.eqb ?a k then _ else _] =>
             destruct (Z.eqb_spec a k); [lia|]
         end.
  reflexivity.
Qed.

Lemma sumc_zset_in : forall cnt k v,
  1 <= k <= 15 -> sumc (zset cnt k v) = sumc cnt + (v - cnt k).
Proof.
  intros cnt k v Hk. unfold sumc, zset.
  assert (H : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7
              \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13
              \/ k = 14 \/ k = 15) by lia.
  clear Hk.
  destruct H as [H|H]. { subst k. cbn [Z.eqb Pos.eqb]. lia. }
  destruct H as [H|H]. { subst k. cbn [Z.eqb Pos.eqb]. lia. }
  destruct H as [H|H]. { subst k. cbn [Z.eqb Pos.eqb]. lia. }
  destruct H as [H|H]. { subst k. cbn [Z.eqb Pos.eqb]. lia. }
  destruct H as [H|H]. { subst k. cbn [Z.eqb Pos.eqb]. lia. }
  destruct H as [H|H]. { subst k. cbn [Z.eqb Pos.eqb]. lia. }
  destruct H as [H|H]. { subst k. cbn [Z.eqb Pos.eqb]. lia. }
  destruct H as [H|H]. { subst k. cbn [Z.eqb Pos.eqb]. lia. }
  destruct H as [H|H]. { subst k. cbn [Z.eqb Pos.eqb]. lia. }
  destruct H as [H|H]. { subst k. cbn [Z.eqb Pos.eqb]. lia. }
  destruct H as [H|H]. { subst k. cbn [Z.eqb Pos.eqb]. lia. }
  destruct H as [H|H]. { subst k. cbn [Z.eqb Pos.eqb]. lia. }
  destruct H as [H|H]. { subst k. cbn [Z.eqb Pos.eqb]. lia. }
  destruct H as [H|H]. { subst k. cbn [Z.eqb Pos.eqb]. lia. }
  subst k. cbn [Z.eqb Pos.eqb]. lia.
Qed.

Lemma sumc_zzero : sumc zzero = 0.
Proof. reflexivity. Qed.

Lemma sumc_le_codes_nat : forall n lens,
  (forall i, 0 <= i < Z.of_nat n -> 0 <= lens i <= 15) ->
  sumc (it_count n 0 lens zzero) <= Z.of_nat n.
Proof.
  induction n as [|n IH]; intros lens Hb.
  - cbn [it_count]. rewrite sumc_zzero. lia.
  - rewrite (count_snoc0 n lens zzero).
    assert (Hbn : 0 <= lens (Z.of_nat n) <= 15) by (apply Hb; lia).
    assert (Hprev : sumc (it_count n 0 lens zzero) <= Z.of_nat n)
      by (apply IH; intros i Hi; apply Hb; lia).
    destruct (Z.le_gt_cases 1 (lens (Z.of_nat n))) as [Hge1|Hlt1].
    + rewrite sumc_zset_in by lia. lia.
    + rewrite sumc_zset_out by lia. lia.
Qed.

Lemma sw_N_is_sumc : forall cnt, sw_offs cnt 15 + cnt 15 = sumc cnt.
Proof.
  intros cnt.
  pose proof (sw_offs_1 cnt) as O1.
  pose proof (sw_offs_step' cnt 1 2 ltac:(lia) eq_refl) as S1.
  pose proof (sw_offs_step' cnt 2 3 ltac:(lia) eq_refl) as S2.
  pose proof (sw_offs_step' cnt 3 4 ltac:(lia) eq_refl) as S3.
  pose proof (sw_offs_step' cnt 4 5 ltac:(lia) eq_refl) as S4.
  pose proof (sw_offs_step' cnt 5 6 ltac:(lia) eq_refl) as S5.
  pose proof (sw_offs_step' cnt 6 7 ltac:(lia) eq_refl) as S6.
  pose proof (sw_offs_step' cnt 7 8 ltac:(lia) eq_refl) as S7.
  pose proof (sw_offs_step' cnt 8 9 ltac:(lia) eq_refl) as S8.
  pose proof (sw_offs_step' cnt 9 10 ltac:(lia) eq_refl) as S9.
  pose proof (sw_offs_step' cnt 10 11 ltac:(lia) eq_refl) as S10.
  pose proof (sw_offs_step' cnt 11 12 ltac:(lia) eq_refl) as S11.
  pose proof (sw_offs_step' cnt 12 13 ltac:(lia) eq_refl) as S12.
  pose proof (sw_offs_step' cnt 13 14 ltac:(lia) eq_refl) as S13.
  pose proof (sw_offs_step' cnt 14 15 ltac:(lia) eq_refl) as S14.
  unfold sumc. lia.
Qed.

(** The tiled extent, and its bound. *)
Definition sw_N (lens : zarr) (codes : Z) : Z :=
  sw_offs (sw_cnt lens codes) 15 + sw_cnt lens codes 15.

Lemma sw_N_le_codes : forall lens codes,
  0 <= codes -> LensBounded lens codes -> sw_N lens codes <= codes.
Proof.
  intros lens codes Hc Hb. unfold sw_N. rewrite sw_N_is_sumc.
  unfold sw_cnt.
  pose proof (sumc_le_codes_nat (Z.to_nat codes) lens) as H.
  rewrite Z2Nat.id in H by lia.
  apply H. intros i Hi. apply Hb. lia.
Qed.

(* ######################################################################### *)
(* 2.  findmin characterisation, and the zero prefix of the offsets           *)
(* ######################################################################### *)

Lemma findmin_result : forall n m mx cnt,
  it_findmin n m mx cnt = mx
  \/ (m <= it_findmin n m mx cnt < mx /\ cnt (it_findmin n m mx cnt) <> 0).
Proof.
  induction n as [|n IH]; intros m mx cnt; cbn [it_findmin].
  - now left.
  - destruct (Z.geb m mx) eqn:Hge; [now left|].
    rewrite Z.geb_leb in Hge. apply Z.leb_gt in Hge.
    destruct (Z.eqb (cnt m) 0) eqn:Hz.
    + destruct (IH (m + 1) mx cnt) as [H|[H1 H2]]; [now left|].
      right. split; [lia | exact H2].
    + apply Z.eqb_neq in Hz. right. split; [lia | exact Hz].
Qed.

Lemma sw_offs_zero_prefix_nat : forall k cnt,
  1 + Z.of_nat k <= 15 ->
  (forall j, 1 <= j < 1 + Z.of_nat k -> cnt j = 0) ->
  sw_offs cnt (1 + Z.of_nat k) = 0.
Proof.
  induction k as [|k IH]; intros cnt Hle Hz.
  - apply sw_offs_1.
  - replace (1 + Z.of_nat (S k)) with ((1 + Z.of_nat k) + 1) by lia.
    rewrite (sw_offs_step' cnt (1 + Z.of_nat k) _ ltac:(lia) eq_refl).
    rewrite IH by (try lia; intros j Hj; apply Hz; lia).
    rewrite (Hz (1 + Z.of_nat k)) by lia. lia.
Qed.

Lemma sw_offs_zero_prefix : forall cnt l,
  1 <= l <= 15 ->
  (forall j, 1 <= j < l -> cnt j = 0) ->
  sw_offs cnt l = 0.
Proof.
  intros cnt l Hl Hz.
  replace l with (1 + Z.of_nat (Z.to_nat (l - 1))) by lia.
  apply sw_offs_zero_prefix_nat; [lia|].
  intros j Hj. apply Hz. lia.
Qed.

(* ######################################################################### *)
(* 3.  Window geometry: what sits just past a finished window                 *)
(* ######################################################################### *)

(** When the cursor steps off the end of [len]'s window and lands in some
    window [l'], that window starts EXACTLY there, is strictly to the right,
    and every window in between is empty. *)
Lemma window_after : forall cnt len s l',
  (forall i, 1 <= i <= 15 -> 0 <= cnt i) ->
  1 <= len <= 15 -> 1 <= l' <= 15 ->
  s = sw_offs cnt len + cnt len ->
  sw_offs cnt l' <= s < sw_offs cnt l' + cnt l' ->
  len < l' /\ sw_offs cnt l' = s /\ (forall l, len < l < l' -> cnt l = 0).
Proof.
  intros cnt len s l' Hnn Hlen Hl' Hs Hw.
  assert (Hlt : len < l').
  { destruct (Z.lt_ge_cases len l') as [H|H]; [exact H|]. exfalso.
    destruct (Z.eqb_spec l' 15) as [->|Hne].
    - (* l' = 15 <= len <= 15, so len = 15 and s = off 15 + cnt 15 *)
      assert (len = 15) by lia. subst len. lia.
    - destruct (Z.eqb_spec l' len) as [->|Hne2]; [lia|].
      pose proof (sw_offs_step' cnt l' (l' + 1) ltac:(lia) eq_refl) as St.
      pose proof (sw_offs_mono cnt (l' + 1) len Hnn ltac:(lia) ltac:(lia)) as Hm.
      pose proof (Hnn len Hlen). lia. }
  assert (Hlen14 : len <= 14) by lia.
  pose proof (sw_offs_step' cnt len (len + 1) ltac:(lia) eq_refl) as Snext.
  assert (Heq : sw_offs cnt l' = s).
  { pose proof (sw_offs_mono cnt (len + 1) l' Hnn ltac:(lia) ltac:(lia)) as Hm.
    lia. }
  split; [exact Hlt|]. split; [exact Heq|].
  intros l Hl.
  pose proof (sw_offs_step' cnt l (l + 1) ltac:(lia) eq_refl) as Sl.
  pose proof (sw_offs_mono cnt (len + 1) l Hnn ltac:(lia) ltac:(lia)) as Hm1.
  pose proof (sw_offs_mono cnt (l + 1) l' Hnn ltac:(lia) ltac:(lia)) as Hm2.
  pose proof (Hnn l ltac:(lia)). lia.
Qed.

(* ######################################################################### *)
(* 4.  The loop invariant                                                     *)
(* ######################################################################### *)

(** The trip cursor [s_sym] sits inside [s_len]'s window of the sorted work
    array, and [s_count] is the SUFFIX histogram: exhausted below the cursor's
    window, partially consumed at it, untouched above. *)
Record TotInv (lens : zarr) (codes : Z) (c : ItCtx) (st : ItSt) : Prop := mkTotInv {
  ti_lens : x_lens c = lens;
  ti_work : x_work c = sw_work lens codes;
  ti_max  : x_max c = it_findmax 15%nat MAXBITS (sw_cnt lens codes);
  ti_mx   : 1 <= x_max c <= 15;
  ti_sym  : 0 <= s_sym st;
  ti_len  : 1 <= s_len st <= 15;
  ti_cur  : sw_offs (sw_cnt lens codes) (s_len st) <= s_sym st
            < sw_offs (sw_cnt lens codes) (s_len st) + sw_cnt lens codes (s_len st);
  ti_cnt  : forall l, 1 <= l <= 15 ->
            s_count st l
            = (if Z.ltb l (s_len st) then 0
               else if Z.eqb l (s_len st)
                    then sw_cnt lens codes l
                         - (s_sym st - sw_offs (sw_cnt lens codes) l)
                    else sw_cnt lens codes l)
}.

Lemma ti_sym_lt_N : forall lens codes c st,
  TotInv lens codes c st -> s_sym st < sw_N lens codes.
Proof.
  intros lens codes c st [Hl Hw Hm HmR Hs Hlen Hcur Hcnt]. unfold sw_N.
  pose proof (sw_cnt_nonneg lens codes) as Hnn0.
  assert (Hnn : forall i, 1 <= i <= 15 -> 0 <= sw_cnt lens codes i)
    by (intros; apply Hnn0).
  destruct (Z.eqb_spec (s_len st) 15) as [Heq|Hne]; [rewrite Heq in Hcur; lia|].
  pose proof (sw_offs_step' (sw_cnt lens codes) (s_len st) (s_len st + 1)
                ltac:(lia) eq_refl) as St.
  pose proof (sw_offs_mono (sw_cnt lens codes) (s_len st + 1) 15 Hnn
                ltac:(lia) ltac:(lia)) as Hm15.
  pose proof (Hnn 15 ltac:(lia)). lia.
Qed.

(** The current length never exceeds the scan's max: its window is nonempty,
    and the counts above [max] are all zero. *)
Lemma ti_len_le_max : forall lens codes c st,
  TotInv lens codes c st -> s_len st <= x_max c.
Proof.
  intros lens codes c st INV.
  destruct INV as [Hl Hw Hm HmR Hs Hlen Hcur Hcnt].
  destruct (Z.le_gt_cases (s_len st) (x_max c)) as [H|H]; [exact H|]. exfalso.
  pose proof (proj1 (sw_findmax_15 (sw_cnt lens codes))) as Hz.
  rewrite <- Hm in Hz.
  assert (Hz0 : sw_cnt lens codes (s_len st) = 0)
    by (apply Hz; unfold MAXBITS; lia).
  lia.
Qed.

(** The max window is nonempty. *)
Lemma ti_cnt_max_pos : forall lens codes c st,
  TotInv lens codes c st -> 1 <= sw_cnt lens codes (x_max c).
Proof.
  intros lens codes c st INV.
  pose proof (ti_max _ _ _ _ INV) as Hm.
  pose proof (ti_mx _ _ _ _ INV) as HmR.
  pose proof (sw_cnt_nonneg lens codes (x_max c)) as Hnn.
  destruct (proj2 (sw_findmax_15 (sw_cnt lens codes))) as [H0|[_ Hne]];
    rewrite <- Hm in *; lia.
Qed.

(* ######################################################################### *)
(* 5.  One trip preserves it                                                  *)
(* ######################################################################### *)

(** All the arithmetic of a fall-through trip, over the three fields the
    invariant reads.  [st'] is abstract so both [ItCont] records of
    [it_step] (sub-table and plain) discharge with the same lemma. *)
Lemma tot_advance : forall lens codes c st st',
  0 <= codes -> LensBounded lens codes ->
  TotInv lens codes c st ->
  (Z.eqb (s_count st (s_len st) - 1) 0 && Z.eqb (s_len st) (x_max c)) = false ->
  s_sym st' = s_sym st + 1 ->
  s_len st' = (if Z.eqb (s_count st (s_len st) - 1) 0
               then x_lens c (x_work c (s_sym st + 1)) else s_len st) ->
  s_count st' = zset (s_count st) (s_len st) (s_count st (s_len st) - 1) ->
  TotInv lens codes c st'.
Proof.
  intros lens codes c st st' Hc Hb INV Ebrk Hsym' Hlen' Hcnt'.
  pose proof (ti_len_le_max _ _ _ _ INV) as Hlemax.
  pose proof (ti_cnt_max_pos _ _ _ _ INV) as Hmaxpos.
  destruct INV as [Hl Hw Hm HmR Hs Hlen Hcur Hcnt].
  set (cnt := sw_cnt lens codes) in *.
  pose proof (sw_cnt_nonneg lens codes) as Hnn0.
  assert (Hnn : forall i, 1 <= i <= 15 -> 0 <= cnt i) by (intros; apply Hnn0).
  assert (Hself : s_count st (s_len st)
                  = cnt (s_len st) - (s_sym st - sw_offs cnt (s_len st))).
  { rewrite (Hcnt (s_len st) Hlen).
    rewrite Z.ltb_irrefl, Z.eqb_refl. reflexivity. }
  destruct (Z.eqb_spec (s_count st (s_len st) - 1) 0) as [Hhit|Hmiss].
  - (* window exhausted; the break case is excluded, so s_len < max *)
    assert (Hnmax : s_len st <> x_max c).
    { intros Habs. rewrite Habs in Ebrk.
      rewrite (proj2 (Z.eqb_eq _ _) eq_refl) in Ebrk.
      cbn in Ebrk. discriminate Ebrk. }
    assert (Hsymend : s_sym st = sw_offs cnt (s_len st) + cnt (s_len st) - 1)
      by lia.
    assert (Hltmax : s_len st < x_max c) by lia.
    (* sym+1 lands at off (s_len + 1), which is inside [0, N) *)
    assert (Hs1 : s_sym st + 1 = sw_offs cnt (s_len st) + cnt (s_len st)) by lia.
    assert (HsltN : s_sym st + 1 < sw_N lens codes).
    { unfold sw_N. fold cnt.
      destruct (Z.eqb_spec (x_max c) 15) as [Hmx15|Hmxne].
      - (* off(len+1) <= off(max) < off(max)+cnt(max) = N *)
        pose proof (sw_offs_step' cnt (s_len st) (s_len st + 1)
                      ltac:(lia) eq_refl) as St.
        pose proof (sw_offs_mono cnt (s_len st + 1) 15 Hnn
                      ltac:(lia) ltac:(lia)) as Hm15.
        rewrite Hmx15 in Hmaxpos. lia.
      - pose proof (sw_offs_step' cnt (s_len st) (s_len st + 1)
                      ltac:(lia) eq_refl) as St.
        pose proof (sw_offs_mono cnt (s_len st + 1) (x_max c) Hnn
                      ltac:(lia) ltac:(lia)) as HmA.
        pose proof (sw_offs_step' cnt (x_max c) (x_max c + 1)
                      ltac:(lia) eq_refl) as Stm.
        pose proof (sw_offs_mono cnt (x_max c + 1) 15 Hnn
                      ltac:(lia) ltac:(lia)) as HmB.
        pose proof (Hnn 15 ltac:(lia)). lia. }
    (* which window holds sym+1 *)
    destruct (sw_window_exists lens codes (s_sym st + 1) Hc Hb
                ltac:(unfold sw_N in HsltN; lia)) as (l' & Hl'r & Hl'w).
    fold cnt in Hl'w.
    assert (Hplace : lens (sw_work lens codes (s_sym st + 1)) = l')
      by (apply sw_places; try assumption; lia).
    destruct (window_after cnt (s_len st) (s_sym st + 1) l' Hnn Hlen Hl'r
                Hs1 Hl'w) as (Hgt & Hoff' & Hmid).
    constructor; try assumption.
    + lia.
    + (* ti_len *)
      rewrite Hlen'. cbv iota.
      rewrite Hl, Hw, Hplace. lia.
    + (* ti_cur *)
      rewrite Hlen', Hsym'. cbv iota.
      rewrite Hl, Hw, Hplace. fold cnt. lia.
    + (* ti_cnt *)
      intros l Hlr. rewrite Hcnt', Hlen', Hsym'. cbv iota.
      rewrite Hl, Hw, Hplace.
      destruct (Z.eqb_spec l (s_len st)) as [->|Hne].
      * rewrite zset_same. fold cnt.
        rewrite (proj2 (Z.ltb_lt _ _) Hgt). lia.
      * rewrite (zset_other _ _ _ _ Hne). rewrite (Hcnt l Hlr). fold cnt.
        destruct (Z.ltb_spec l (s_len st)) as [Hlt|Hge].
        { rewrite (proj2 (Z.ltb_lt l l') ltac:(lia)). reflexivity. }
        destruct (Z.ltb_spec l l') as [Hlt'|Hge'].
        { (* s_len < l < l': the empty middle *)
          assert (Hz : cnt l = 0) by (apply Hmid; lia).
          rewrite (proj2 (Z.eqb_neq l (s_len st)) Hne).
          destruct (Z.eqb_spec l l') as [->|_]; lia. }
        destruct (Z.eqb_spec l l') as [->|Hne'].
        { rewrite (proj2 (Z.eqb_neq l' (s_len st)) ltac:(lia)). lia. }
        { rewrite (proj2 (Z.eqb_neq l (s_len st)) Hne). lia. }
  - (* same window, one more consumed *)
    constructor; try assumption.
    + lia.
    + rewrite Hlen'. cbv iota. exact Hlen.
    + rewrite Hlen', Hsym'. cbv iota. fold cnt.
      lia.
    + intros l Hlr. rewrite Hcnt', Hlen', Hsym'. cbv iota.
      destruct (Z.eqb_spec l (s_len st)) as [->|Hne].
      * rewrite zset_same. rewrite Z.ltb_irrefl. fold cnt. lia.
      * rewrite (zset_other _ _ _ _ Hne). rewrite (Hcnt l Hlr). fold cnt.
        destruct (Z.ltb_spec l (s_len st)) as [_|_]; [reflexivity|].
        rewrite (proj2 (Z.eqb_neq l (s_len st)) Hne). reflexivity.
Qed.

(** Wiring [tot_advance] to [it_step]'s two [ItCont] shapes ([GtUsedBits.
    used_mono_step]'s destruct style: underscores, never [injection]). *)
Lemma tot_step : forall lens codes c st,
  0 <= codes -> LensBounded lens codes ->
  TotInv lens codes c st ->
  match it_step c st with
  | ItCont st' => TotInv lens codes c st' /\ s_sym st' = s_sym st + 1
  | _ => True
  end.
Proof.
  intros lens codes c st Hc Hb INV.
  unfold it_step. cbv zeta.
  destruct (Z.eqb (zset (s_count st) (s_len st) (s_count st (s_len st) - 1) (s_len st)) 0
            && Z.eqb (s_len st) (x_max c)) eqn:Ebrk; [exact I|].
  rewrite zset_same in Ebrk.
  destruct ((Z.ltb (x_root c) _) && negb (Z.eqb _ (s_low st))) eqn:Esub.
  - destruct (it_enough (x_type c) _) eqn:Eov; [exact I|].
    rewrite !zset_same.
    split.
    + apply (tot_advance lens codes c st _ Hc Hb INV Ebrk); reflexivity.
    + reflexivity.
  - rewrite !zset_same.
    split.
    + apply (tot_advance lens codes c st _ Hc Hb INV Ebrk); reflexivity.
    + reflexivity.
Qed.

(* ######################################################################### *)
(* 6.  The loop exits within its fuel                                         *)
(* ######################################################################### *)

Lemma tot_loop : forall f lens codes c st,
  0 <= codes -> LensBounded lens codes ->
  TotInv lens codes c st ->
  sw_N lens codes - s_sym st <= Z.of_nat f ->
  exists r, it_loop f c st = Some r
            /\ match r with ItCont _ => False | _ => True end.
Proof.
  induction f as [|f IH]; intros lens codes c st Hc Hb INV Hfuel.
  - exfalso. pose proof (ti_sym_lt_N _ _ _ _ INV). cbn [Z.of_nat] in Hfuel. lia.
  - cbn [it_loop].
    pose proof (tot_step lens codes c st Hc Hb INV) as HS.
    destruct (it_step c st) as [st'|st'|t] eqn:E.
    + destruct HS as [INV' Hsym'].
      apply (IH lens codes c st' Hc Hb INV').
      rewrite Hsym'. rewrite Nat2Z.inj_succ in Hfuel. lia.
    + exists (ItBreak st'). split; [reflexivity | exact I].
    + exists (ItOverflow t). split; [reflexivity | exact I].
Qed.

(* ######################################################################### *)
(* 7.  The entry state satisfies the invariant                                *)
(* ######################################################################### *)

Definition PreTotOk (lens : zarr) (codes : Z) (r : ItPre) : Prop :=
  match r with PreGo c st => TotInv lens codes c st | _ => True end.

Lemma pre_tot_ok : forall ty lens codes root0 t0,
  0 <= codes -> LensBounded lens codes ->
  PreTotOk lens codes (it_pre ty lens codes root0 t0).
Proof.
  intros ty lens codes root0 t0 Hc Hb. unfold PreTotOk, it_pre. cbv zeta.
  destruct (Z.eqb (it_findmax 15%nat MAXBITS (it_count (Z.to_nat codes) 0 lens zzero)) 0)
    eqn:Emx; [exact I|].
  destruct (it_kraft 15%nat 1 1 (it_count (Z.to_nat codes) 0 lens zzero)) as [lft|];
    [|exact I].
  destruct (it_incomplete ty lft _); [exact I|].
  destruct (it_enough ty _); [exact I|].
  apply Z.eqb_neq in Emx.
  set (cnt := it_count (Z.to_nat codes) 0 lens zzero) in *.
  assert (Hcnt : cnt = sw_cnt lens codes) by reflexivity.
  set (mx := it_findmax 15%nat MAXBITS cnt) in *.
  set (mn := it_findmin 16%nat 1 mx cnt) in *.
  pose proof (sw_cnt_nonneg lens codes) as Hnn0.
  assert (Hnn : forall l, 0 <= cnt l) by (intros; rewrite Hcnt; apply Hnn0).
  (* the findmax facts *)
  pose proof (sw_findmax_15 cnt) as [Hzhi Hdisj].
  fold mx in Hzhi, Hdisj.
  destruct Hdisj as [H0|[HmxR Hmxnz]]; [contradiction|].
  assert (HmxR' : 1 <= mx <= 15) by (unfold MAXBITS in HmxR; lia).
  (* the findmin facts *)
  pose proof (sw_findmin_16 mx cnt ltac:(lia)) as [Hzlo _].
  fold mn in Hzlo.
  assert (HmnR : 1 <= mn <= 15 /\ 1 <= cnt mn).
  { destruct (findmin_result 16%nat 1 mx cnt) as [Heq|[HR Hnz]].
    - fold mn in Heq. split; [lia|]. rewrite Heq. pose proof (Hnn mx). lia.
    - fold mn in HR, Hnz. split; [lia|]. pose proof (Hnn mn). lia. }
  destruct HmnR as [HmnR Hmnpos].
  assert (Hoffmn : sw_offs cnt mn = 0).
  { apply sw_offs_zero_prefix; [lia|]. intros j Hj. apply Hzlo. lia. }
  constructor; cbn [x_lens x_work x_max s_sym s_len s_count].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact HmxR'.
  - lia.
  - exact HmnR.
  - rewrite <- Hcnt. rewrite Hoffmn. lia.
  - intros l Hl. rewrite <- Hcnt.
    destruct (Z.ltb_spec l mn) as [Hlt|Hge].
    + apply Hzlo. lia.
    + destruct (Z.eqb_spec l mn) as [->|Hne]; [rewrite Hoffmn|]; lia.
Qed.

(* ######################################################################### *)
(* 8.  T5: the model always answers                                           *)
(* ######################################################################### *)

(** [it_model]'s only [None]s are [it_loop] fuel exhaustion ([Inftrees.v]'s
    own note): with the invariant, the loop exits by trip [sw_N <= codes],
    so fuel [S (Z.to_nat codes)] always suffices.  The premise is
    [sw_places]'s own: length values within [0, 15] on the [codes] inputs
    (every caller builds [lens] from reads bounded by construction). *)
Theorem it_model_total : forall ty lens codes root0 t0,
  0 <= codes -> LensBounded lens codes ->
  it_model ty lens codes root0 t0 <> None.
Proof.
  intros ty lens codes root0 t0 Hc Hb. unfold it_model.
  pose proof (pre_tot_ok ty lens codes root0 t0 Hc Hb) as HP.
  destruct (it_pre ty lens codes root0 t0) as [|t| |c st]; try discriminate.
  cbn [PreTotOk] in HP.
  assert (Hfuel : sw_N lens codes - s_sym st <= Z.of_nat (S (Z.to_nat codes))).
  { pose proof (sw_N_le_codes lens codes Hc Hb).
    pose proof (ti_sym _ _ _ _ HP).
    rewrite Nat2Z.inj_succ, Z2Nat.id by lia. lia. }
  destruct (tot_loop (S (Z.to_nat codes)) lens codes c st Hc Hb HP Hfuel)
    as (r & Hr & Hnc).
  rewrite Hr. destruct r as [st'|st'|t']; [case Hnc | discriminate | discriminate].
Qed.

Print Assumptions it_model_total.
