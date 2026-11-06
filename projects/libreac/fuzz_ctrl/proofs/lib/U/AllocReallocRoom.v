From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0g YO0h YO0w YO0s YO11 YO15 YO12 YO0z YO14 YO0u YO0q YO0v YO0t YO0x YO03 YO0m YO0p.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0j YO0n YO0l YO0o YO0d YM02.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0d_cf YO03_cf YO0n_cf PlaceCapW.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require AgreeLim.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import AllocSI AllocRealloc AllocReallocOK.
Import ListNotations.
Local Open Scope Z_scope.

(* The room bound of the cut-free walk (roomcf) for realloc: every charged request of the tree fits under X, and
   every slotted request has the slot room when X <= LIM_AG. *)

(* The move branch is malloc then free; free has no charged or slotted request in any state. *)
Lemma roomcf_move s p n X : WF s -> II s -> 0 <= n -> ROOM4 s n ->
  LIVE_UB s + 3 * PGSZ + area s + Z.max MMAX (page_round (n + IB + UNIT)) <= X ->
  (X <= AgreeLim.LIM_AG -> SLOT_UB s + 5 + KRES <= slot_capW (Z.max (Z.max MMAX (page_round (n + IB + UNIT))) (area s))) ->
  roomcf X (realloc_move p n s).
Proof.
  intros HW HII Hn R4 RX RS. unfold realloc_move, bind.
  apply roomcf_ibind_all; [exact (roomcf_malloc n s X (malloc_reqs_ok s n HW Hn) HII Hn R4 RX RS)|].
  intros [[q|] s1]; [|exact I].
  exact (presR_bind _ _ (r_free (Some p)) (fun _ => presR_ret _) X s1).
Qed.

Theorem roomcf_realloc : forall s p k n X, WF s -> In (p, k) (user_blocks s) -> II s -> 0 <= n < 2 ^ 62 -> ROOM4 s n ->
  page_round (n + IB + UNIT) + PGSZ <= MG_REQ ->
  LIVE_UB s + 3 * PGSZ + area s + Z.max MMAX (page_round (n + IB + UNIT)) <= X ->
  (X <= AgreeLim.LIM_AG -> SLOT_UB s + 5 + KRES <= slot_capW (Z.max (Z.max MMAX (page_round (n + IB + UNIT) + PGSZ)) (area s))) ->
  roomcf X (realloc (Some p) n s).
Proof.
  intros s p k n X HW Hin HII Hn R4 Hrq RX RS.
  assert (MX0 : 0 < MMAX) by (unfold MMAX; reflexivity).
  assert (AW : slot_capW (Z.max (Z.max MMAX (page_round (n + IB + UNIT) + PGSZ)) (area s)) <=
               slot_capW (Z.max (Z.max MMAX (page_round (n + IB + UNIT))) (area s)))
    by (apply slot_capW_anti; unfold PGSZ; lia).
  assert (Ov : size_overflows n = false) by (unfold size_overflows; apply Z.leb_gt; lia).
  destruct (user_blocks_frame s p k HW Hin) as (g & am & i & fr & Hu & Hi & Hfr & Hk & En & Ep).
  assert (Hff : find_frame_in (st_metas s) p = Some (g, i))
    by (rewrite Ep; exact (find_frame_in_spec [] None U0 s HW g am i fr Hu Hi Hfr)).
  pose proof (inv_groups HW g am Hu) as (_ & _ & Hsl & _).
  assert (Hoff : 0 <= fr_off fr <= 255).
  { pose proof (Hsl i Hi) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (_ & _ & (_ & Ho & _) & _). exact Ho. }
  pose proof (roomcf_move s p n X HW HII (proj1 Hn) R4 RX ltac:(intros HXl; specialize (RS HXl); lia)) as HM.
  unfold realloc. rewrite Ov. unfold bind.
  rewrite (ra_ffe p s (g, i) Hff). cbn [ibind fst snd].
  rewrite (ra_getm g s am (proj1 (usedX_MT _ _ _ _ Hu))). cbn [ibind]. rewrite Hfr.
  destruct ((n <=? stride_of am - IB - UNIT * fr_off fr) && (n <? MMAP_THRESHOLD) && (am_sc am <=? size_to_class n + 1)).
  - cbn [ibind fst snd bind setm modify ret]. exact I.
  - destruct ((48 <=? am_sc am) && (MMAP_THRESHOLD <=? n)); [|exact HM].
    destruct (am_sc am =? 63); cbn [ibind massert ret fail]; [|exact I].
    destruct (am_maplen am * 4096 =? page_round (n + UNIT * fr_off fr + UNIT + IB)).
    + cbn [ibind fst snd bind setm modify ret]. exact I.
    + cbn [ibind ask roomcf].
      pose proof (LIVE_UB_ok s (proj1 HII)) as HL.
      pose proof (page_round_add (n + IB + UNIT) (UNIT * fr_off fr) ltac:(unfold UNIT, PGSZ; lia)) as PA.
      pose proof (page_round_ge (n + IB + UNIT + UNIT * fr_off fr)) as PG.
      assert (Ha : 0 <= area s) by (unfold area, PGSZ; pose proof (Z.pow_nonneg 2 (shift s) ltac:(lia)); lia).
      pose proof (Z.le_max_r MMAX (page_round (n + IB + UNIT))) as Mx.
      split; [|split].
      * intros _. cbn [req_len].
        replace (n + UNIT * fr_off fr + UNIT + IB) with (n + IB + UNIT + UNIT * fr_off fr) by lia.
        unfold PGSZ in *. lia.
      * intros _ HXl. specialize (RS HXl). unfold slot_room. cbn [req_len].
        replace (n + UNIT * fr_off fr + UNIT + IB) with (n + IB + UNIT + UNIT * fr_off fr) by lia.
        pose proof (SLOT_UB_ok s (proj1 HII)) as HS.
        assert (AR : slot_capW (Z.max (Z.max MMAX (page_round (n + IB + UNIT) + PGSZ)) (area s)) <=
                     slot_capW (page_round (n + IB + UNIT + UNIT * fr_off fr)))
          by (apply slot_capW_anti; unfold UNIT, IB in *; lia).
        unfold MG_REQ, PGSZ, UNIT, IB in *. lia.
      * intros z _. destruct (negb (z =? 0)); cbn [ibind fst snd]; [|exact HM].
        cbn [ibind fst snd bind setm modify ret new_region get put upd_region]. exact I.
Qed.

Theorem roomcf_realloc_null : forall s n X, WF s -> II s -> 0 <= n < 2 ^ 62 -> ROOM4 s n ->
  LIVE_UB s + 3 * PGSZ + area s + Z.max MMAX (page_round (n + IB + UNIT)) <= X ->
  (X <= AgreeLim.LIM_AG -> SLOT_UB s + 5 + KRES <= slot_capW (Z.max (Z.max MMAX (page_round (n + IB + UNIT))) (area s))) ->
  roomcf X (realloc None n s).
Proof.
  intros s n X HW HII Hn R4 RX RS.
  exact (roomcf_malloc n s X (malloc_reqs_ok s n HW (proj1 Hn)) HII (proj1 Hn) R4 RX RS).
Qed.
