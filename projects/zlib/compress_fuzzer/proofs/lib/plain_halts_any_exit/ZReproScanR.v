(** * ZReproScanR — the R39 range repair of the BL-freshness seam.

    OWNER: an earlier development run (2026-08-20; TL-approved ADDITIVE plan, third R39
    sighting).  [ScanBase.cover_both_streams_final] and
    [CoverEnd.send_tree_roundtrip_from_scan] carried
    [forall s', t_freq (ts_trees st TK_BL) s' = 0] — FALSE at every
    second-and-later flush ([bt_loop] writes internal-node freq sums at
    indices >= BL_CODES; [init_block] re-zeroes only [0, BL_CODES)).
    The infection reaches definitions: [ScanKeepsPos]'s own premise and
    [ScanCount.Budget] are whole-array, so no spelling tweak repairs the
    landed names.  This file is the ADDITIVE fix: [_r] twins over
    [ZReproG6M.RBudget] (the canonical range invariant, in-tree first;
    literal range [0 <= s < 19] = [0, BL_CODES) — one vocabulary, R38).
    The old names stay landed and true; they are simply not dischargeable
    at reachable states, and nothing should cite them there.

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees DeflateSpec ZBitsOut ZBitsBridge BwStream.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  HuffGenCodes HuffMaxBits ClStream SendItems SendGo SendGoLens SendGoWf
  HuffCover ScanCount BuildChain BtTerm SendTreeRT CoverChain ScanBase
  CoverEnd.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproG6M.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** [ScanKeepsPos], with the freshness the CALLER can actually supply:
    [init_block]'s range.  Range literal matches [RBudget]. *)
Definition ScanKeepsPosR : Prop :=
  forall tL maxcL tD maxcD bl p1 p2 s,
    0 <= maxcL <= 285 -> 0 <= maxcD <= 285 ->
    (forall i, 0 <= i <= maxcL -> 0 <= t_len tL i <= 15) ->
    (forall i, 0 <= i <= maxcD -> 0 <= t_len tD i <= 15) ->
    (forall s', 0 <= s' < 19 -> t_freq bl s' = 0) ->
    p1 = scan_tree tL maxcL bl ->
    p2 = scan_tree tD maxcD (snd p1) ->
    In s (items_syms (send_tree_items (fst p1) maxcL))
      \/ In s (items_syms (send_tree_items (fst p2) maxcD)) ->
    0 < t_freq (snd p2) s.

(** The scanned-output wellformedness, factored (the [0xffff] guard). *)
Lemma scan_output_wf : forall t maxc bl,
  0 <= maxc <= 285 ->
  (forall i, 0 <= i <= maxc -> 0 <= t_len t i <= 15) ->
  CLWf nil (send_tree_items (fst (scan_tree t maxc bl)) maxc).
Proof.
  intros t maxc bl Hmc H15.
  apply send_tree_items_wf.
  - lia.
  - unfold scan_tree. cbn [fst]. rewrite t_len_setlen_same. reflexivity.
  - unfold scan_tree. cbn [fst]. intros i Hi.
    rewrite t_len_setlen_other by lia. apply H15. lia.
Qed.

(** [scan_tree_positive] over the range freshness. *)
Lemma scan_tree_positive_r : forall t maxc bl s,
  0 <= maxc <= 285 ->
  (forall i, 0 <= i <= maxc -> 0 <= t_len t i <= 15) ->
  (forall s', 0 <= s' < 19 -> t_freq bl s' = 0) ->
  In s (items_syms (send_tree_items (fst (scan_tree t maxc bl)) maxc)) ->
  0 < t_freq (snd (scan_tree t maxc bl)) s.
Proof.
  intros t maxc bl s Hmc Hlen15 Hzero Hin.
  pose proof (items_syms_range _ nil s (scan_output_wf t maxc bl Hmc Hlen15)
                Hin) as Hs19.
  assert (Hbud : RBudget bl 0)
    by (intros s' Hs'; rewrite (Hzero s' Hs'); lia).
  rewrite (scan_tree_counts_r t maxc bl s 0 (maxc + 1) Hmc Hlen15 Hbud
             ltac:(lia) ltac:(lia) ltac:(lia)).
  rewrite (Hzero s ltac:(lia)).
  unfold hid_zcount.
  assert (Hpos : (0 < count_occ Z.eq_dec
                   (items_syms (send_tree_items
                      (fst (scan_tree t maxc bl)) maxc)) s)%nat)
    by (apply (count_occ_In Z.eq_dec); exact Hin).
  lia.
Qed.

(** THE seam theorem at the range freshness. *)
Theorem scan_keeps_pos_r : ScanKeepsPosR.
Proof.
  unfold ScanKeepsPosR.
  intros tL maxcL tD maxcD bl p1 p2 s HmcL HmcD H15L H15D Hfresh Hp1 Hp2
    Hin.
  subst p2. subst p1.
  assert (Hs19 : 0 <= s <= 18).
  { destruct Hin as [Hin|Hin].
    - exact (items_syms_range _ nil s
               (scan_output_wf tL maxcL bl HmcL H15L) Hin).
    - exact (items_syms_range _ nil s
               (scan_output_wf tD maxcD (snd (scan_tree tL maxcL bl))
                  HmcD H15D) Hin). }
  assert (Hb0 : RBudget bl 0)
    by (intros s' Hs'; rewrite (Hfresh s' Hs'); lia).
  assert (Hb1 : RBudget (snd (scan_tree tL maxcL bl)) 286).
  { apply (scan_tree_budget_r tL maxcL bl 0 286); try assumption; lia. }
  assert (Heq : t_freq (snd (scan_tree tD maxcD (snd (scan_tree tL maxcL bl)))) s
                = t_freq (snd (scan_tree tL maxcL bl)) s
                  + hid_zcount s (items_syms (send_tree_items
                      (fst (scan_tree tD maxcD (snd (scan_tree tL maxcL bl))))
                      maxcD))).
  { apply (scan_tree_counts_r tD maxcD (snd (scan_tree tL maxcL bl)) s 286
             572); try assumption; lia. }
  assert (Hnn1 : 0 <= t_freq (snd (scan_tree tL maxcL bl)) s)
    by (destruct (Hb1 s ltac:(lia)); lia).
  destruct Hin as [Hin|Hin].
  - assert (Hpos1 : 0 < t_freq (snd (scan_tree tL maxcL bl)) s).
    { apply (scan_tree_positive_r tL maxcL bl s); try assumption. }
    assert (Hz : 0 <= hid_zcount s (items_syms (send_tree_items
                    (fst (scan_tree tD maxcD (snd (scan_tree tL maxcL bl))))
                    maxcD)))
      by (unfold hid_zcount; lia).
    lia.
  - assert (Hc : (0 < count_occ Z.eq_dec
                    (items_syms (send_tree_items
                       (fst (scan_tree tD maxcD (snd (scan_tree tL maxcL bl))))
                       maxcD)) s)%nat)
      by (apply (count_occ_In Z.eq_dec); exact Hin).
    assert (Hpos2 : 0 < hid_zcount s (items_syms (send_tree_items
                       (fst (scan_tree tD maxcD (snd (scan_tree tL maxcL bl))))
                       maxcD)))
      by (unfold hid_zcount; lia).
    lia.
Qed.

(** [cover_both_streams] at the range freshness — the seam hypothesis is
    now DISCHARGED rather than carried. *)
Theorem cover_both_streams_r :
  forall (st st2 : TSt) (cl : list nat) tL maxcL tD maxcD p1 p2
         t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1,
  0 <= maxcL <= 285 -> 0 <= maxcD <= 285 ->
  (forall i, 0 <= i <= maxcL -> 0 <= t_len tL i <= 15) ->
  (forall i, 0 <= i <= maxcD -> 0 <= t_len tD i <= 15) ->
  (forall s', 0 <= s' < 19 -> t_freq (ts_trees st TK_BL) s' = 0) ->
  p1 = scan_tree tL maxcL (ts_trees st TK_BL) ->
  p2 = scan_tree tD maxcD (snd p1) ->
  ts_trees st2 TK_BL = snd p2 ->
  DlNn (snd p2) ->
  bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems TK_BL) (ts_trees st2 TK_BL)
          (ts_heap st2) (ts_depth st2) 0 (-1) = (t0, hp0, dep0, hlen0, maxc0) ->
  bt_force2 3%nat (sd_stree TK_BL) t0 hp0 dep0 hlen0 maxc0
            (ts_optlen st2) (ts_statlen st2)
    = (t1, hp1, dep1, hlen1, maxc1, ol1, sl1) ->
  LensOf (ts_trees (build_tree TK_BL st2) TK_BL) cl ->
  (19 <= length cl)%nat ->
  CLCovers cl (send_tree_items (fst p1) maxcL)
  /\ CLCovers cl (send_tree_items (fst p2) maxcD).
Proof.
  intros st st2 cl tL maxcL tD maxcD p1 p2 t0 hp0 dep0 hlen0 maxc0
         t1 hp1 dep1 hlen1 maxc1 ol1 sl1
         HmcL HmcD H15L H15D Hfresh Hp1 Hp2 Hst2 Hnn Hinit Hforce HL Hlen.
  assert (Hchain : forall s,
            0 <= s <= 18 -> 0 < t_freq (snd p2) s ->
            exists n, nth_error cl (Z.to_nat s) = Some n /\ (1 <= n <= 7)%nat).
  { intros s Hs Hpos. eapply covered_of_freq_pos; try eassumption.
    - rewrite Hst2. exact Hnn.
    - rewrite Hst2. exact Hpos. }
  assert (Hwf1 : CLWf nil (send_tree_items (fst p1) maxcL))
    by (rewrite Hp1; apply scan_output_wf; assumption).
  assert (Hwf2 : CLWf nil (send_tree_items (fst p2) maxcD))
    by (rewrite Hp2; apply scan_output_wf; assumption).
  split; intros s Hin.
  - apply Hchain.
    + exact (items_syms_range _ nil s Hwf1 Hin).
    + apply (scan_keeps_pos_r tL maxcL tD maxcD (ts_trees st TK_BL) p1 p2 s
               HmcL HmcD H15L H15D Hfresh Hp1 Hp2).
      left. exact Hin.
  - apply Hchain.
    + exact (items_syms_range _ nil s Hwf2 Hin).
    + apply (scan_keeps_pos_r tL maxcL tD maxcD (ts_trees st TK_BL) p1 p2 s
               HmcL HmcD H15L H15D Hfresh Hp1 Hp2).
      right. exact Hin.
Qed.

(** The two consumer-facing finals, at the range freshness. *)
Corollary cover_both_streams_final_r :
  forall (st st2 : TSt) (cl : list nat) tL maxcL tD maxcD p1 p2
         t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1,
  0 <= maxcL <= 285 -> 0 <= maxcD <= 285 ->
  (forall i, 0 <= i <= maxcL -> 0 <= t_len tL i <= 15) ->
  (forall i, 0 <= i <= maxcD -> 0 <= t_len tD i <= 15) ->
  (forall s', 0 <= s' < 19 -> t_freq (ts_trees st TK_BL) s' = 0) ->
  p1 = scan_tree tL maxcL (ts_trees st TK_BL) ->
  p2 = scan_tree tD maxcD (snd p1) ->
  ts_trees st2 TK_BL = snd p2 ->
  DlNn (snd p2) ->
  bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems TK_BL) (ts_trees st2 TK_BL)
          (ts_heap st2) (ts_depth st2) 0 (-1) = (t0, hp0, dep0, hlen0, maxc0) ->
  bt_force2 3%nat (sd_stree TK_BL) t0 hp0 dep0 hlen0 maxc0
            (ts_optlen st2) (ts_statlen st2)
    = (t1, hp1, dep1, hlen1, maxc1, ol1, sl1) ->
  LensOf (ts_trees (build_tree TK_BL st2) TK_BL) cl ->
  (19 <= length cl)%nat ->
  (exists bits, cl_bits cl (send_tree_items (fst p1) maxcL) = Some bits)
  /\ (exists bits, cl_bits cl (send_tree_items (fst p2) maxcD) = Some bits).
Proof.
  intros.
  edestruct (cover_both_streams_r st st2 cl tL maxcL tD maxcD p1 p2)
    as [Hc1 Hc2]; try eassumption.
  split; apply cl_bits_total; assumption.
Qed.

Theorem send_tree_roundtrip_from_scan_r :
  forall (st st2 : TSt) (cl : list nat) tL maxcL tD maxcD p1 p2
         maxcbl blc rest
         t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1,
  0 <= maxcL <= 285 -> 0 <= maxcD <= 285 ->
  DlNn tL ->
  (forall i, 0 <= i <= maxcL -> 0 <= t_len tL i <= 15) ->
  (forall i, 0 <= i <= maxcD -> 0 <= t_len tD i <= 15) ->
  (forall s', 0 <= s' < 19 -> t_freq (ts_trees st TK_BL) s' = 0) ->
  p1 = scan_tree tL maxcL (ts_trees st TK_BL) ->
  p2 = scan_tree tD maxcD (snd p1) ->
  ts_trees st2 TK_BL = snd p2 ->
  DlNn (snd p2) ->
  bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems TK_BL) (ts_trees st2 TK_BL)
          (ts_heap st2) (ts_depth st2) 0 (-1) = (t0, hp0, dep0, hlen0, maxc0) ->
  bt_force2 3%nat (sd_stree TK_BL) t0 hp0 dep0 hlen0 maxc0
            (ts_optlen st2) (ts_statlen st2)
    = (t1, hp1, dep1, hlen1, maxc1, ol1, sl1) ->
  LensOf (ts_trees (build_tree TK_BL st2) TK_BL) cl ->
  (19 <= length cl)%nat ->
  BlcOf blc cl -> ValidLengths cl 7%nat ->
  AbsentBeyond cl maxcbl -> -1 <= maxcbl <= 288 ->
  read_lengths cl (length (tree_lens (fst p1) maxcL))
    (bw_stream (send_tree (fst p1) maxcL
        (gen_codes (ts_trees (build_tree TK_BL st2) TK_BL) maxcbl blc) bw_init)
     ++ rest)
  = Some (tree_lens (fst p1) maxcL, rest).
Proof.
  intros st st2 cl tL maxcL tD maxcD p1 p2 maxcbl blc rest
         t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1
         HmcL HmcD HnnL H15L H15D Hfresh Hp1 Hp2 Hst2 Hnn2 Hinit Hforce
         HL Hlen Hblc HV Hab Hmcbl.
  destruct (cover_both_streams_final_r st st2 cl tL maxcL tD maxcD p1 p2
              t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1
              HmcL HmcD H15L H15D Hfresh Hp1 Hp2 Hst2 Hnn2 Hinit Hforce HL
              Hlen)
    as [[bits Hbits] _].
  subst p2. subst p1.
  apply (send_tree_roundtrip (fst (scan_tree tL maxcL (ts_trees st TK_BL)))
           maxcL cl (ts_trees (build_tree TK_BL st2) TK_BL) maxcbl blc bits
           rest).
  - exact HmcL.
  - apply scanned_tree_dlnn. exact HnnL.
  - apply scanned_tree_guard.
  - apply scanned_tree_lens15; [lia | exact H15L].
  - exact HL.
  - exact Hblc.
  - exact HV.
  - exact Hab.
  - exact Hmcbl.
  - exact Hbits.
Qed.

Print Assumptions scan_keeps_pos_r.
Print Assumptions cover_both_streams_r.
Print Assumptions cover_both_streams_final_r.
Print Assumptions send_tree_roundtrip_from_scan_r.
