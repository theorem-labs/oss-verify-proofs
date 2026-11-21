(** * ZReproG6D — G6 bound-fit, part D: [send_all_trees]'s exact bit cost.

    OWNER: g6-bound (zlib z-repro campaign, 2026-08-19).

    The dynamic-arm header: 5+5+4 bits, 3 bits per bl_order rank, then the
    two RLE-coded length streams.  [SendGo.send_go_emit] already factors
    each [send_tree] through the item stream [send_tree_items]; this file
    counts those items ([item_cost]) and regroups the count into the
    BL-frequency-weighted sum — the SAME [hid_zcount] vocabulary
    [ScanCount.scan_tree_counts] uses for the frequencies [build_bl_tree]
    feeds into [opt_len].  So emitted tree-header bits tie to the counter
    with no new aliasing argument.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Chunk ZBitsOut BwStream Trees BtWin CbEmit ClStream SendItems
  SendGo SendGoWf ScanCount HuffCover.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproL0 ZReproG6A
  ZReproG6C.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  BL extra-bits table facts (reflection, as in part C).
   ========================================================================== *)

Definition g6_ebl_at (c : Z) : bool :=
  (0 <=? extra_blbits c) && (extra_blbits c <=? 16).

Lemma g6_ebl_all : forallb g6_ebl_at (zseq 19 0) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma extra_blbits_range : forall c, 0 <= c < 19 -> 0 <= extra_blbits c <= 16.
Proof.
  intros c Hc.
  pose proof (forallb_zseq' g6_ebl_at 19 19 c
                ltac:(vm_compute; reflexivity) g6_ebl_all Hc) as H.
  unfold g6_ebl_at in H.
  apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Definition g6_ebl0_at (c : Z) : bool := extra_blbits c =? 0.

Lemma g6_ebl0_all : forallb g6_ebl0_at (zseq 16 0) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma extra_blbits_low : forall c, 0 <= c < 16 -> extra_blbits c = 0.
Proof.
  intros c Hc.
  pose proof (forallb_zseq' g6_ebl0_at 16 16 c
                ltac:(vm_compute; reflexivity) g6_ebl0_all Hc) as H.
  unfold g6_ebl0_at in H. apply Z.eqb_eq in H. exact H.
Qed.

(* ==========================================================================
   2.  Item cost.
   ========================================================================== *)

Definition item_cost (bl : Tree) (it : CLItem) : Z :=
  match it with
  | CLit l   => t_len bl (Z.of_nat l)
  | CRep _ _ => t_len bl 16 + 2
  | CZ3 _    => t_len bl 17 + 3
  | CZ11 _   => t_len bl 18 + 7
  end.

Fixpoint items_cost (bl : Tree) (items : list CLItem) : Z :=
  match items with
  | [] => 0
  | it :: tl => item_cost bl it + items_cost bl tl
  end.

(** All 19 BL code lengths inside the writer window. *)
Definition LenBL (bl : Tree) : Prop :=
  forall s, 0 <= s < 19 -> 0 <= t_len bl s <= 15.

Lemma emit_item_len : forall bl it b,
  bwv b -> LenBL bl ->
  (forall l, it = CLit l -> (l <= 15)%nat) ->
  zbits (emit_item bl it b) = zbits b + item_cost bl it
  /\ bwv (emit_item bl it b).
Proof.
  intros bl it b Hb HBL Hlit.
  destruct it as [l | p k | k | k]; cbn [emit_item item_cost].
  - specialize (Hlit l eq_refl).
    apply zbits_send_code; [exact Hb|].
    unfold Buf_size. pose proof (HBL (Z.of_nat l) ltac:(lia)). lia.
  - destruct (zbits_send_code 16 bl b Hb
                ltac:(unfold Buf_size; pose proof (HBL 16 ltac:(lia)); lia))
      as [Z1 V1].
    destruct (zbits_send_bits (Z.of_nat k - 3) 2 (send_code 16 bl b) V1
                ltac:(unfold Buf_size; lia)) as [Z2 V2].
    split; [rewrite Z2, Z1; ring | exact V2].
  - destruct (zbits_send_code 17 bl b Hb
                ltac:(unfold Buf_size; pose proof (HBL 17 ltac:(lia)); lia))
      as [Z1 V1].
    destruct (zbits_send_bits (Z.of_nat k - 3) 3 (send_code 17 bl b) V1
                ltac:(unfold Buf_size; lia)) as [Z2 V2].
    split; [rewrite Z2, Z1; ring | exact V2].
  - destruct (zbits_send_code 18 bl b Hb
                ltac:(unfold Buf_size; pose proof (HBL 18 ltac:(lia)); lia))
      as [Z1 V1].
    destruct (zbits_send_bits (Z.of_nat k - 11) 7 (send_code 18 bl b) V1
                ltac:(unfold Buf_size; lia)) as [Z2 V2].
    split; [rewrite Z2, Z1; ring | exact V2].
Qed.

Lemma emit_items_len : forall items acc bl b,
  bwv b -> LenBL bl -> CLWf acc items ->
  zbits (emit_items bl items b) = zbits b + items_cost bl items
  /\ bwv (emit_items bl items b).
Proof.
  induction items as [|it tl IH]; intros acc bl b Hb HBL Hwf;
    cbn [emit_items items_cost].
  - split; [ring | exact Hb].
  - assert (Hlit : forall l, it = CLit l -> (l <= 15)%nat).
    { intros l ->. cbn [CLWf] in Hwf. tauto. }
    destruct (emit_item_len bl it b Hb HBL Hlit) as [Z1 V1].
    assert (Hwf' : exists acc', CLWf acc' tl).
    { destruct it as [l | p k | k | k]; cbn [CLWf] in Hwf.
      - exists (acc ++ [l]). tauto.
      - exists (acc ++ repeat p k). tauto.
      - exists (acc ++ repeat 0%nat k). tauto.
      - exists (acc ++ repeat 0%nat k). tauto. }
    destruct Hwf' as [acc' Hwf'].
    destruct (IH acc' bl (emit_item bl it b) V1 HBL Hwf') as [Z2 V2].
    split; [rewrite Z2, Z1; ring | exact V2].
Qed.

(* ==========================================================================
   3.  The regroup into hid_zcount.
   ========================================================================== *)

Lemma hid_one : forall x s, hid_zcount s [x] = if Z.eqb x s then 1 else 0.
Proof.
  intros x s. destruct (Z.eqb_spec x s) as [->|Ne].
  - apply hid_zcount_one_same.
  - apply hid_zcount_one_diff. exact Ne.
Qed.

Theorem items_cost_regroup : forall bl items acc,
  CLWf acc items ->
  items_cost bl items
  = wsum (fun s => hid_zcount s (items_syms items)
                   * (t_len bl s + extra_blbits s)) 0 19.
Proof.
  intros bl items; induction items as [|it tl IH]; intros acc Hwf.
  - cbn [items_cost items_syms flat_map].
    symmetry. apply g6_wsum_zero.
    intros i _. rewrite hid_zcount_nil. ring.
  - cbn [items_cost].
    assert (Hsplit : items_syms (it :: tl) = item_syms it ++ items_syms tl)
      by reflexivity.
    (* the item's single symbol, and its range *)
    assert (Hone : exists x, item_syms it = [x] /\ 0 <= x < 19
                   /\ item_cost bl it = t_len bl x + extra_blbits x).
    { destruct it as [l | p k | k | k]; cbn [item_syms item_cost CLWf] in *.
      - exists (Z.of_nat l).
        assert (Hl : (l <= 15)%nat) by tauto.
        repeat split; try lia.
        all: rewrite (extra_blbits_low (Z.of_nat l) ltac:(lia)); ring.
      - exists REP_3_6. unfold REP_3_6.
        repeat split; try lia.
        all: replace (extra_blbits 16) with 2 by (vm_compute; reflexivity);
             ring.
      - exists REPZ_3_10. unfold REPZ_3_10.
        repeat split; try lia.
        all: replace (extra_blbits 17) with 3 by (vm_compute; reflexivity);
             ring.
      - exists REPZ_11_138. unfold REPZ_11_138.
        repeat split; try lia.
        all: replace (extra_blbits 18) with 7 by (vm_compute; reflexivity);
             ring. }
    destruct Hone as (x & Ex & Hx & Ecost).
    assert (Hwf' : exists acc', CLWf acc' tl).
    { destruct it as [l | p k | k | k]; cbn [CLWf] in Hwf.
      - exists (acc ++ [l]). tauto.
      - exists (acc ++ repeat p k). tauto.
      - exists (acc ++ repeat 0%nat k). tauto.
      - exists (acc ++ repeat 0%nat k). tauto. }
    destruct Hwf' as [acc' Hwf'].
    rewrite (IH acc' Hwf').
    rewrite (wsum_ext
               (fun s => hid_zcount s (items_syms (it :: tl))
                         * (t_len bl s + extra_blbits s))
               (fun s => (if Z.eqb x s then 1 else 0)
                           * (t_len bl s + extra_blbits s)
                         + hid_zcount s (items_syms tl)
                             * (t_len bl s + extra_blbits s))
               0 19%nat).
    2:{ intros p _.
        rewrite Hsplit, hid_zcount_app, Ex, hid_one. ring. }
    rewrite wsum_plus.
    rewrite (wsum_delta (fun s => t_len bl s + extra_blbits s) x 0 19%nat)
      by (cbn [Z.of_nat]; lia).
    rewrite Ecost. ring.
Qed.

(* ==========================================================================
   4.  sat_ranks and send_all_trees.
   ========================================================================== *)

Lemma sat_ranks_len : forall fuel rank blcodes bl b,
  bwv b ->
  0 <= rank <= blcodes ->
  (Z.to_nat (blcodes - rank) < fuel)%nat ->
  zbits (sat_ranks fuel rank blcodes bl b) = zbits b + 3 * (blcodes - rank)
  /\ bwv (sat_ranks fuel rank blcodes bl b).
Proof.
  induction fuel as [|fuel IH]; intros rank blcodes bl b Hb Hr Hf; [lia|].
  cbn [sat_ranks].
  destruct (Z.leb_spec blcodes rank) as [Hle|Hlt].
  - split; [replace (blcodes - rank) with 0 by lia; ring | exact Hb].
  - destruct (zbits_send_bits (t_len bl (bl_order rank)) 3 b Hb
                ltac:(unfold Buf_size; lia)) as [Z1 V1].
    destruct (IH (rank + 1) blcodes bl
                 (bw_send_bits (t_len bl (bl_order rank)) 3 b) V1
                 ltac:(lia) ltac:(lia)) as [Z2 V2].
    split; [rewrite Z2, Z1; ring | exact V2].
Qed.

Theorem send_all_trees_len : forall lcodes dcodes blcodes s,
  bwv (ts_bw s) ->
  0 <= lcodes - 1 <= 285 ->
  0 <= dcodes - 1 <= 285 ->
  0 <= blcodes <= 19 ->
  t_len (ts_trees s TK_L) (lcodes - 1 + 1) = 65535 ->
  t_len (ts_trees s TK_D) (dcodes - 1 + 1) = 65535 ->
  (forall i, 0 <= i <= lcodes - 1 -> 0 <= t_len (ts_trees s TK_L) i <= 15) ->
  (forall i, 0 <= i <= dcodes - 1 -> 0 <= t_len (ts_trees s TK_D) i <= 15) ->
  (forall i, 0 <= t_len (ts_trees s TK_L) i) ->
  (forall i, 0 <= t_len (ts_trees s TK_D) i) ->
  LenBL (ts_trees s TK_BL) ->
  zbits (send_all_trees lcodes dcodes blcodes s)
    = zbits (ts_bw s) + 14 + 3 * blcodes
      + wsum (fun sy => hid_zcount sy
                          (items_syms (send_tree_items (ts_trees s TK_L)
                                         (lcodes - 1)))
                        * (t_len (ts_trees s TK_BL) sy
                           + extra_blbits sy)) 0 19
      + wsum (fun sy => hid_zcount sy
                          (items_syms (send_tree_items (ts_trees s TK_D)
                                         (dcodes - 1)))
                        * (t_len (ts_trees s TK_BL) sy
                           + extra_blbits sy)) 0 19
  /\ bwv (send_all_trees lcodes dcodes blcodes s).
Proof.
  intros lcodes dcodes blcodes s Hb HmcL HmcD Hbl HgL HgD H15L H15D HnnL HnnD
         HBL.
  unfold send_all_trees. cbv zeta.
  destruct (zbits_send_bits (lcodes - 257) 5 (ts_bw s) Hb
              ltac:(unfold Buf_size; lia)) as [Z0 V0].
  set (b0 := bw_send_bits (lcodes - 257) 5 (ts_bw s)) in *.
  destruct (zbits_send_bits (dcodes - 1) 5 b0 V0
              ltac:(unfold Buf_size; lia)) as [Z1 V1].
  set (b1 := bw_send_bits (dcodes - 1) 5 b0) in *.
  destruct (zbits_send_bits (blcodes - 4) 4 b1 V1
              ltac:(unfold Buf_size; lia)) as [Z2 V2].
  set (b2 := bw_send_bits (blcodes - 4) 4 b1) in *.
  destruct (sat_ranks_len (Z.to_nat BL_CODES + 1) 0 blcodes
              (ts_trees s TK_BL) b2 V2 ltac:(lia)
              ltac:(unfold BL_CODES; lia)) as [Z3 V3].
  set (b3 := sat_ranks (Z.to_nat BL_CODES + 1) 0 blcodes
               (ts_trees s TK_BL) b2) in *.
  (* send_tree TK_L: factor through the item stream *)
  assert (EL : send_tree (ts_trees s TK_L) (lcodes - 1) (ts_trees s TK_BL) b3
               = emit_items (ts_trees s TK_BL)
                   (send_tree_items (ts_trees s TK_L) (lcodes - 1)) b3).
  { unfold send_tree, send_tree_items.
    apply send_go_emit; [exact HnnL | lia | apply HnnL |].
    destruct (Z.eqb (t_len (ts_trees s TK_L) 0) 0); lia. }
  assert (HwfL : CLWf [] (send_tree_items (ts_trees s TK_L) (lcodes - 1))).
  { apply send_tree_items_wf; [lia | exact HgL | exact H15L]. }
  destruct (emit_items_len (send_tree_items (ts_trees s TK_L) (lcodes - 1))
              [] (ts_trees s TK_BL) b3 V3 HBL HwfL) as [Z4 V4].
  set (b4 := emit_items (ts_trees s TK_BL)
               (send_tree_items (ts_trees s TK_L) (lcodes - 1)) b3) in *.
  assert (ED : send_tree (ts_trees s TK_D) (dcodes - 1) (ts_trees s TK_BL) b4
               = emit_items (ts_trees s TK_BL)
                   (send_tree_items (ts_trees s TK_D) (dcodes - 1)) b4).
  { unfold send_tree, send_tree_items.
    apply send_go_emit; [exact HnnD | lia | apply HnnD |].
    destruct (Z.eqb (t_len (ts_trees s TK_D) 0) 0); lia. }
  assert (HwfD : CLWf [] (send_tree_items (ts_trees s TK_D) (dcodes - 1))).
  { apply send_tree_items_wf; [lia | exact HgD | exact H15D]. }
  destruct (emit_items_len (send_tree_items (ts_trees s TK_D) (dcodes - 1))
              [] (ts_trees s TK_BL) b4 V4 HBL HwfD) as [Z5 V5].
  rewrite EL. fold b4. rewrite ED.
  split; [|exact V5].
  rewrite Z5, Z4, Z3, Z2, Z1, Z0.
  rewrite (items_cost_regroup (ts_trees s TK_BL)
             (send_tree_items (ts_trees s TK_L) (lcodes - 1)) [] HwfL).
  rewrite (items_cost_regroup (ts_trees s TK_BL)
             (send_tree_items (ts_trees s TK_D) (dcodes - 1)) [] HwfD).
  ring.
Qed.

Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Print Assumptions send_all_trees_len.
Print Assumptions items_cost_regroup.
Print Assumptions emit_items_len.
