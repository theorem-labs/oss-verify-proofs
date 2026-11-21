(** * A1core — DYN ROUND Leg A1/A2 core: the two-level chase
    (q7-decode, dyn round, 2026-08-20; working text v3, freeze v4
    75426016; statements = A1StmtsV3).

    Contents: the hdecode negative-half lemma; the two-level producing
    FETCH chase (leaf / pointer / marker classification at zr_two_own_v3
    tables); the windowed child fetch (Q6T's zr_fetch2_stream re-proved
    with WINDOW-quantified premises — the banked global-bounds form is
    not derivable from two-own; Q6T itself lifts untouched); and the
    composite inf_decode chase [zr_decode_hdecode_two].

    Vocabulary: ambient [br_stream] = ZReproQ6A's (the Q6P/Q6Q
    convention); ZBitsBridge-spelled library facts cross via
    [zr_stream_eq] (reflexivity-equal constants), the Q6P idiom. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From Stdlib Require Znumtheory.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Huff DeflateSpec Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZReproQ6A ZReproQ6I ZReproQ6N ZReproQ6P.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require DecodeBridge.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require InflateThy.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require ZBitsBridge.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require ZReproQ6M.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require ZReproQ6T.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtBrAlign.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import A1StmtsV3.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require GtDecHsel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require W2Stream.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   0.  Small-integer band facts (the 15/16-case pattern g1 used).
   ========================================================================== *)

Lemma zrA_land240_small : forall a, 0 <= a < 16 -> Z.land a 240 = 0.
Proof.
  intros a Ha.
  assert (E : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6
              \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12
              \/ a = 13 \/ a = 14 \/ a = 15) by lia.
  decompose [or] E; subst; reflexivity.
Qed.

Lemma zrA_land240_16 : forall a, 16 <= a < 32 -> Z.land a 240 = 16.
Proof.
  intros a Ha.
  assert (E : a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21
              \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27
              \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31) by lia.
  decompose [or] E; subst; reflexivity.
Qed.

Lemma zrA_land64_240 : forall a, Z.land a 64 <> 0 -> Z.land a 240 <> 0.
Proof.
  intros a H C. apply H. exact (proj2 (GtDecHsel.land240_sub a C)).
Qed.

(* ==========================================================================
   1.  Dispatch-alignment facts at the concrete subs ([ADJ-3]'s three
       premises, discharged for sub_len and sub_dist).
   ========================================================================== *)

Lemma zrA_sub_len_240 : forall e, Z.land (c_op e) 240 <> 0 ->
  sub_len e = false.
Proof.
  intros e H. unfold sub_len.
  destruct (Z.eqb_spec (Z.land (c_op e) 240) 0); [contradiction|].
  apply andb_false_r.
Qed.

Lemma zrA_sub_dist_240 : forall e, Z.land (c_op e) 240 <> 0 ->
  sub_dist e = false.
Proof.
  intros e H. unfold sub_dist.
  destruct (Z.eqb_spec (Z.land (c_op e) 240) 0); [contradiction|].
  reflexivity.
Qed.

Lemma zrA_sub_len_ptr : forall e,
  c_op e <> 0 -> Z.land (c_op e) 240 = 0 -> sub_len e = true.
Proof.
  intros e Hnz H240. unfold sub_len.
  destruct (Z.eqb_spec (c_op e) 0); [contradiction|].
  destruct (Z.eqb_spec (Z.land (c_op e) 240) 0); [reflexivity|contradiction].
Qed.

Lemma zrA_sub_dist_ptr : forall e,
  c_op e <> 0 -> Z.land (c_op e) 240 = 0 -> sub_dist e = true.
Proof.
  intros e _ H240. unfold sub_dist.
  destruct (Z.eqb_spec (Z.land (c_op e) 240) 0); [reflexivity|contradiction].
Qed.

Lemma zrA_sub_len_marker : sub_len (mkCodeT 64 1 0) = false.
Proof. reflexivity. Qed.

Lemma zrA_sub_dist_marker : sub_dist (mkCodeT 64 1 0) = false.
Proof. reflexivity. Qed.

Lemma zrA_lents_sub_len : forall ll entl,
  zr_len_ents ll entl ->
  forall sym cw, code_for ll 15%nat sym = Some cw ->
  sub_len (entl sym) = false.
Proof.
  intros ll entl HE sym cw Hcf.
  destruct (HE sym cw Hcf)
    as [ (_ & Hop & _)
       | [ (_ & _ & _ & _ & H64)
         | [ (_ & (b0 & e0 & _ & _ & Hop & _ & _ & _ & _ & _ & _ & He5 & _))
           | (_ & _ & _ & H64) ] ] ].
  - unfold sub_len. rewrite Hop. reflexivity.
  - apply zrA_sub_len_240, zrA_land64_240. exact H64.
  - apply zrA_sub_len_240.
    rewrite (zrA_land240_16 (c_op (entl sym)) ltac:(rewrite Hop; lia)).
    lia.
  - apply zrA_sub_len_240, zrA_land64_240. exact H64.
Qed.

Lemma zrA_dents_sub_dist : forall dl entd,
  zr_dist_ents dl entd ->
  forall sym cw, code_for dl 15%nat sym = Some cw ->
  sub_dist (entd sym) = false.
Proof.
  intros dl entd HE sym cw Hcf.
  destruct (HE sym cw Hcf)
    as [ (b0 & e0 & _ & _ & Hop & _ & _ & _ & _ & He13)
       | (H64 & _) ].
  - apply zrA_sub_dist_240.
    rewrite (zrA_land240_16 (c_op (entd sym)) ltac:(rewrite Hop; lia)).
    lia.
  - apply zrA_sub_dist_240, zrA_land64_240. exact H64.
Qed.

(* ==========================================================================
   2.  The hdecode negative half (Huff has only None -> no-prefix).
   ========================================================================== *)

Theorem zr_hdecode_none_marker : zr_hdecode_none_marker_STMT.
Proof.
  unfold zr_hdecode_none_marker_STMT.
  intros A table.
  induction table as [|[cw a] rest IH]; intros bits Hnp.
  - reflexivity.
  - cbn [hdecode].
    rewrite (Hnp cw a (or_introl eq_refl)).
    apply IH. intros cw' a' Hin. exact (Hnp cw' a' (or_intror Hin)).
Qed.

Lemma zrA_firstn_prefix : forall (cw s : list bool),
  is_prefix cw s = true -> firstn (length cw) s = cw.
Proof.
  intros cw s Hp. apply is_prefix_true_iff in Hp as [r ->].
  rewrite firstn_app, firstn_all, Nat.sub_diag.
  cbn [firstn]. apply app_nil_r.
Qed.

(** The marker window has NO parse: no codeword (of any length)
    prefixes a stream whose root window spells a negatively-owned
    index. *)
Lemma zrA_marker_none : forall (lens : list nat) (root i : Z)
                               (s : list bool),
  0 < root ->
  firstn (Z.to_nat root) s = write_bits (Z.to_nat root) i ->
  zr_no_short_code lens root i ->
  zr_no_long_code_at lens root i ->
  hdecode (code_table lens 15%nat) s = None.
Proof.
  intros lens root i s Hr Hs Hns Hnl.
  apply zr_hdecode_none_marker.
  intros cw sym Hin.
  apply code_table_In_iff in Hin.
  destruct (is_prefix cw s) eqn:Hp; [exfalso|reflexivity].
  pose proof (zrA_firstn_prefix cw s Hp) as Hf.
  destruct (Z.le_gt_cases (Z.of_nat (length cw)) root) as [Hle|Hgt].
  - (* short: the window spelling owns the prefix *)
    apply (Hns sym cw Hin Hle).
    assert (Hcwn : (length cw <= Z.to_nat root)%nat).
    { apply Nat2Z.inj_le. rewrite Z2Nat.id by lia. lia. }
    rewrite <- Hs, firstn_firstn, Nat.min_l by exact Hcwn.
    exact Hf.
  - (* long: the codeword's root prefix would spell the window *)
    apply (Hnl sym cw Hin Hgt).
    apply is_prefix_true_iff in Hp as [r Hsr].
    assert (Hcwn : (Z.to_nat root <= length cw)%nat).
    { apply Nat2Z.inj_le. rewrite Z2Nat.id by lia. lia. }
    rewrite <- Hs, Hsr, firstn_app.
    replace (Z.to_nat root - length cw)%nat with 0%nat by lia.
    cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.

(* ==========================================================================
   3.  Window arithmetic for the child fetch.
   ========================================================================== *)

(* q6 landing-prep note (freeze v7): callers bound i < 2^root,
   op <= 15 - root; write_bits truncates out-of-range indices silently. *)
Lemma zrA_bits_window : forall n rb b,
  0 <= rb <= n -> 0 <= br_hold b ->
  0 <= Z.shiftr (br_bits_of n b) rb < 2 ^ (n - rb).
Proof.
  intros n rb b Hrn Hh.
  pose proof (InflateThy.land_ones_range (br_hold b) n ltac:(lia)) as Hm.
  unfold br_bits_of.
  rewrite Z.shiftr_div_pow2 by lia.
  split.
  - apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia].
  - apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
    rewrite <- Z.pow_add_r by lia.
    replace (rb + (n - rb)) with n by lia.
    lia.
Qed.

(** Bits rb..rb+m of Y, two spellings (pure bit-level). *)
Lemma zrA_div_mod_window : forall Y rb m,
  0 <= rb -> 0 <= m ->
  (Y / 2 ^ rb) mod 2 ^ m = (Y mod 2 ^ (rb + m)) / 2 ^ rb.
Proof.
  intros Y rb m Hrb Hm.
  apply Z.bits_inj'. intros k Hk.
  destruct (Z.lt_ge_cases k m) as [Hkm|Hkm].
  - rewrite Z.mod_pow2_bits_low by lia.
    rewrite Z.div_pow2_bits by lia.
    rewrite Z.div_pow2_bits by lia.
    rewrite Z.mod_pow2_bits_low by lia.
    reflexivity.
  - rewrite Z.mod_pow2_bits_high by lia.
    rewrite Z.div_pow2_bits by lia.
    rewrite Z.mod_pow2_bits_high by lia.
    reflexivity.
Qed.

(** The machine's child index, reduced to the [m]-window: the low [m]
    bits of the [op]-window index are the [m]-window index. *)
Lemma zrA_shiftr_bits_mod : forall b rb m op,
  0 <= rb -> 0 < m <= op -> 0 <= br_hold b ->
  (Z.shiftr (br_bits_of (rb + op) b) rb) mod 2 ^ m
  = Z.shiftr (br_bits_of (rb + m) b) rb.
Proof.
  intros b rb m op Hrb Hm Hh.
  assert (Hp : forall k, 0 <= k -> 0 < 2 ^ k)
    by (intros; apply Z.pow_pos_nonneg; lia).
  unfold br_bits_of. rewrite !Z.shiftl_1_l.
  replace (Z.land (br_hold b) (2 ^ (rb + op) - 1))
    with (br_hold b mod 2 ^ (rb + op))
    by (rewrite <- Z.land_ones by lia; f_equal; rewrite Z.ones_equiv; lia).
  replace (Z.land (br_hold b) (2 ^ (rb + m) - 1))
    with (br_hold b mod 2 ^ (rb + m))
    by (rewrite <- Z.land_ones by lia; f_equal; rewrite Z.ones_equiv; lia).
  rewrite !Z.shiftr_div_pow2 by lia.
  rewrite (zrA_div_mod_window (br_hold b mod 2 ^ (rb + op)) rb m)
    by lia.
  f_equal.
  symmetry.
  apply Znumtheory.Zmod_div_mod;
    [apply Hp; lia | apply Hp; lia |].
  exists (2 ^ (op - m)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma zrA_skipn_skipn : forall (A : Type) (a b : nat) (l : list A),
  skipn a (skipn b l) = skipn (b + a) l.
Proof.
  intros A a b. revert b.
  induction b as [|b IH]; intros l; [reflexivity|].
  destruct l as [|x l]; cbn [skipn].
  - destruct a; reflexivity.
  - apply IH.
Qed.

(* ==========================================================================
   4.  Ownership-derived width bound (feeds the fetch pull-safety and
       the align machinery — leaf <= root, pointer = root, marker = 1).
   ========================================================================== *)

Lemma zrA_two_own_cbits : forall T root lens ent,
  0 < root ->
  zr_two_own_v3 T root lens ent ->
  forall i, 0 <= i < 2 ^ root -> 0 <= c_bits (T i) <= root.
Proof.
  intros T root lens ent Hr Hown i Hi.
  destruct (Hown i Hi)
    as [ (sym & cw & _ & Hcwr & HTi & Hcb & _)
       | [ (Hcb & _) | (Hrec & Hro & _) ] ].
  - rewrite HTi, Hcb. lia.
  - lia.
  - assert (Hc : c_bits (mkCodeT 64 1 0) = 1) by reflexivity.
    rewrite Hrec, Hc. lia.
Qed.

(* ==========================================================================
   5.  The two-level producing FETCH chase.
   ========================================================================== *)

Lemma zrA_fetch_go_two :
  forall (T : ztbl) (root : Z) (lens : list nat) (ent : nat -> Code),
    0 < root <= 15 ->
    ValidLengths lens 15%nat ->
    zr_two_own_v3 T root lens ent ->
    forall f b, br_wf b ->
      match inf_fetch_go f T root b with
      | FetchOk h b' =>
          br_stream b' = br_stream b
          /\ br_wf b'
          /\ (W2Stream.br_haligned b -> W2Stream.br_haligned b')
          /\ c_bits h <= br_bits b'
          /\ ( (exists sym cw,
                  code_for lens 15%nat sym = Some cw
                  /\ h = ent sym
                  /\ c_bits h = Z.of_nat (length cw)
                  /\ hdecode (code_table lens 15%nat) (br_stream b')
                     = Some (sym, br_stream (br_dropbits (c_bits h) b')))
             \/ (exists i, 0 <= i < 2 ^ root
                  /\ h = T i
                  /\ c_bits h = root
                  /\ 1 <= c_op h <= 15 - root
                  /\ 2 ^ root <= c_val h
                  /\ root <= br_bits b'
                  /\ firstn (Z.to_nat root) (br_stream b')
                     = write_bits (Z.to_nat root) i
                  /\ zr_width_covers lens root i (c_op h)
                  /\ zr_ptr_children T root lens ent i (c_op h) (c_val h))
             \/ (h = mkCodeT 64 1 0
                  /\ hdecode (code_table lens 15%nat) (br_stream b') = None))
      | FetchLeave b' => br_stream b' = br_stream b /\ br_wf b'
      | FetchFuel => True
      end.
Proof.
  intros T root lens ent Hroot HV Hown.
  induction f as [|f IH]; intros b Hwf; cbn [inf_fetch_go]; [exact I|].
  pose proof (DecodeBridge.br_bits_of_in_range root b ltac:(lia)) as Hir.
  destruct (Z.leb_spec (c_bits (T (br_bits_of root b))) (br_bits b))
    as [Hle|Hgt].
  - (* stop *)
    destruct (Hown (br_bits_of root b) Hir)
      as [ (sym & cw & Hcf & Hcwr & HTi & Hcb & Hpref)
         | [ (Hcb & Hop & Hval & Hwc & Hch)
           | (Hrec & Hro1 & Hns & Hnl) ] ].
    + (* coded short leaf: Q6M's stop argument *)
      rewrite HTi in Hle. rewrite Hcb in Hle.
      assert (Hcwn : (length cw <= Z.to_nat root)%nat).
      { apply Nat2Z.inj_le. rewrite Z2Nat.id by lia. lia. }
      assert (Hfp : cw = firstn (length cw) (br_stream b)).
      { pose proof (DecodeBridge.br_index_spells_stream
                      (Z.of_nat (length cw)) root b
                      ltac:(lia) ltac:(lia)) as HS.
        change ZBitsBridge.br_stream with br_stream in HS.
        rewrite <- (Nat2Z.id (length cw)).
        rewrite <- HS.
        rewrite Nat2Z.id.
        rewrite <- (DecodeBridge.firstn_write_bits (Z.to_nat root)
                      (length cw) (br_bits_of root b)) by exact Hcwn.
        symmetry. exact Hpref. }
      set (rest := skipn (length cw) (br_stream b)).
      assert (Hsplit : br_stream b = cw ++ rest).
      { unfold rest. rewrite Hfp at 1. rewrite <- Hfp. rewrite Hfp at 1.
        apply eq_sym, firstn_skipn. }
      split; [reflexivity|].
      split; [exact Hwf|].
      split; [intro Hal; exact Hal|].
      split; [rewrite HTi, Hcb; exact Hle|].
      left. exists sym, cw.
      split; [exact Hcf|].
      split; [exact HTi|].
      split; [rewrite HTi; exact Hcb|].
      rewrite HTi, Hcb.
      assert (Hdrop : br_stream (br_dropbits (Z.of_nat (length cw)) b)
                      = rest).
      { pose proof (ZBitsBridge.br_stream_dropbits
                      (Z.of_nat (length cw)) b
                      ltac:(lia)
                      ltac:(destruct Hwf as (_ & Hh & _); lia)) as HD.
        change ZBitsBridge.br_stream with br_stream in HD.
        rewrite HD, Nat2Z.id. reflexivity. }
      rewrite Hdrop, Hsplit.
      exact (hdecode_complete nat Nat.eq_dec (code_table lens 15%nat)
               cw sym rest (code_table_prefix_free lens 15%nat HV)
               (proj2 (code_table_In_iff lens 15%nat sym cw) Hcf)).
    + (* pointer *)
      rewrite Hcb in Hle.
      pose proof (DecodeBridge.br_index_spells_stream root root b
                    ltac:(lia) ltac:(lia)) as HS.
      change ZBitsBridge.br_stream with br_stream in HS.
      split; [reflexivity|].
      split; [exact Hwf|].
      split; [intro Hal; exact Hal|].
      split; [rewrite Hcb; exact Hle|].
      right; left. exists (br_bits_of root b).
      split; [exact Hir|].
      split; [reflexivity|].
      split; [exact Hcb|].
      split; [exact Hop|].
      split; [exact Hval|].
      split; [exact Hle|].
      split; [symmetry; exact HS|].
      split; [exact Hwc|].
      exact Hch.
    + (* marker: bits = 1, root = 1, no parse *)
      assert (Hc1 : c_bits (mkCodeT 64 1 0) = 1) by reflexivity.
      rewrite Hrec, Hc1 in Hle.
      pose proof (DecodeBridge.br_index_spells_stream root root b
                    ltac:(lia) ltac:(lia)) as HS.
      change ZBitsBridge.br_stream with br_stream in HS.
      split; [reflexivity|].
      split; [exact Hwf|].
      split; [intro Hal; exact Hal|].
      split; [rewrite Hrec, Hc1; lia|].
      right; right.
      split; [exact Hrec|].
      apply (zrA_marker_none lens root (br_bits_of root b) (br_stream b)
               ltac:(lia)).
      * symmetry; exact HS.
      * exact Hns.
      * exact Hnl.
  - (* pull *)
    assert (H31 : br_bits b <= 31).
    { pose proof (zrA_two_own_cbits T root lens ent ltac:(lia) Hown
                    (br_bits_of root b) Hir). lia. }
    destruct (br_pullbyte b) as [b2|] eqn:HP.
    + assert (Hwf2 : br_wf b2) by (apply (br_wf_pullbyte b b2 Hwf H31 HP)).
      pose proof (ZBitsBridge.br_stream_pullbyte b b2 Hwf HP) as Hs2.
      change ZBitsBridge.br_stream with br_stream in Hs2.
      pose proof (IH b2 Hwf2) as HI.
      destruct (inf_fetch_go f T root b2) as [h' b'|b'|]; [| |exact I].
      * destruct HI as (S1 & S2 & S3 & S4 & S5).
        split; [rewrite S1; exact Hs2|].
        split; [exact S2|].
        split; [intro Hal;
                exact (S3 (br_haligned_pullbyte b b2 Hwf HP Hal))|].
        split; [exact S4 | exact S5].
      * destruct HI as (S1 & S2).
        split; [rewrite S1; exact Hs2 | exact S2].
    + split; [reflexivity | exact Hwf].
Qed.

Theorem zr_fetch_hdecode_two : zr_fetch_hdecode_two_STMT.
Proof.
  unfold zr_fetch_hdecode_two_STMT.
  intros T root lens ent b Hroot HV Hown Hwf.
  exact (zrA_fetch_go_two T root lens ent Hroot HV Hown
           (S (Z.to_nat (br_have b))) b Hwf).
Qed.

(* ==========================================================================
   6.  The WINDOWED child fetch (the Q6T induction with window-quantified
       premises: two-own constrains nothing outside the child window, so
       the banked global bounds are not derivable — the reads stay inside
       the window by the index formula, which is what this proof threads).
   ========================================================================== *)

Lemma zrA_fetch2_go_two :
  forall (T : ztbl) (root : Z) (lens : list nat) (ent : nat -> Code)
         (i0 : Z) (h0 : Code),
    0 < root <= 15 ->
    c_bits h0 = root ->
    1 <= c_op h0 <= 15 - root ->
    zr_ptr_children T root lens ent i0 (c_op h0) (c_val h0) ->
    forall f b, br_wf b ->
      match inf_fetch2_go f T h0 b with
      | FetchOk h b' =>
          br_stream b' = br_stream b
          /\ br_wf b'
          /\ (W2Stream.br_haligned b -> W2Stream.br_haligned b')
          /\ root + c_bits h <= br_bits b'
          /\ h = T (c_val h0
                    + Z.shiftr (br_bits_of (root + c_op h0) b') root)
      | FetchLeave b' => br_stream b' = br_stream b /\ br_wf b'
      | FetchFuel => True
      end.
Proof.
  intros T root lens ent i0 h0 Hroot Hcb0 Hop0 Hch.
  induction f as [|f IH]; intros b Hwf; cbn [inf_fetch2_go]; [exact I|].
  destruct (Z.leb_spec
              (c_bits h0
               + c_bits (T (c_val h0
                            + Z.shiftr (br_bits_of (c_bits h0 + c_op h0) b)
                                       (c_bits h0))))
              (br_bits b)) as [Hle|Hgt].
  - (* stop *)
    rewrite Hcb0 in Hle |- *.
    split; [reflexivity|].
    split; [exact Hwf|].
    split; [intro Hal; exact Hal|].
    split; [exact Hle | reflexivity].
  - (* pull: the current read is inside the child window *)
    assert (Hj : 0 <= Z.shiftr (br_bits_of (c_bits h0 + c_op h0) b)
                               (c_bits h0)
                 < 2 ^ c_op h0).
    { rewrite Hcb0.
      pose proof (zrA_bits_window (root + c_op h0) root b
                    ltac:(lia)
                    ltac:(destruct Hwf as (_ & Hh & _); lia)) as HW.
      replace (root + c_op h0 - root) with (c_op h0) in HW by lia.
      exact HW. }
    destruct (Hch _ Hj)
      as (sym & cw & _ & Hrng & HTj & Hcbj & _).
    assert (H31 : br_bits b <= 31).
    { rewrite Hcb0 in Hgt.
      rewrite Hcb0 in HTj.
      rewrite HTj, Hcbj in Hgt. lia. }
    destruct (br_pullbyte b) as [b2|] eqn:HP.
    + assert (Hwf2 : br_wf b2) by (apply (br_wf_pullbyte b b2 Hwf H31 HP)).
      pose proof (ZBitsBridge.br_stream_pullbyte b b2 Hwf HP) as Hs2.
      change ZBitsBridge.br_stream with br_stream in Hs2.
      pose proof (IH b2 Hwf2) as HI.
      destruct (inf_fetch2_go f T h0 b2) as [h' b'|b'|]; [| |exact I].
      * destruct HI as (S1 & S2 & S3 & S4 & S5).
        split; [rewrite S1; exact Hs2|].
        split; [exact S2|].
        split; [intro Hal;
                exact (S3 (br_haligned_pullbyte b b2 Hwf HP Hal))|].
        split; [exact S4 | exact S5].
      * destruct HI as (S1 & S2).
        split; [rewrite S1; exact Hs2 | exact S2].
    + split; [reflexivity | exact Hwf].
Qed.

(* ==========================================================================
   7.  The composite decode chase.
   ========================================================================== *)

Theorem zr_decode_hdecode_two : zr_decode_hdecode_two_STMT.
Proof.
  unfold zr_decode_hdecode_two_STMT.
  intros sub T root lens ent b Hroot HV Hown HsubL HsubP HsubM Hwf.
  unfold inf_decode.
  pose proof (zr_fetch_hdecode_two T root lens ent b Hroot HV Hown Hwf)
    as HF.
  unfold zr_fetch_hdecode_two_STMT in HF.
  destruct (inf_fetch T root b) as [h0 b0|b0|] eqn:EF;
    [| exact HF | exact I].
  destruct HF as (Hs0 & Hwf0 & Hal0 & Hbb0 & HC).
  destruct HC as [ (sym & cw & Hcf & Hent & Hcbw & Hhd)
                 | [ (i & Hir & Hh0 & Hcb & Hop & Hval & Hrb0 & Hpre0 & Hwc & Hch)
                   | (Hrec & Hnone) ] ].
  - (* coded short leaf: sub false, single drop *)
    rewrite Hent in Hbb0, Hcbw, Hhd.
    rewrite Hent, (HsubL sym cw Hcf). cbv beta iota.
    assert (Hrange : 0 <= c_bits (ent sym) <= br_bits b0)
      by (rewrite Hcbw in Hbb0 |- *; lia).
    split.
    { apply ZReproQ6A.br_wf_dropbits; [exact Hwf0 | exact Hrange]. }
    split.
    { intro Hal.
      apply br_haligned_dropbits; [exact Hrange | exact (Hal0 Hal)]. }
    left. exists sym, cw.
    split; [exact Hcf|].
    split; [reflexivity|].
    rewrite <- Hs0. exact Hhd.
  - (* pointer: sub true, chase the child *)
    assert (Hsub0 : sub h0 = true).
    { apply HsubP.
      - lia.
      - apply zrA_land240_small. lia. }
    rewrite Hsub0. cbv beta iota.
    pose proof (zrA_fetch2_go_two T root lens ent i h0 Hroot Hcb Hop Hch
                  (S (Z.to_nat (br_have b0))) b0 Hwf0) as HG.
    unfold inf_fetch2 in *.
    destruct (inf_fetch2_go (S (Z.to_nat (br_have b0))) T h0 b0)
      as [h1 b1|b1|] eqn:EF2;
      [| destruct HG as (G1 & G2);
         split; [rewrite G1; exact Hs0 | exact G2]
       | exact I].
    destruct HG as (Hs1 & Hwf1 & Hal1 & Hbb1 & Hpos1).
    cbv beta iota.
    set (jw := Z.shiftr (br_bits_of (root + c_op h0) b1) root) in *.
    assert (Hjw : 0 <= jw < 2 ^ c_op h0).
    { unfold jw.
      pose proof (zrA_bits_window (root + c_op h0) root b1
                    ltac:(lia)
                    ltac:(destruct Hwf1 as (_ & Hh & _); lia)) as HW.
      replace (root + c_op h0 - root) with (c_op h0) in HW by lia.
      exact HW. }
    destruct (Hch jw Hjw)
      as (sym & cw & Hcf & Hrng & HTj & Hcbj & Hsp).
    rewrite <- Hpos1 in HTj.
    set (m := Z.of_nat (length cw) - root) in *.
    assert (Hm : 0 < m <= c_op h0) by (unfold m; lia).
    assert (Hcbm : c_bits h1 = m) by (rewrite HTj; exact Hcbj).
    assert (Hlen : Z.of_nat (length cw) = root + m) by (unfold m; lia).
    assert (Hlcw : length cw = Z.to_nat (root + m)).
    { rewrite <- Hlen, Nat2Z.id. reflexivity. }
    (* the full-codeword prefix of the (preserved) stream *)
    assert (Hcwfull : firstn (length cw) (br_stream b1) = cw).
    { pose proof (ZReproQ6T.zr_spell_two root m b1
                    ltac:(lia) ltac:(lia)
                    ltac:(rewrite <- Hcbm; exact Hbb1) Hwf1) as HSP.
      change ZBitsBridge.br_stream with br_stream in HSP.
      (* first slab = the root index spelling *)
      pose proof (DecodeBridge.br_index_spells_stream root root b1
                    ltac:(lia) ltac:(lia)) as HS1.
      change ZBitsBridge.br_stream with br_stream in HS1.
      assert (Hpre1 : firstn (Z.to_nat root) (br_stream b1)
                      = write_bits (Z.to_nat root) i)
        by (rewrite Hs1; exact Hpre0).
      rewrite HS1, Hpre1 in HSP.
      (* second slab = the m-window child spelling *)
      pose proof (zrA_shiftr_bits_mod b1 root m (c_op h0)
                    ltac:(lia) ltac:(lia)
                    ltac:(destruct Hwf1 as (_ & Hh & _); lia)) as HM.
      change (Z.shiftr (br_bits_of (root + c_op h0) b1) root) with jw in HM.
      rewrite <- HM in HSP.
      rewrite (DecodeBridge.write_bits_mod_pow2 (Z.to_nat m) m jw
                 ltac:(rewrite Z2Nat.id by lia; lia)) in HSP.
      (* the ownership spelling, truncated to the real codeword *)
      assert (Hsp' : write_bits (Z.to_nat root) i
                     ++ write_bits (Z.to_nat m) jw = cw).
      { rewrite <- Hsp, Hlcw.
        rewrite Z2Nat.inj_add by lia.
        rewrite firstn_app.
        rewrite write_bits_length.
        rewrite firstn_all2
          by (rewrite write_bits_length; lia).
        replace (Z.to_nat root + Z.to_nat m - Z.to_nat root)%nat
          with (Z.to_nat m) by lia.
        rewrite (DecodeBridge.firstn_write_bits (Z.to_nat (c_op h0))
                   (Z.to_nat m) jw)
          by (apply Nat2Z.inj_le; rewrite !Z2Nat.id by lia; lia).
        reflexivity. }
      rewrite Hsp' in HSP.
      rewrite <- Hlcw in HSP.
      exact HSP. }
    set (rest := skipn (length cw) (br_stream b1)).
    assert (Hsplit : br_stream b1 = cw ++ rest).
    { unfold rest. rewrite <- Hcwfull at 1. apply eq_sym, firstn_skipn. }
    (* the two machine drops *)
    assert (Hrbb1 : root <= br_bits b1) by (rewrite Hcbm in Hbb1; lia).
    assert (Hwfd1 : br_wf (br_dropbits root b1))
      by (apply ZReproQ6A.br_wf_dropbits; [exact Hwf1 | lia]).
    assert (Hbits_d1 : br_bits (br_dropbits root b1) = br_bits b1 - root)
      by reflexivity.
    assert (Hwfd2 : br_wf (br_dropbits (c_bits h1) (br_dropbits root b1))).
    { apply ZReproQ6A.br_wf_dropbits; [exact Hwfd1|].
      rewrite Hbits_d1, Hcbm. rewrite Hcbm in Hbb1. lia. }
    rewrite Hcb.
    split; [exact Hwfd2|].
    split.
    { intro Hal.
      apply br_haligned_dropbits.
      - rewrite Hbits_d1, Hcbm. rewrite Hcbm in Hbb1. split; [lia|lia].
      - apply br_haligned_dropbits; [lia|].
        exact (Hal1 (Hal0 Hal)). }
    left. exists sym, cw.
    split; [exact Hcf|].
    split; [exact HTj|].
    (* stream bookkeeping: two drops = skipn |cw| *)
    assert (HD1 : br_stream (br_dropbits root b1)
                  = skipn (Z.to_nat root) (br_stream b1)).
    { pose proof (ZBitsBridge.br_stream_dropbits root b1
                    ltac:(lia)
                    ltac:(destruct Hwf1 as (_ & Hh & _); lia)) as HD.
      change ZBitsBridge.br_stream with br_stream in HD. exact HD. }
    assert (HD2 : br_stream (br_dropbits (c_bits h1) (br_dropbits root b1))
                  = skipn (Z.to_nat m) (skipn (Z.to_nat root) (br_stream b1))).
    { pose proof (ZBitsBridge.br_stream_dropbits (c_bits h1)
                    (br_dropbits root b1)
                    ltac:(rewrite Hbits_d1, Hcbm; rewrite Hcbm in Hbb1; lia)
                    ltac:(destruct Hwfd1 as (_ & Hh & _); lia)) as HD.
      change ZBitsBridge.br_stream with br_stream in HD.
      rewrite HD, HD1, Hcbm. reflexivity. }
    rewrite HD2, zrA_skipn_skipn.
    replace (Z.to_nat root + Z.to_nat m)%nat with (length cw)
      by (rewrite Hlcw, Z2Nat.inj_add by lia; reflexivity).
    rewrite <- Hs0, <- Hs1.
    rewrite Hsplit at 1.
    fold rest.
    exact (hdecode_complete nat Nat.eq_dec (code_table lens 15%nat)
             cw sym rest (code_table_prefix_free lens 15%nat HV)
             (proj2 (code_table_In_iff lens 15%nat sym cw) Hcf)).
  - (* marker: sub false, selected; no parse *)
    rewrite Hrec in Hbb0.
    rewrite Hrec, HsubM. cbv beta iota.
    assert (Hcb1 : c_bits (mkCodeT 64 1 0) = 1) by reflexivity.
    assert (Hrange : 0 <= c_bits (mkCodeT 64 1 0) <= br_bits b0)
      by (rewrite Hcb1 in Hbb0 |- *; lia).
    split.
    { apply ZReproQ6A.br_wf_dropbits; [exact Hwf0 | exact Hrange]. }
    split.
    { intro Hal.
      apply br_haligned_dropbits; [exact Hrange | exact (Hal0 Hal)]. }
    right.
    split; [reflexivity|].
    rewrite <- Hs0. exact Hnone.
Qed.
