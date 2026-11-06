(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzCStream BzCState BzCHuff BzCMtf BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzR5a.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cG.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cW.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cW.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cG.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cG BzR5cE BzR5cF.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5a OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cG.BzR5b OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cW OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cW.BzR5cLB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cG.BzR5cD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cG OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cE OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cF.
Import ListNotations.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cG.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cW. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cG.
Module BzR5cX.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5a OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cG.BzR5b.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cW OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cW.BzR5cLB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cG.BzR5cD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cG OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cE OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cF.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bit01_range : forall x, bit01 x = 0 \/ bit01 x = 1.
Proof. intros x. unfold bit01. destruct (negb (x =? 0)); [right| left]; reflexivity. Qed.

Lemma ws_in16_bits16 : forall n in16 i, ws_in16 n in16 i = ws_bits16 n (fun j => bit01 (zget in16 j)) i.
Proof. induction n as [|n IH]; intros; cbn [ws_in16 ws_bits16]; [reflexivity| rewrite IH; reflexivity]. Qed.
Lemma ws_inuse_row_bits16 : forall n inUse i j, ws_inuse_row n inUse i j = ws_bits16 n (fun j' => bit01 (zget inUse (i * 16 + j'))) j.
Proof. induction n as [|n IH]; intros; cbn [ws_inuse_row ws_bits16]; [reflexivity| rewrite IH; reflexivity]. Qed.
Lemma ws_inuse_rows : forall n in16 inUse i, ws_inuse n in16 inUse i = ws_rows n (fun j => zget in16 j) (fun c => bit01 (zget inUse c)) i.
Proof.
  induction n as [|n IH]; intros; cbn [ws_inuse ws_rows]; [reflexivity|]. rewrite IH, ws_inuse_row_bits16. reflexivity.
Qed.
Lemma ws_sels_unary : forall n selMtf i, ws_sels n selMtf i = ws_unary n (fun k => zget selMtf k) i.
Proof. induction n as [|n IH]; intros; cbn [ws_sels ws_unary]; [reflexivity| rewrite IH; reflexivity]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ws_bits16_legal : forall n f i, (forall j, f j = 0 \/ f j = 1) -> wlegal (ws_bits16 n f i).
Proof.
  induction n as [|n IH]; intros f i Hf; cbn [ws_bits16]; [apply wlegal_nil|].
  apply wlegal_cons. split; [| apply IH; exact Hf]. cbn [fst snd]. destruct (Hf i) as [E|E]; rewrite E; cbn; lia.
Qed.
Lemma ws_rows_legal : forall n g16 bit i, (forall c, bit c = 0 \/ bit c = 1) -> wlegal (ws_rows n g16 bit i).
Proof.
  induction n as [|n IH]; intros g16 bit i Hb; cbn [ws_rows]; [apply wlegal_nil|].
  apply wlegal_app. split; [| apply IH; exact Hb]. destruct (negb (g16 i =? 0)); [apply ws_bits16_legal; intros; apply Hb| apply wlegal_nil].
Qed.
Lemma ws_unary_legal : forall n msel i, wlegal (ws_unary n msel i).
Proof.
  induction n as [|n IH]; intros; cbn [ws_unary]; [apply wlegal_nil|].
  apply wlegal_app. split; [| apply IH]. apply wlegal_app. split; [apply wlegal_repeat; cbn; lia|]. apply wlegal_cons. split; [cbn; lia| apply wlegal_nil].
Qed.
Lemma ws_drow_legal : forall n ln i curr, wlegal (ws_drow n ln i curr).
Proof.
  induction n as [|n IH]; intros; cbn [ws_drow]; [apply wlegal_nil|].
  apply wlegal_app. split; [destruct (curr <? ln i); apply dsteps_legal|]. apply wlegal_cons. split; [cbn; lia| apply IH].
Qed.
(* [comment removed for export] *)
Lemma ws_blk_hdr_legal : forall crc op, 0 <= op < 16777216 -> wlegal (ws_blk_hdr crc op).
Proof.
  intros crc op Hop. unfold ws_blk_hdr. apply wlegal_app. split.
  { repeat (apply wlegal_cons; split; [cbn; lia|]). apply wlegal_nil. }
  apply wlegal_app. split; [apply ws_u32_legal|].
  repeat (apply wlegal_cons; split; [| try apply wlegal_nil]); cbn [fst snd]; change (2 ^ 8) with 256; try lia.
  - split; [lia|]. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia].
  - split; [lia| apply Z.mod_pos_bound; lia].
  - split; [lia| apply Z.mod_pos_bound; lia].
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ws_lens_row_bits : forall n len t i curr rest, wlegal rest ->
  wbits (ws_lens_row n len t i curr ++ rest) = wbits (ws_drow n (fun v => zget len (258 * t + v)) i curr ++ rest) /\
  wlegal (ws_lens_row n len t i curr).
Proof.
  induction n as [|n IH]; intros len t i curr rest HR; cbn [ws_lens_row ws_drow]; [split; [reflexivity| apply wlegal_nil]|].
  set (tgt := zget len (258 * t + i)).
  destruct (IH len t (i + 1) tgt rest HR) as [E1 L1].
  assert (LD : wlegal (ws_delta curr tgt)).
  { unfold ws_delta. apply wlegal_app. split; [destruct (curr <? tgt); apply wlegal_repeat; cbn; lia|]. apply wlegal_cons. split; [cbn; lia| apply wlegal_nil]. }
  set (dstp := if curr <? tgt then dsteps true (Z.to_nat (tgt - curr)) else dsteps false (Z.to_nat (curr - tgt))).
  assert (LS : wlegal dstp) by (subst dstp; destruct (curr <? tgt); apply dsteps_legal).
  assert (L10 : wlegal [(1, 0)]) by (apply wlegal_cons; split; [cbn; lia| apply wlegal_nil]).
  assert (ED : wbits (ws_delta curr tgt) = wbits (dstp ++ [(1, 0)])).
  { unfold ws_delta. subst dstp. rewrite !wbits_app; try assumption; try (destruct (curr <? tgt); apply wlegal_repeat; cbn; lia).
    f_equal. destruct (curr <? tgt); [apply wbits_dsteps_up| apply wbits_dsteps_down]. }
  split; [| apply wlegal_app; split; [exact LD| exact L1]].
  rewrite <- app_assoc. rewrite wbits_app by (try exact LD; apply wlegal_app; split; assumption). rewrite E1, ED.
  rewrite <- wbits_app; [| apply wlegal_app; split; assumption| apply wlegal_app; split; [apply ws_drow_legal| exact HR]].
  f_equal. rewrite <- !app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
End BzR5cX.

Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mtf1 (pos : Z -> Z) (j : Z) : Z -> Z :=
  fun k => if k =? 0 then pos j else if (0 <? k) && (k <=? j) then pos (k - 1) else pos k.

Section SelMtf.
  Variable nG : Z.
  Hypothesis HnG : 1 <= nG <= 8.
  (* [comment removed for export] *)
  Definition PINV (pos : Z -> Z) : Prop :=
    (forall k, 0 <= k < nG -> 0 <= pos k < nG) /\ (forall v, 0 <= v < nG -> exists k, 0 <= k < nG /\ pos k = v).

  Lemma mtf1_PINV : forall pos j, PINV pos -> 0 <= j < nG -> PINV (mtf1 pos j).
  Proof.
    intros pos j [R S] Hj. split.
    - intros k Hk. unfold mtf1. destruct (Z.eqb_spec k 0); [apply R; lia|].
      destruct (Z.ltb_spec 0 k), (Z.leb_spec k j); cbn; apply R; lia.
    - intros v Hv. cps_destruct (S v Hv) as (k & Hk & E). unfold mtf1.
      destruct (Z.eq_dec k j) as [->|NE].
      + exists 0. split; [lia|]. rewrite Z.eqb_refl. exact E.
      + destruct (Z.lt_ge_cases k j) as [LT|GE].
        * exists (k + 1). split; [lia|]. replace (k + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
          replace ((0 <? k + 1) && (k + 1 <=? j))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.ltb_lt| apply Z.leb_le]; lia).
          replace (k + 1 - 1) with k by lia. exact E.
        * exists k. split; [lia|]. replace (k =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
          replace ((0 <? k) && (k <=? j))%bool with false by (symmetry; apply Bool.andb_false_iff; right; apply Z.leb_gt; lia). exact E.
  Qed.

  (* [comment removed for export] *)
  Lemma pos_search_spec : forall f pos0 (pos : zarr) x j,
    0 <= j -> (Z.to_nat (nG - j) <= f)%nat ->
    (exists j0, j <= j0 < nG /\ pos0 j0 = x /\ forall k, j <= k < j0 -> pos0 k <> x) ->
    (forall k, 0 <= k < nG -> (k <= 0 \/ j < k) -> zget pos k = pos0 k) -> (forall k, 1 <= k <= j -> zget pos k = pos0 (k - 1)) ->
    let '(pos', tmp, j') := sm_pos_search f pos x (pos0 j) j in
    tmp = x /\ pos0 j' = x /\ j <= j' < nG /\ (forall k, j <= k < j' -> pos0 k <> x) /\
    (forall k, 0 <= k < nG -> (k <= 0 \/ j' < k) -> zget pos' k = pos0 k) /\ (forall k, 1 <= k <= j' -> zget pos' k = pos0 (k - 1)) /\
    (forall k, (k < 0 \/ nG <= k) -> zget pos' k = zget pos k).
  Proof.
    induction f as [|f IH]; (intros pos0 pos x j Hj Hf; cps_intros (j0 & R0 & E0 & N0); intros P1 P2).
    - exfalso. lia.
    - cbn [sm_pos_search]. destruct (Z.eqb_spec x (pos0 j)) as [E|NE].
      + split; [auto|]. split; [auto|]. split; [lia|]. split; [intros; lia|]. split; [exact P1|]. split; [exact P2| intros; reflexivity].
      + assert (j <> j0) by (intros ->; congruence).
        rewrite (P1 (j + 1)) by lia.
        assert (A1 : exists j1, j + 1 <= j1 < nG /\ pos0 j1 = x /\ forall k, j + 1 <= k < j1 -> pos0 k <> x).
        { exists j0. split; [lia|]. split; [exact E0|]. intros k Hk. apply N0; lia. }
        assert (A2 : forall k, 0 <= k < nG -> (k <= 0 \/ j + 1 < k) -> zget (zset pos (j + 1) (pos0 j)) k = pos0 k).
        { intros k Hk Hk2. rewrite zget_zset_other by lia. apply P1; lia. }
        assert (A3 : forall k, 1 <= k <= j + 1 -> zget (zset pos (j + 1) (pos0 j)) k = pos0 (k - 1)).
        { intros k Hk. destruct (Z.eq_dec k (j + 1)) as [->|NK]; [rewrite zget_zset_same; f_equal; lia|]. rewrite zget_zset_other by lia. apply P2. lia. }
        pose proof (IH pos0 (zset pos (j + 1) (pos0 j)) x (j + 1) ltac:(lia) ltac:(lia) A1 A2 A3) as IH'. clear IH.
        destruct (sm_pos_search f _ x _ (j + 1)) as [[pos' tmp] j']. cps_destruct IH' as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
        split; [exact T1|]. split; [exact T2|]. split; [lia|]. split; [| split; [exact T5| split; [exact T6|]]].
        * intros k Hk. destruct (Z.eq_dec k j) as [->|NK]; [congruence| apply T4; lia].
        * intros k Hk. rewrite T7 by lia. apply zget_zset_other. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pos_shift_spec : forall f v pos, 0 <= v -> (Z.to_nat v <= f)%nat ->
    (forall k, 1 <= k <= v -> zget (pos_shift f v pos) k = zget pos (k - 1)) /\
    (forall k, (k <= 0 \/ v < k) -> zget (pos_shift f v pos) k = zget pos k).
  Proof.
    induction f as [|f IH]; intros v pos Hv Hf; cbn [pos_shift].
    - split; intros; [lia| reflexivity].
    - destruct (Z.ltb_spec 0 v) as [GT|LE].
      + destruct (IH (v - 1) (zset pos v (zget pos (v - 1))) ltac:(lia) ltac:(lia)) as [A B]. split.
        * intros k Hk. destruct (Z.eq_dec k v) as [->|NK]; [rewrite B by lia; apply zget_zset_same|]. rewrite A by lia. apply zget_zset_other. lia.
        * intros k Hk. rewrite B by lia. apply zget_zset_other. lia.
      + split; intros; [lia| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma first_hit : forall m (P : Z -> bool) a b, (Z.to_nat (b - a) <= m)%nat ->
    (exists k, a <= k < b /\ P k = true) -> exists j0, a <= j0 < b /\ P j0 = true /\ forall k, a <= k < j0 -> P k = false.
  Proof.
    induction m as [|m IH]; (intros P a b Hm; cps_intros (k & Hk & Pk)); [lia|].
    destruct (P a) eqn:Pa.
    - exists a. split; [lia|]. split; [exact Pa| intros; lia].
    - cps_destruct (IH P (a + 1) b ltac:(lia)) as (j0 & H0 & P0 & N0).
      { exists k. split; [| exact Pk]. destruct (Z.eq_dec k a) as [->|NE]; [congruence| lia]. }
      exists j0. split; [lia|]. split; [exact P0|]. intros k' Hk'. destruct (Z.eq_dec k' a) as [->|NE]; [exact Pa| apply N0; lia].
  Qed.

  (* [comment removed for export] *)
  Theorem selmtf_undo : forall n (pos0 : Z -> Z) pose posd sel selMtf seld i,
    PINV pos0 -> 0 <= i -> (forall k, 0 <= k < nG -> zget pose k = pos0 k /\ zget posd k = pos0 k) ->
    (forall k, i <= k < i + Z.of_nat n -> 0 <= zget sel k < nG) ->
    let '(_, selMtf') := sm_selmtf n pose sel selMtf i in
    let '(_, sel') := sel_undo n i posd selMtf' seld in
    (forall k, i <= k < i + Z.of_nat n -> zget sel' k = zget sel k) /\
    (forall k, (k < i \/ i + Z.of_nat n <= k) -> zget sel' k = zget seld k) /\
    (forall k, i <= k < i + Z.of_nat n -> 0 <= zget selMtf' k < nG) /\
    (forall k, (k < i \/ i + Z.of_nat n <= k) -> zget selMtf' k = zget selMtf k).
  Proof.
    induction n as [|n IH]; intros pos0 pose posd sel selMtf seld i PI Hi AG HS.
    - cbn. split; [intros; lia|]. split; [intros; reflexivity|]. split; [intros; lia| intros; reflexivity].
    - cbn [sm_selmtf sel_undo].
      set (x := zget sel i). pose proof (HS i ltac:(lia)) as Hx. fold x in Hx.
      destruct PI as [PR PS].
      cps_destruct (first_hit (Z.to_nat nG) (fun k => pos0 k =? x) 0 nG ltac:(lia)) as (j0 & R0 & E0 & N0).
      { cps_destruct (PS x Hx) as (k0 & Hk0 & Ek). exists k0. split; [exact Hk0| apply Z.eqb_eq; exact Ek]. }
      apply Z.eqb_eq in E0.
      pose proof (pos_search_spec 8 pos0 pose x 0 ltac:(lia) ltac:(lia)) as SR.
      replace (pos0 0) with (zget pose 0) in SR by (exact (proj1 (AG 0 ltac:(lia)))).
      assert (B1 : exists j1, 0 <= j1 < nG /\ pos0 j1 = x /\ forall k, 0 <= k < j1 -> pos0 k <> x).
      { exists j0. split; [lia|]. split; [exact E0|]. intros k Hk. apply Z.eqb_neq. apply N0. lia. }
      assert (B2 : forall k, 0 <= k < nG -> (k <= 0 \/ 0 < k) -> zget pose k = pos0 k) by (intros k Hk _; apply AG; exact Hk).
      assert (B3 : forall k, 1 <= k <= 0 -> zget pose k = pos0 (k - 1)) by (intros; lia).
      specialize (SR B1 B2 B3).
      destruct (sm_pos_search 8 pose x (zget pose 0) 0) as [[pos1 tmp] j]. cps_destruct SR as (T1 & T2 & T3 & T4 & T5 & T6 & T7). subst tmp.
      (* [comment removed for export] *)
      set (pose' := zset pos1 0 x).
      set (posd' := zset (pos_shift 8 j posd) 0 (zget posd j)).
      assert (AG' : forall k, 0 <= k < nG -> zget pose' k = mtf1 pos0 j k /\ zget posd' k = mtf1 pos0 j k).
      { intros k Hk. subst pose' posd'. unfold mtf1.
        destruct (pos_shift_spec 8 j posd ltac:(lia) ltac:(lia)) as [S1 S2].
        destruct (Z.eqb_spec k 0) as [->|NK].
        - rewrite !zget_zset_same. split; [symmetry; exact T2| apply AG; lia].
        - rewrite !zget_zset_other by lia. destruct (Z.ltb_spec 0 k), (Z.leb_spec k j); cbn [andb]; try lia.
          + split; [apply T6; lia|]. rewrite S1 by lia. apply AG. lia.
          + split; [apply T5; lia|]. rewrite S2 by lia. apply AG. lia. }
      pose proof (IH (mtf1 pos0 j) pose' posd' sel (zset selMtf i j) (zset seld i (zget posd j)) (i + 1)
                    (mtf1_PINV pos0 j (conj PR PS) ltac:(lia)) ltac:(lia) AG' ltac:(intros; apply HS; lia)) as IH'.
      destruct (sm_selmtf n pose' sel (zset selMtf i j) (i + 1)) as [pe selMtf'].
      assert (Ej : zget selMtf' i = j).
      { destruct (sel_undo n (i + 1) posd' selMtf' (zset seld i (zget posd j))) as [pd0 sel0].
        cps_destruct IH' as (_ & _ & _ & R4). rewrite R4 by lia. apply zget_zset_same. }
      rewrite Ej. fold posd'.
      destruct (sel_undo n (i + 1) posd' selMtf' _) as [pd sel'].
      cps_destruct IH' as (R1 & R2 & R3 & R4).
      split; [| split; [| split]].
      + intros k Hk. destruct (Z.eq_dec k i) as [->|NK]; [| apply R1; lia].
        rewrite R2 by lia. rewrite zget_zset_same. rewrite (proj2 (AG j ltac:(lia))). subst x. exact T2.
      + intros k Hk. rewrite R2 by lia. apply zget_zset_other. lia.
      + intros k Hk. destruct (Z.eq_dec k i) as [->|NK]; [| apply R3; lia]. rewrite Ej. lia.
      + intros k Hk. rewrite R4 by lia. apply zget_zset_other. lia.
  Qed.
End SelMtf.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ztabs_get : forall n t aS lnT a, (aS <= 258)%nat ->
  (forall t' v, t <= t' < t + Z.of_nat n -> 0 <= v < Z.of_nat aS -> zget (ztabs n t aS lnT a) (258 * t' + v) = lnT t' v) /\
  (forall c, (c < 258 * t \/ 258 * (t + Z.of_nat n) <= c \/ Z.of_nat aS <= c mod 258) -> zget (ztabs n t aS lnT a) c = zget a c).
Proof.
  induction n as [|n IH]; intros t aS lnT a HaS; cbn [ztabs].
  - split; [intros; lia| intros; reflexivity].
  - destruct (IH (t + 1) aS lnT (zsets aS (258 * t) (fun c : Z => Some (lnT t (c - 258 * t))) a) HaS) as [A B]. split.
    + intros t' v Ht Hv. destruct (Z.eq_dec t' t) as [->|NE].
      * rewrite B. 2:{ left. lia. }
        rewrite zsets_get. replace ((258 * t <=? 258 * t + v) && (258 * t + v <? 258 * t + Z.of_nat aS))%bool with true
          by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
        f_equal. lia.
      * apply A; lia.
    + intros c Hc. rewrite B.
      * rewrite zsets_get. destruct (Z.leb_spec (258 * t) c), (Z.ltb_spec c (258 * t + Z.of_nat aS)); cbn [andb]; try reflexivity.
        exfalso. destruct Hc as [Hc|[Hc|Hc]]; try lia.
        replace c with ((c - 258 * t) + t * 258) in Hc by lia. rewrite Z_mod_plus_full, Z.mod_small in Hc by lia. lia.
      * destruct Hc as [Hc|[Hc|Hc]]; [left; lia| right; left; lia| right; right; exact Hc].
Qed.

(* [comment removed for export] *)
Lemma minmax_len_spec : forall n i len off mn0 mx0,
  let '(mn, mx) := minmax_len n i len off mn0 mx0 in
  mn <= mn0 /\ mx0 <= mx /\ (forall v, i <= v < i + Z.of_nat n -> mn <= zget len (off + v) <= mx) /\
  (mn = mn0 \/ exists v, i <= v < i + Z.of_nat n /\ mn = zget len (off + v)) /\
  (mx = mx0 \/ exists v, i <= v < i + Z.of_nat n /\ mx = zget len (off + v)).
Proof.
  induction n as [|n IH]; intros i len off mn0 mx0; cbn [minmax_len].
  - split; [lia|]. split; [lia|]. split; [intros; lia|]. split; left; reflexivity.
  - set (l := zget len (off + i)).
    specialize (IH (i + 1) len off (if l <? mn0 then l else mn0) (if mx0 <? l then l else mx0)).
    destruct (minmax_len n (i + 1) len off _ _) as [mn mx]. cps_destruct IH as (A & B & C & D & E).
    destruct (Z.ltb_spec l mn0), (Z.ltb_spec mx0 l).
    all: split; [lia|]; split; [lia|]; split; [intros v Hv; destruct (Z.eq_dec v i) as [->|NE]; [fold l; lia| apply C; lia]|].
    all: split; [destruct D as [D|(v & Hv & D)]; [| right; exists v; split; [lia| exact D]] | destruct E as [E'|(v & Hv & E')]; [| right; exists v; split; [lia| exact E']]].
    all: try (left; exact D); try (left; exact E'); try (right; exists i; split; [lia| exact D]); try (right; exists i; split; [lia| exact E']).
Qed.

Lemma sm_minmax_eq : forall n len t i mn mx, sm_minmax n len t i mn mx = minmax_len n i len (258 * t) mn mx.
Proof. induction n as [|n IH]; intros; cbn [sm_minmax minmax_len]; [reflexivity| apply IH]. Qed.

(* [comment removed for export] *)
Section MakeTables.
  Variables (aS : Z) (len0 : zarr).
  Hypothesis HaS : 1 <= aS <= 258.
  Let Lf (t : Z) : Z -> Z := Lrow len0 (258 * t).

  Definition grp_ok (limit base perm minLens : zarr) (t mn mx : Z) : Prop :=
    1 <= mn /\ mx <= 20 /\ (forall v, 0 <= v < aS -> mn <= Lf t v <= mx) /\ zget minLens t = mn /\
    (forall n, mn <= n <= mx -> zget limit (258 * t + n) = wsum (Lf t) aS n - 1) /\
    (forall n, mn <= n <= mx -> zget base (258 * t + n) = fcode (Lf t) aS n - cnt_lt (Lf t) aS n) /\
    (forall j, 0 <= j < aS -> zget perm (258 * t + crank (Lf t) aS j) = j).

  Lemma make_tables_spec : forall n t d, 0 <= t -> d_len d = len0 ->
    (forall t' v, t <= t' < t + Z.of_nat n -> 0 <= v < aS -> 1 <= Lf t' v <= 20) ->
    let D := make_tables n t aS d in
    (forall t', t <= t' < t + Z.of_nat n -> exists mn mx, grp_ok (d_limit D) (d_base D) (d_perm D) (d_minLens D) t' mn mx) /\
    d_len D = len0 /\
    (forall p, (p < 258 * t) -> zget (d_limit D) p = zget (d_limit d) p /\ zget (d_base D) p = zget (d_base d) p /\ zget (d_perm D) p = zget (d_perm d) p) /\
    (forall t', (t' < t \/ t + Z.of_nat n <= t') -> zget (d_minLens D) t' = zget (d_minLens d) t') /\
    (forall F : dst -> Prop, (forall x li ba pe ml, F x -> F (d_set_minLens (d_set_perm (d_set_base (d_set_limit x li) ba) pe) ml)) -> F d -> F D).
  Proof.
    induction n as [|n IH]; intros t d Ht HL HR; cbv zeta.
    - cbn [make_tables]. split; [intros; lia|]. split; [exact HL|]. split; [intros; repeat split; reflexivity|]. split; [intros; reflexivity|]. intros F _ HF; exact HF.
    - rewrite make_tables_S. cbv zeta. rewrite HL.
      pose proof (minmax_len_spec (Z.to_nat aS) 0 len0 (258 * t) 32 0) as MM.
      destruct (minmax_len (Z.to_nat aS) 0 len0 (258 * t) 32 0) as [mn mx]. cps_destruct MM as (M1 & M2 & M3 & M4 & M5).
      assert (R : forall v, 0 <= v < aS -> 1 <= Lf t v <= 20) by (intros; apply HR; lia).
      assert (Bmn : 1 <= mn /\ mx <= 20 /\ mn <= mx).
      { pose proof (R 0 ltac:(lia)) as R0. pose proof (M3 0 ltac:(lia)) as C0. unfold Lf, Lrow in R0.
        destruct M4 as [M4|(v & Hv & M4)]; [lia|]. destruct M5 as [M5|(v' & Hv' & M5)]; [lia|].
        pose proof (R v ltac:(lia)). pose proof (R v' ltac:(lia)). unfold Lf, Lrow in *. lia. }
      pose proof (hbCreateDecodeTables_spec len0 (258 * t) aS ltac:(lia) (d_limit d) (d_base d) (d_perm d) mn mx ltac:(lia) ltac:(lia)) as HB.
      destruct (hbCreateDecodeTables (d_limit d) (d_base d) (d_perm d) len0 (258 * t) mn mx aS) as [[li ba] pe].
      cps_destruct HB as (H1 & H2 & H3 & H4 & H5 & H6).
      { intros j Hj. apply M3. lia. }
      set (d1 := d_set_minLens (d_set_perm (d_set_base (d_set_limit d li) ba) pe) (zset (d_minLens d) t mn)).
      cps_destruct (IH (t + 1) d1 ltac:(lia) ltac:(subst d1; exact HL) ltac:(intros; apply HR; lia)) as (G1 & G2 & G3 & G4 & G5).
      split; [| split; [exact G2| split; [| split]]].
      + intros t' Ht'. destruct (Z.eq_dec t' t) as [->|NE]; [| apply G1; lia].
        exists mn, mx. unfold grp_ok.
        cps_destruct (G3 (258 * t + 257) ltac:(lia)) as (_ & _ & _).
        split; [lia|]. split; [lia|]. split; [intros v Hv; apply M3; lia|]. split; [rewrite G4 by lia; subst d1; cbn; apply zget_zset_same|].
        split; [| split].
        * intros k Hk. cps_destruct (G3 (258 * t + k) ltac:(lia)) as (E1 & _ & _). rewrite E1. subst d1; cbn. apply H1. exact Hk.
        * intros k Hk. cps_destruct (G3 (258 * t + k) ltac:(lia)) as (_ & E2 & _). rewrite E2. subst d1; cbn. apply H2. exact Hk.
        * intros j Hj. pose proof (crank_range (Lf t) aS j Hj) as CR. cps_destruct (G3 (258 * t + crank (Lf t) aS j) ltac:(lia)) as (_ & _ & E3). rewrite E3. subst d1; cbn. apply H3. exact Hj.
      + intros p Hp. cps_destruct (G3 p ltac:(lia)) as (E1 & E2 & E3). rewrite E1, E2, E3. subst d1; cbn.
        split; [apply H4; lia|]. split; [apply H5; lia| apply H6; lia].
      + intros t' Ht'. rewrite G4 by lia. subst d1; cbn. apply zget_zset_other. lia.
      + intros F HF Fd. apply G5; [exact HF|]. subst d1. apply HF. exact Fd.
  Qed.
End MakeTables.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mkmaps_spec : forall n inE inD unseq s2u i n0,
  0 <= i -> 0 <= n0 -> (forall k, i <= k < i + Z.of_nat n -> (zget inE k =? 0) = (zget inD k =? 0)) ->
  let '(unseq', nE) := mk_maps n inE unseq i n0 in
  let '(s2u', nD) := mkmaps n i inD s2u n0 in
  nE = nD /\ n0 <= nE <= n0 + Z.of_nat n /\
  (forall k, i <= k < i + Z.of_nat n -> zget inE k <> 0 -> n0 <= zget unseq' k < nE /\ zget s2u' (zget unseq' k) = k) /\
  (forall v, n0 <= v < nE -> i <= zget s2u' v < i + Z.of_nat n /\ zget inE (zget s2u' v) <> 0 /\ zget unseq' (zget s2u' v) = v) /\
  (forall k, (k < i \/ i + Z.of_nat n <= k) -> zget unseq' k = zget unseq k) /\
  (forall v, (v < n0 \/ nE <= v) -> zget s2u' v = zget s2u v).
Proof.
  induction n as [|n IH]; intros inE inD unseq s2u i n0 Hi Hn0 HZ; cbn [mk_maps mkmaps].
  - split; [reflexivity|]. split; [lia|]. split; [intros; lia|]. split; [intros; lia|]. split; intros; reflexivity.
  - rewrite <- (HZ i) by lia. destruct (Z.eqb_spec (zget inE i) 0) as [E0|NE0]; cbn [negb].
    + specialize (IH inE inD unseq s2u (i + 1) n0 ltac:(lia) Hn0 ltac:(intros; apply HZ; lia)).
      destruct (mk_maps n inE unseq (i + 1) n0) as [unseq' nE]. destruct (mkmaps n (i + 1) inD s2u n0) as [s2u' nD].
      cps_destruct IH as (A & B & C & D & E & F). split; [exact A|]. split; [lia|]. split; [| split; [| split]].
      * intros k Hk NZ. destruct (Z.eq_dec k i) as [->|NK]; [congruence|]. apply C; [lia| exact NZ].
      * intros v Hv. cps_destruct (D v Hv) as (D1 & D2 & D3). split; [lia|]. split; assumption.
      * intros k Hk. apply E. lia.
      * exact F.
    + specialize (IH inE inD (zset unseq i n0) (zset s2u n0 i) (i + 1) (n0 + 1) ltac:(lia) ltac:(lia) ltac:(intros; apply HZ; lia)).
      destruct (mk_maps n inE (zset unseq i n0) (i + 1) (n0 + 1)) as [unseq' nE]. destruct (mkmaps n (i + 1) inD (zset s2u n0 i) (n0 + 1)) as [s2u' nD].
      cps_destruct IH as (A & B & C & D & E & F). split; [exact A|]. split; [lia|]. split; [| split; [| split]].
      * intros k Hk NZ. destruct (Z.eq_dec k i) as [->|NK].
        -- rewrite E by lia. rewrite zget_zset_same. split; [lia|]. rewrite F by lia. apply zget_zset_same.
        -- destruct (C k ltac:(lia) NZ) as [C1 C2]. split; [lia| exact C2].
      * intros v Hv. destruct (Z.eq_dec v n0) as [->|NV].
        -- rewrite F by lia. rewrite zget_zset_same. split; [lia|]. split; [exact NE0|]. rewrite E by lia. apply zget_zset_same.
        -- cps_destruct (D v ltac:(lia)) as (D1 & D2 & D3). split; [lia|]. split; assumption.
      * intros k Hk. rewrite E by lia. apply zget_zset_other. lia.
      * intros v Hv. rewrite F by lia. apply zget_zset_other. lia.
Qed.

Lemma clear256_get : forall n i a c, zget (clear256 n i a) c = (if (i <=? c) && (c <? i + Z.of_nat n) then 0 else zget a c)%bool.
Proof.
  induction n as [|n IH]; intros i a c; cbn [clear256].
  - destruct (Z.leb_spec i c), (Z.ltb_spec c (i + Z.of_nat 0)); cbn; try reflexivity; lia.
  - rewrite IH, zget_zset. destruct (Z.leb_spec (i + 1) c), (Z.ltb_spec c (i + 1 + Z.of_nat n)), (Z.eqb_spec c i), (Z.leb_spec i c), (Z.ltb_spec c (i + Z.of_nat (S n))); cbn; try reflexivity; lia.
Qed.

Lemma map_rows_inUse : forall n i g16 bit d c,
  0 <= i ->
  zget (d_inUse (map_rows n i g16 bit d)) c =
  (if (16 * i <=? c) && (c <? 16 * (i + Z.of_nat n)) && negb (g16 (c / 16) =? 0) && (bit c =? 1) then 1 else zget (d_inUse d) c)%bool.
Proof.
  induction n as [|n IH]; intros i g16 bit d c Hi; cbn [map_rows].
  - destruct (Z.leb_spec (16 * i) c), (Z.ltb_spec c (16 * (i + Z.of_nat 0))); cbn [andb]; try reflexivity; lia.
  - rewrite IH by lia.
    assert (ROW : forall x, zget (d_inUse (if negb (g16 i =? 0) then d_set_inUse (d_set_state x 29) (zsets 16 (i * 16) (rowf bit) (d_inUse x)) else x)) c =
                      (if (16 * i <=? c) && (c <? 16 * i + 16) && negb (g16 i =? 0) && (bit c =? 1) then 1 else zget (d_inUse x) c)%bool).
    { intros x. destruct (negb (g16 i =? 0)); cbn [d_inUse d_set_inUse d_set_state andb].
      - rewrite zsets_get. unfold rowf. replace (i * 16) with (16 * i) by lia. change (Z.of_nat 16) with 16.
        destruct (Z.leb_spec (16 * i) c), (Z.ltb_spec c (16 * i + 16)); cbn [andb]; try reflexivity. destruct (bit c =? 1); reflexivity.
      - destruct ((16 * i <=? c) && (c <? 16 * i + 16))%bool; reflexivity. }
    rewrite ROW.
    destruct (Z.leb_spec (16 * i) c) as [A|A]; cbn [andb].
    + destruct (Z.ltb_spec c (16 * i + 16)) as [B|B]; cbn [andb].
      * replace (16 * (i + 1) <=? c) with false by (symmetry; apply Z.leb_gt; lia). cbn [andb].
        replace (c <? 16 * (i + Z.of_nat (S n))) with true by (symmetry; apply Z.ltb_lt; lia).
        replace (c / 16) with i by (apply (Z.div_unique c 16 i (c - 16 * i)); lia). reflexivity.
      * replace (16 * (i + 1) <=? c) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
        destruct (Z.ltb_spec c (16 * (i + 1 + Z.of_nat n))), (Z.ltb_spec c (16 * (i + Z.of_nat (S n)))); cbn [andb]; try reflexivity; lia.
    + replace (16 * (i + 1) <=? c) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sm_in16_row_spec : forall n inUse i j acc, (acc = 0 \/ acc = 1) ->
  sm_in16_row n inUse i j acc = 1 /\ (acc = 1 \/ exists j', j <= j' < j + Z.of_nat n /\ zget inUse (i * 16 + j') <> 0) \/
  sm_in16_row n inUse i j acc = 0 /\ acc = 0 /\ (forall j', j <= j' < j + Z.of_nat n -> zget inUse (i * 16 + j') = 0).
Proof.
  induction n as [|n IH]; intros inUse i j acc Hacc; cbn [sm_in16_row].
  - destruct Hacc as [-> | ->]; [right; repeat split; intros; lia| left; split; [reflexivity| left; reflexivity]].
  - destruct (Z.eqb_spec (zget inUse (i * 16 + j)) 0) as [E|NE]; cbn [negb].
    + destruct (IH inUse i (j + 1) acc Hacc) as [[A [B|(j' & Hj' & C)]]|(A & B & C)].
      * left. split; [exact A| left; exact B].
      * left. split; [exact A| right; exists j'; split; [lia| exact C]].
      * right. split; [exact A|]. split; [exact B|]. intros j' Hj'. destruct (Z.eq_dec j' j) as [->|NJ]; [exact E| apply C; lia].
    + destruct (IH inUse i (j + 1) 1 ltac:(right; reflexivity)) as [[A _]|(A & B & C)]; [| lia].
      left. split; [exact A|]. right. exists j. split; [lia| exact NE].
Qed.
Lemma sm_in16_get : forall n in16 inUse i c,
  zget (sm_in16 n in16 inUse i) c = (if (i <=? c) && (c <? i + Z.of_nat n) then sm_in16_row 16 inUse c 0 0 else zget in16 c)%bool.
Proof.
  induction n as [|n IH]; intros in16 inUse i c; cbn [sm_in16].
  - destruct (Z.leb_spec i c), (Z.ltb_spec c (i + Z.of_nat 0)); cbn; try reflexivity; lia.
  - rewrite IH, zget_zset. destruct (Z.leb_spec (i + 1) c), (Z.ltb_spec c (i + 1 + Z.of_nat n)), (Z.eqb_spec c i), (Z.leb_spec i c), (Z.ltb_spec c (i + Z.of_nat (S n))); cbn; subst; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
Theorem map_d_inUse : forall inUse in160 crc op d c, 0 <= c < 256 ->
  let in16 := sm_in16 16 in160 inUse 0 in
  (zget (d_inUse (map_d (fun i => bit01 (zget in16 i)) (fun c => bit01 (zget inUse c)) crc op d)) c =? 0) = (zget inUse c =? 0).
Proof.
  intros inUse in160 crc op d c Hc. cbv zeta. unfold map_d. cbv zeta.
  assert (MK : forall x, d_inUse (makeMaps_d x) = d_inUse x).
  { intros x. unfold makeMaps_d. destruct (mkmaps _ _ _ _ _). reflexivity. }
  rewrite MK, map_rows_inUse by lia. cbn [d_inUse d_set_inUse d_set_inUse16 d_set_state d_set_origPtr d_set_rand d_set_sbcrc d_set_blockNo].
  rewrite clear256_get. change (Z.of_nat 256) with 256. change (Z.of_nat 16) with 16.
  replace ((0 <=? c) && (c <? 0 + 256))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
  replace ((16 * 0 <=? c) && (c <? 16 * (0 + 16)))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
  cbn [andb]. rewrite sm_in16_get. change (Z.of_nat 16) with 16.
  assert (R : 0 <= c / 16 < 16) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  replace ((0 <=? c / 16) && (c / 16 <? 0 + 16))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
  unfold bit01. pose proof (Z.div_mod c 16 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound c 16 ltac:(lia)) as MB.
  destruct (sm_in16_row_spec 16 inUse (c / 16) 0 0 ltac:(left; reflexivity)) as [[A B]|(A & _ & C)]; rewrite A; cbn [Z.eqb negb andb].
  - destruct (Z.eqb_spec (zget inUse c) 0); cbn; reflexivity.
  - specialize (C (c mod 16) ltac:(change (Z.of_nat 16) with 16; lia)). replace (c / 16 * 16 + c mod 16) with c in C by lia.
    rewrite C. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pos_init_get : forall n v pos k, zget (pos_init n v pos) k = (if (v <=? k) && (k <? v + Z.of_nat n) then k else zget pos k)%bool.
Proof.
  induction n as [|n IH]; intros v pos k; cbn [pos_init].
  - destruct (Z.leb_spec v k), (Z.ltb_spec k (v + Z.of_nat 0)); cbn; try reflexivity; lia.
  - rewrite IH, zget_zset. destruct (Z.leb_spec (v + 1) k), (Z.ltb_spec k (v + 1 + Z.of_nat n)), (Z.eqb_spec k v), (Z.leb_spec v k), (Z.ltb_spec k (v + Z.of_nat (S n))); cbn; subst; try reflexivity; lia.
Qed.
Lemma yy_init_get' : forall n a i x, zget (yy_init n a i) x = (if (i <=? x) && (x <? i + Z.of_nat n) then x else zget a x)%bool.
Proof.
  induction n as [|n IH]; intros a i x; cbn [yy_init].
  - destruct (Z.leb_spec i x), (Z.ltb_spec x (i + Z.of_nat 0)); cbn; try reflexivity; lia.
  - rewrite IH, zget_zset. destruct (Z.leb_spec (i + 1) x), (Z.ltb_spec x (i + 1 + Z.of_nat n)), (Z.eqb_spec x i), (Z.leb_spec i x), (Z.ltb_spec x (i + Z.of_nat (S n))); cbn; subst; try reflexivity; lia.
Qed.
Lemma sel_undo_ext : forall n i pos a b sel, (forall k, i <= k < i + Z.of_nat n -> zget a k = zget b k) ->
  snd (sel_undo n i pos a sel) = snd (sel_undo n i pos b sel).
Proof.
  induction n as [|n IH]; intros i pos a b sel H; cbn [sel_undo]; [reflexivity|].
  rewrite (H i) by lia. apply IH. intros; apply H; lia.
Qed.

(* [comment removed for export] *)
Theorem sels_d_spec : forall nG nS sel selMtf0 pos0 d k,
  1 <= nG <= 8 -> 0 <= nS -> (forall k, 0 <= k < nS -> 0 <= zget sel k < nG) ->
  let selMtf := snd (sm_selmtf (Z.to_nat nS) (yy_init (Z.to_nat nG) pos0 0) sel selMtf0 0) in
  (0 <= k < nS -> zget (d_sel (sels_d (fun j => zget selMtf j) nS nG d)) k = zget sel k) /\
  (0 <= k < nS -> 0 <= zget selMtf k < nG).
Proof.
  intros nG nS sel selMtf0 pos0 d k HnG HnS HS. cbv zeta.
  pose proof (selmtf_undo nG HnG (Z.to_nat nS) (fun v => v) (yy_init (Z.to_nat nG) pos0 0) (pos_init (Z.to_nat nG) 0 znew) sel selMtf0
                (d_sel d) 0) as SU.
  destruct (sm_selmtf (Z.to_nat nS) (yy_init (Z.to_nat nG) pos0 0) sel selMtf0 0) as [pe selMtf] eqn:SM. cbn [snd].
  assert (PI : PINV nG (fun v : Z => v)) by (split; [intros; lia| intros v Hv; exists v; split; [lia| reflexivity]]).
  assert (AG : forall k0, 0 <= k0 < nG -> zget (yy_init (Z.to_nat nG) pos0 0) k0 = k0 /\ zget (pos_init (Z.to_nat nG) 0 znew) k0 = k0).
  { intros k0 Hk0. rewrite yy_init_get', pos_init_get.
    replace ((0 <=? k0) && (k0 <? 0 + Z.of_nat (Z.to_nat nG)))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
    split; reflexivity. }
  specialize (SU PI ltac:(lia) AG ltac:(intros; apply HS; lia)).
  unfold sels_d. cbn [d_sel d_set_sel d_set_selMtf d_set_state d_selMtf].
  rewrite (sel_undo_ext (Z.to_nat nS) 0 _ (zsets (Z.to_nat nS) 0 (fun k0 : Z => Some (zget selMtf k0)) (d_selMtf d)) selMtf (d_sel d)).
  2:{ intros k0 Hk0. rewrite zsets_get. replace ((0 <=? k0) && (k0 <? 0 + Z.of_nat (Z.to_nat nS)))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia). reflexivity. }
  destruct (sel_undo (Z.to_nat nS) 0 (pos_init (Z.to_nat nG) 0 znew) selMtf (d_sel d)) as [pd sel']. cbn [snd].
  cps_destruct SU as (R1 & R2 & R3 & R4). split; intros Hk; [apply R1; lia| apply R3; lia].
Qed.

(* [comment removed for export] *)
Theorem lens_d_spec : forall lnT aS nG d, 0 <= aS <= 258 -> 0 <= nG ->
  (forall t v, 0 <= t < nG -> 0 <= v < aS -> zget (d_len (lens_d lnT aS nG d)) (258 * t + v) = lnT t v) /\
  (forall c, (c < 0 \/ 258 * nG <= c \/ aS <= c mod 258) -> zget (d_len (lens_d lnT aS nG d)) c = zget (d_len d) c).
Proof.
  intros lnT aS nG d HaS HnG. unfold lens_d. cbn [d_len d_set_len d_set_state].
  destruct (ztabs_get (Z.to_nat nG) 0 (Z.to_nat aS) lnT (d_len d) ltac:(lia)) as [A B]. split.
  - intros t v Ht Hv. apply A; lia.
  - intros c Hc. apply B. lia.
Qed.
