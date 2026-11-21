(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateOverlay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition BQ (s : deflate_state) : Prop :=
  ds_sym_next s = 3 * nsym s /\ 0 <= nsym s /\ (forall j, 0 <= j < nsym s -> sym_okb s j) /\ freq_hist s.


Lemma BQ_same : forall s s',
  ds_pending_buf s' = ds_pending_buf s -> ds_lit_bufsize s' = ds_lit_bufsize s -> ds_sym_next s' = ds_sym_next s ->
  ds_dyn_ltree_fc s' = ds_dyn_ltree_fc s -> ds_dyn_dtree_fc s' = ds_dyn_dtree_fc s -> ds_bl_tree_fc s' = ds_bl_tree_fc s ->
  BQ s -> BQ s'.
Proof.
  intros s s' E1 E2 E3 E4 E5 E6 H.
  assert (EN : nsym s' = nsym s) by (unfold nsym; rewrite E3; reflexivity).
  assert (ED : forall i, sym_dist s' i = sym_dist s i) by (intros; unfold sym_dist, sym_d0, sym_d1, sym_buf_get; rewrite E1, E2; reflexivity).
  assert (EL : forall i, sym_lc s' i = sym_lc s i) by (intros; unfold sym_lc, sym_buf_get; rewrite E1, E2; reflexivity).
  assert (EC : forall j, sym_lcode s' j = sym_lcode s j) by (intros; unfold sym_lcode; rewrite ED, EL; reflexivity).
  assert (EI : forall j, sym_isdist s' j = sym_isdist s j) by (intros; unfold sym_isdist; rewrite ED; reflexivity).
  assert (EDC : forall j, sym_dcode s' j = sym_dcode s j) by (intros; unfold sym_dcode; rewrite ED; reflexivity).
  destruct H as (A & B & C & D1 & D2 & D3). unfold BQ. rewrite EN, E3. split; [exact A|]. split; [exact B|]. split.
  - intros j Hj. unfold sym_okb. rewrite ED, EL. exact (C j Hj).
  - unfold freq_hist. rewrite EN, E4, E5, E6. split; [|split; [|exact D3]].
    + intros c Hc. rewrite (D1 c Hc). f_equal. apply zsum_ext. intros; rewrite EC; reflexivity.
    + intros d Hd. rewrite (D2 d Hd). apply zsum_ext. intros; rewrite EI, EDC; reflexivity.
Qed.

Lemma BQ_fresh : forall s,
  ds_sym_next s = 0 ->
  (forall c, 0 <= c < L_CODES -> arr_get (ds_dyn_ltree_fc s) c = zind (c =? END_BLOCK)) ->
  (forall d, 0 <= d < D_CODES -> arr_get (ds_dyn_dtree_fc s) d = 0) ->
  (forall b, 0 <= b < BL_CODES -> arr_get (ds_bl_tree_fc s) b = 0) ->
  BQ s /\ nsym s = 0.
Proof.
  intros s H0 HL HD HB. assert (N0 : nsym s = 0) by (unfold nsym; rewrite H0; reflexivity).
  unfold BQ, freq_hist. rewrite N0, H0. split; [|reflexivity]. split; [reflexivity|]. split; [lia|]. split; [intros; lia|].
  split; [|split; [|exact HB]].
  - intros c Hc. rewrite (HL c Hc). reflexivity.
  - intros d Hd. rewrite (HD d Hd). reflexivity.
Qed.

Lemma BQ_freq_bound : forall s, BQ s ->
  (forall c, 0 <= c < L_CODES -> 0 <= arr_get (ds_dyn_ltree_fc s) c <= nsym s + 1)
  /\ (forall d, 0 <= d < D_CODES -> 0 <= arr_get (ds_dyn_dtree_fc s) d <= nsym s).
Proof.
  intros s (_ & N0 & _ & HLf & HDf & _). split.
  - intros c Hc. rewrite (HLf c Hc). pose proof (zind_le1 (c =? END_BLOCK)).
    pose proof (zsum_nonneg (fun j => zind (sym_lcode s j =? c)) 0 (Z.to_nat (nsym s)) ltac:(intros; apply zind_le1)).
    pose proof (zsum_mono (fun j => zind (sym_lcode s j =? c)) (fun _ => 1) 0 (Z.to_nat (nsym s)) ltac:(intros; apply zind_le1)).
    rewrite zsum_const1 in *. lia.
  - intros d Hd. rewrite (HDf d Hd).
    pose proof (zsum_nonneg (fun j => zind (sym_isdist s j && (sym_dcode s j =? d))) 0 (Z.to_nat (nsym s)) ltac:(intros; apply zind_le1)).
    pose proof (zsum_mono (fun j => zind (sym_isdist s j && (sym_dcode s j =? d))) (fun _ => 1) 0 (Z.to_nat (nsym s)) ltac:(intros; apply zind_le1)).
    rewrite zsum_const1 in *. lia.
Qed.


Lemma tally_lit_fields : forall s c,
  let r := fst (tr_tally_lit s c) in
  let lbs := ds_lit_bufsize s in let sn := ds_sym_next s in
  ds_pending_buf r = arr_set (arr_set (arr_set (ds_pending_buf s) (lbs + sn) (wrap8 0)) (lbs + (sn + 1)) (wrap8 0)) (lbs + (sn + 1 + 1)) (wrap8 (wrap8 c))
  /\ ds_sym_next r = sn + 1 + 1 + 1 /\ ds_lit_bufsize r = lbs
  /\ ds_dyn_ltree_fc r = arr_set (ds_dyn_ltree_fc s) (wrap8 c) (wrap16 (arr_get (ds_dyn_ltree_fc s) (wrap8 c) + 1))
  /\ ds_dyn_dtree_fc r = ds_dyn_dtree_fc s /\ ds_bl_tree_fc r = ds_bl_tree_fc s.
Proof.
  intros s c. unfold tr_tally_lit, sym_buf_set, set_Freq, Freq, tree_fc, set_tree_fc. dsred. repeat split; reflexivity.
Qed.

Lemma tally_dist_fields : forall s distance length,
  let r := fst (tr_tally_dist s distance length) in
  let lbs := ds_lit_bufsize s in let sn := ds_sym_next s in
  let len := wrap8 length in let dist := wrap16 distance in
  let lc := arr_get length_code_a len + LITERALS + 1 in
  let L1 := arr_set (ds_dyn_ltree_fc s) lc (wrap16 (arr_get (ds_dyn_ltree_fc s) lc + 1)) in
  ds_pending_buf r = arr_set (arr_set (arr_set (ds_pending_buf s) (lbs + sn) (wrap8 dist)) (lbs + (sn + 1)) (wrap8 (Z.shiftr dist 8))) (lbs + (sn + 1 + 1)) (wrap8 len)
  /\ ds_sym_next r = sn + 1 + 1 + 1 /\ ds_lit_bufsize r = lbs
  /\ ds_dyn_ltree_fc r = L1
  /\ ds_dyn_dtree_fc r = arr_set (ds_dyn_dtree_fc s) (d_code (wrap16 (dist - 1))) (wrap16 (arr_get (ds_dyn_dtree_fc s) (d_code (wrap16 (dist - 1))) + 1))
  /\ ds_bl_tree_fc r = ds_bl_tree_fc s.
Proof.
  intros s distance length. unfold tr_tally_dist, sym_buf_set, set_Freq, Freq, tree_fc, set_tree_fc. dsred. repeat split; reflexivity.
Qed.


Section Tally.
Variable s : deflate_state.
Let n := nsym s.
Hypothesis HBQ : BQ s.
Hypothesis Hroom : ds_lit_bufsize s + ds_sym_next s + 3 <= arr_len (ds_pending_buf s).
Hypothesis Hlbs : 0 <= ds_lit_bufsize s.
Hypothesis Hn : nsym s + 2 < 65536.

Definition tally_shape (s' : deflate_state) (b0 b1 b2 : Z) : Prop :=
  ds_sym_next s' = 3 * n + 3 /\ ds_lit_bufsize s' = ds_lit_bufsize s
  /\ (forall k, 0 <= k < 3 * n -> sym_buf_get s' k = sym_buf_get s k)
  /\ sym_buf_get s' (3 * n) = b0 /\ sym_buf_get s' (3 * n + 1) = b1 /\ sym_buf_get s' (3 * n + 1 + 1) = b2
  /\ 0 <= b0 < 256 /\ 0 <= b1 < 256 /\ 0 <= b2 < 256.

Lemma tally_shape_of_stores : forall s' v0 v1 v2,
  ds_pending_buf s' = arr_set (arr_set (arr_set (ds_pending_buf s) (ds_lit_bufsize s + ds_sym_next s) (wrap8 v0))
                                (ds_lit_bufsize s + (ds_sym_next s + 1)) (wrap8 v1))
                                (ds_lit_bufsize s + (ds_sym_next s + 1 + 1)) (wrap8 v2) ->
  ds_sym_next s' = ds_sym_next s + 1 + 1 + 1 -> ds_lit_bufsize s' = ds_lit_bufsize s ->
  tally_shape s' (wrap8 v0) (wrap8 v1) (wrap8 v2).
Proof.
  intros s' v0 v1 v2 EP EN EL. pose proof (proj1 HBQ) as SN. pose proof (proj1 (proj2 HBQ)) as N0. fold n in SN.
  pose proof (wrap8_range v0). pose proof (wrap8_range v1). pose proof (wrap8_range v2). change (2 ^ 8) with 256 in *.
  assert (G : forall k, sym_buf_get s' k =
     if 3 * n + 1 + 1 =? k then wrap8 v2 else if 3 * n + 1 =? k then wrap8 v1 else if 3 * n =? k then wrap8 v0 else sym_buf_get s k).
  { intros k. unfold sym_buf_get. rewrite EP, EL, !arr_get_set. unfold arr_inb. rewrite !arr_len_set, SN.
    destruct (Z.eqb_spec (3 * n + 1 + 1) k) as [E2|N2].
    { subst k. rewrite Z.eqb_refl. replace ((0 <=? _) && (_ <? _)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). reflexivity. }
    replace (ds_lit_bufsize s + (3 * n + 1 + 1) =? ds_lit_bufsize s + k) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
    destruct (Z.eqb_spec (3 * n + 1) k) as [E1|N1].
    { subst k. rewrite Z.eqb_refl. replace ((0 <=? _) && (_ <? _)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). reflexivity. }
    replace (ds_lit_bufsize s + (3 * n + 1) =? ds_lit_bufsize s + k) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
    destruct (Z.eqb_spec (3 * n) k) as [E0|N0'].
    { subst k. rewrite Z.eqb_refl. replace ((0 <=? _) && (_ <? _)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). reflexivity. }
    replace (ds_lit_bufsize s + 3 * n =? ds_lit_bufsize s + k) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  unfold tally_shape. rewrite EN, EL, SN. split; [lia|]. split; [reflexivity|].
  split. { intros k Hk. rewrite G. replace (3 * n + 1 + 1 =? k) with false by (symmetry; apply Z.eqb_neq; lia).
           replace (3 * n + 1 =? k) with false by (symmetry; apply Z.eqb_neq; lia). replace (3 * n =? k) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  split. { rewrite G. replace (3 * n + 1 + 1 =? 3 * n) with false by (symmetry; apply Z.eqb_neq; lia).
           replace (3 * n + 1 =? 3 * n) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.eqb_refl. reflexivity. }
  split. { rewrite G. replace (3 * n + 1 + 1 =? 3 * n + 1) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.eqb_refl. reflexivity. }
  split. { rewrite G. rewrite Z.eqb_refl. reflexivity. }
  lia.
Qed.

Lemma tally_shape_syms : forall s' b0 b1 b2, tally_shape s' b0 b1 b2 ->
  nsym s' = n + 1
  /\ (forall j, 0 <= j < n -> sym_dist s' (3 * j) = sym_dist s (3 * j) /\ sym_lc s' (3 * j) = sym_lc s (3 * j))
  /\ sym_dist s' (3 * n) = b0 + Z.shiftl b1 8 /\ sym_lc s' (3 * n) = b2.
Proof.
  intros s' b0 b1 b2 (A & B & C & D0 & D1 & D2 & R0 & R1 & R2). pose proof (proj1 (proj2 HBQ)) as N0.
  split; [unfold nsym; rewrite A; Z.to_euclidean_division_equations; lia|]. split.
  - intros j Hj. unfold sym_dist, sym_d0, sym_d1, sym_lc. rewrite !C by lia. split; reflexivity.
  - unfold sym_dist, sym_d0, sym_d1, sym_lc. rewrite D0, D1, D2.
    change 255 with (Z.ones 8). rewrite !Z.land_ones by lia. rewrite !Z.mod_small by lia. split; reflexivity.
Qed.

Lemma tally_shape_BQ : forall s' b0 b1 b2, tally_shape s' b0 b1 b2 ->
  let dist := b0 + Z.shiftl b1 8 in
  dist <= 32768 ->
  ds_bl_tree_fc s' = ds_bl_tree_fc s ->
  (forall c, 0 <= c < L_CODES -> arr_get (ds_dyn_ltree_fc s') c
      = arr_get (ds_dyn_ltree_fc s) c + zind ((if dist =? 0 then b2 else arr_get length_code_a b2 + LITERALS + 1) =? c)) ->
  (forall d, 0 <= d < D_CODES -> arr_get (ds_dyn_dtree_fc s') d
      = arr_get (ds_dyn_dtree_fc s) d + zind (negb (dist =? 0) && (d_code (dist - 1) =? d))) ->
  BQ s' /\ nsym s' = n + 1.
Proof.
  intros s' b0 b1 b2 SH dist Hdist HB HL HD.
  pose proof (tally_shape_syms s' b0 b1 b2 SH) as (N' & OLD & ND & NL). pose proof SH as (A & B & C & _ & _ & _ & R0 & R1 & R2).
  assert (Dn : 0 <= dist) by (subst dist; rewrite Z.shiftl_mul_pow2 by lia; lia).
  destruct HBQ as (_ & N0 & OK & HLf & HDf & HBf).
  assert (ECo : forall j, 0 <= j < n -> sym_lcode s' j = sym_lcode s j /\ sym_isdist s' j = sym_isdist s j /\ sym_dcode s' j = sym_dcode s j).
  { intros j Hj. destruct (OLD j Hj) as [E1 E2]. unfold sym_lcode, sym_isdist, sym_dcode. rewrite E1, E2. repeat split; reflexivity. }
  split; [| exact N'].
  unfold BQ. rewrite N', A. split; [lia|]. split; [lia|]. split.
  - intros j Hj. unfold sym_okb. destruct (Z.eq_dec j n) as [->|NE].
    + rewrite ND, NL. lia.
    + destruct (OLD j ltac:(lia)) as [E1 E2]. rewrite E1, E2. exact (OK j ltac:(lia)).
  - unfold freq_hist. rewrite N', HB. replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia. split; [|split; [|exact HBf]].
    + intros c Hc. rewrite (HL c Hc), (HLf c Hc), zsum_snoc.
      rewrite (zsum_ext (fun j => zind (sym_lcode s' j =? c)) (fun j => zind (sym_lcode s j =? c))) by (intros j Hj; rewrite (proj1 (ECo j ltac:(lia))); reflexivity).
      replace (0 + Z.of_nat (Z.to_nat n)) with n by lia.
      replace (sym_lcode s' n) with (if dist =? 0 then b2 else arr_get length_code_a b2 + LITERALS + 1) by (unfold sym_lcode; rewrite ND, NL; reflexivity).
      cbv delta [n] in *. lia.
    + intros d Hd. rewrite (HD d Hd), (HDf d Hd), zsum_snoc.
      rewrite (zsum_ext (fun j => zind (sym_isdist s' j && (sym_dcode s' j =? d))) (fun j => zind (sym_isdist s j && (sym_dcode s j =? d))))
        by (intros j Hj; destruct (ECo j ltac:(lia)) as (_ & -> & ->); reflexivity).
      replace (0 + Z.of_nat (Z.to_nat n)) with n by lia.
      replace (sym_isdist s' n) with (negb (dist =? 0)) by (unfold sym_isdist; rewrite ND; reflexivity).
      replace (sym_dcode s' n) with (d_code (dist - 1)) by (unfold sym_dcode; rewrite ND; reflexivity). cbv delta [n] in *. lia.
Qed.

Lemma freq_bump : forall (a : arr) (x c E : Z),
  0 <= x < E -> E <= arr_len a -> 0 <= arr_get a x -> arr_get a x + 1 < 65536 -> 0 <= c < E ->
  arr_get (arr_set a x (wrap16 (arr_get a x + 1))) c = arr_get a c + zind (x =? c).
Proof.
  intros a x c E Hx HE H0 H1 Hc. rewrite arr_get_set. unfold arr_inb.
  destruct (Z.eqb_spec x c) as [<-|N]; cbn [andb zind]; [|lia].
  replace ((0 <=? x) && (x <? arr_len a)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  rewrite wrap16_id by lia. reflexivity.
Qed.

Hypothesis HLl : L_CODES <= arr_len (ds_dyn_ltree_fc s).
Hypothesis HDl : D_CODES <= arr_len (ds_dyn_dtree_fc s).

Theorem BQ_tally_lit : forall c,
  let r := fst (tr_tally_lit s c) in
  BQ r /\ nsym r = n + 1 /\ sym_dist r (3 * n) = 0 /\ sym_lc r (3 * n) = wrap8 c
  /\ (forall j, 0 <= j < n -> sym_dist r (3 * j) = sym_dist s (3 * j) /\ sym_lc r (3 * j) = sym_lc s (3 * j)).
Proof.
  intros c r. pose proof (tally_lit_fields s c) as (EP & EN & EL & ELT & EDT & EBT). cbv zeta in *. fold r in EP, EN, EL, ELT, EDT, EBT.
  pose proof (tally_shape_of_stores r 0 0 (wrap8 c) EP EN EL) as SH.
  rewrite (wrap8_id 0) in SH by lia. rewrite (wrap8_id (wrap8 c)) in SH by apply wrap8_range.
  pose proof (tally_shape_syms _ _ _ _ SH) as (N' & OLD & ND & NL). change (0 + Z.shiftl 0 8) with 0 in ND.
  pose proof (wrap8_range c) as Rc. change (2 ^ 8) with 256 in Rc.
  destruct (BQ_freq_bound s HBQ) as [FBL FBD]. fold n in FBL, FBD.
  destruct (tally_shape_BQ _ _ _ _ SH) as [B' _].
  - change (0 + Z.shiftl 0 8) with 0. lia.
  - exact EBT.
  - intros c0 Hc0. change (0 + Z.shiftl 0 8) with 0. cbn [Z.eqb]. rewrite ELT. unfold L_CODES in *.
    pose proof (FBL (wrap8 c) ltac:(lia)). apply (freq_bump _ _ _ 286); lia.
  - intros d Hd. change (0 + Z.shiftl 0 8) with 0. cbn [Z.eqb negb andb zind]. rewrite EDT. lia.
  - split; [exact B'|]. split; [exact N'|]. split; [exact ND|]. split; [exact NL|]. exact OLD.
Qed.

Theorem BQ_tally_dist : forall distance length,
  1 <= distance <= 32768 ->
  let r := fst (tr_tally_dist s distance length) in
  BQ r /\ nsym r = n + 1 /\ sym_dist r (3 * n) = distance /\ sym_lc r (3 * n) = wrap8 length
  /\ (forall j, 0 <= j < n -> sym_dist r (3 * j) = sym_dist s (3 * j) /\ sym_lc r (3 * j) = sym_lc s (3 * j)).
Proof.
  intros distance length Hd r. pose proof (tally_dist_fields s distance length) as (EP & EN & EL & ELT & EDT & EBT). cbv zeta in *.
  fold r in EP, EN, EL, ELT, EDT, EBT.
  rewrite (wrap16_id distance) in EP, EDT by lia. rewrite (wrap16_id (distance - 1)) in EDT by lia.
  pose proof (tally_shape_of_stores r distance (Z.shiftr distance 8) (wrap8 length) EP EN EL) as SH.
  pose proof (wrap8_range length) as Rl. change (2 ^ 8) with 256 in Rl.
  rewrite (wrap8_id (wrap8 length)) in SH by lia.
  assert (DD : wrap8 distance + Z.shiftl (wrap8 (Z.shiftr distance 8)) 8 = distance).
  { rewrite !wrap8_mod, Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
    rewrite (Z.mod_small (distance / 256)) by (Z.to_euclidean_division_equations; lia). Z.to_euclidean_division_equations; lia. }
  pose proof (tally_shape_syms _ _ _ _ SH) as (N' & OLD & ND & NL). rewrite DD in ND.
  destruct (BQ_freq_bound s HBQ) as [FBL FBD]. fold n in FBL, FBD.
  pose proof (length_code_bound (wrap8 length)) as LCB. pose proof (dist_code_bound) as DCB.
  assert (DCR : 0 <= d_code (distance - 1) < 30) by (unfold d_code; destruct (_ <? _); apply DCB).
  destruct (tally_shape_BQ _ _ _ _ SH) as [B' _].
  - rewrite DD. lia.
  - exact EBT.
  - intros c0 Hc0. rewrite DD. replace (distance =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite ELT. unfold L_CODES, LITERALS in *.
    pose proof (FBL (arr_get length_code_a (wrap8 length) + 256 + 1) ltac:(lia)). apply (freq_bump _ _ _ 286); lia.
  - intros d Hd0. rewrite DD. replace (distance =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb andb]. rewrite EDT. unfold D_CODES in *.
    pose proof (FBD (d_code (distance - 1)) ltac:(lia)). apply (freq_bump _ _ _ 30); lia.
  - split; [exact B'|]. split; [exact N'|]. split; [exact ND|]. split; [exact NL|]. exact OLD.
Qed.
End Tally.
