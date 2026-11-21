(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState DeflateSetters Trees TreeModel
  BuildTreeModel GenBitlenModel HuffTree HuffSpec HuffBuild HuffBuild2 HuffFlush HuffSend GenCodesBound
  ScanModel SendModel OverlayFBS OverlayFlush RefFlushBlk11 FB6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import TrApi6u TFB6u_1 TFB6u_8.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.
Lemma tree_fc_set_opt_len : forall s v t', tree_fc (set_opt_len s v) t' = tree_fc s t'.
Proof. intros s v t'; destruct s; destruct t'; reflexivity. Qed.
Lemma tree_fc_set_static_len : forall s v t', tree_fc (set_static_len s v) t' = tree_fc s t'.
Proof. intros s v t'; destruct s; destruct t'; reflexivity. Qed.
Lemma tree_fc_set_bl_count : forall s v t', tree_fc (set_bl_count s v) t' = tree_fc s t'.
Proof. intros s v t'; destruct s; destruct t'; reflexivity. Qed.
Lemma tree_fc_bl_count_set : forall s i v t', tree_fc (bl_count_set s i v) t' = tree_fc s t'.
Proof. intros s i v t'. unfold bl_count_set. apply tree_fc_set_bl_count. Qed.

Lemma tree_fc_gbl1 : forall f s t mc base ml h ov t',
  tree_fc (fst (gen_bitlen_loop1 f s t mc base ml h ov)) t' = tree_fc s t'.
Proof.
  induction f as [|f IH]; intros; cbn [gen_bitlen_loop1 fst]; [reflexivity|].
  destruct (h <? HEAP_SIZE); [|reflexivity].
  destruct (ml <? Len s t (Dad s t (heap_get s h)) + 1);
    (destruct (mc <? heap_get s h); [rewrite IH, tree_fc_set_Len; reflexivity|]);
    rewrite IH; (destruct (stree_has t); rewrite ?tree_fc_set_static_len, tree_fc_set_opt_len, tree_fc_bl_count_set, tree_fc_set_Len; reflexivity).
Qed.

Lemma tree_fc_gbl2 : forall f s ml ov t', tree_fc (gen_bitlen_loop2 f s ml ov) t' = tree_fc s t'.
Proof.
  induction f as [|f IH]; intros; cbn [gen_bitlen_loop2]; [reflexivity|].
  destruct (0 <? ov - 2); rewrite ?IH, !tree_fc_bl_count_set; reflexivity.
Qed.

Lemma tree_fc_gbl3i : forall f s t mc bits n h t',
  tree_fc (fst (gen_bitlen_loop3i f s t mc bits n h)) t' = tree_fc s t'.
Proof.
  induction f as [|f IH]; intros; cbn [gen_bitlen_loop3i fst]; [reflexivity|].
  destruct (negb (n =? 0)); [|reflexivity].
  destruct (mc <? heap_get s (h - 1)); [apply IH|].
  rewrite IH. destruct (negb (Len s t (heap_get s (h - 1)) =? bits)); [|reflexivity].
  rewrite tree_fc_set_Len, tree_fc_set_opt_len. reflexivity.
Qed.

Lemma tree_fc_gbl3 : forall f s t mc bits h t', tree_fc (gen_bitlen_loop3 f s t mc bits h) t' = tree_fc s t'.
Proof.
  induction f as [|f IH]; intros; cbn [gen_bitlen_loop3]; [reflexivity|].
  destruct (negb (bits =? 0)); [|reflexivity].
  destruct (gen_bitlen_loop3i 574 s t mc bits (bl_count_get s bits) h) as [s' h'] eqn:E.
  rewrite IH. pose proof (tree_fc_gbl3i 574 s t mc bits (bl_count_get s bits) h t') as G. rewrite E in G. exact G.
Qed.

Lemma tree_fc_gen_bitlen : forall s t t', tree_fc (gen_bitlen s t) t' = tree_fc s t'.
Proof.
  intros s t t'. unfold gen_bitlen.
  set (s1 := set_Len (set_bl_count s (arr_fill (ds_bl_count s) 0 (MAX_BITS + 1) 0)) t _ 0).
  destruct (gen_bitlen_loop1 573 s1 t (max_code s t) (sd_extra_base t) (sd_max_length t) (ds_heap_max s1 + 1) 0) as [s2 ov] eqn:E.
  assert (G : tree_fc s2 t' = tree_fc s t').
  { pose proof (tree_fc_gbl1 573 s1 t (max_code s t) (sd_extra_base t) (sd_max_length t) (ds_heap_max s1 + 1) 0 t') as G.
    rewrite E in G. cbn [fst] in G. rewrite G. subst s1. rewrite tree_fc_set_Len, tree_fc_set_bl_count. reflexivity. }
  destruct (ov =? 0); rewrite ?tree_fc_gbl3, ?tree_fc_gbl2, G; reflexivity.
Qed.

Lemma tree_dl_gcl2 : forall f s t nc mc n t', tree_dl (gen_codes_loop2 f s t nc mc n) t' = tree_dl s t'.
Proof.
  induction f as [|f IH]; intros; cbn [gen_codes_loop2]; [reflexivity|].
  destruct (n <=? mc); [|reflexivity]. destruct (Len s t n =? 0); [apply IH|].
  rewrite IH. unfold set_Code. destruct s; destruct t; destruct t'; reflexivity.
Qed.
Lemma Len_gen_codes : forall s t mc t' i, Len (gen_codes s t mc) t' i = Len s t' i.
Proof. intros. unfold Len, gen_codes. rewrite tree_dl_gcl2. reflexivity. Qed.

Lemma tree_fc_gcl2_other : forall f s t nc mc n t', t' <> t -> tree_fc (gen_codes_loop2 f s t nc mc n) t' = tree_fc s t'.
Proof.
  induction f as [|f IH]; intros s t nc mc n t' Ht; cbn [gen_codes_loop2]; [reflexivity|].
  destruct (n <=? mc); [|reflexivity]. destruct (Len s t n =? 0); [apply IH; exact Ht|].
  rewrite IH by exact Ht. unfold set_Code. destruct s; destruct t; destruct t'; try reflexivity; exfalso; apply Ht; reflexivity.
Qed.
Lemma tree_fc_gen_codes_other : forall s t mc t', t' <> t -> tree_fc (gen_codes s t mc) t' = tree_fc s t'.
Proof. intros. unfold gen_codes. apply tree_fc_gcl2_other. assumption. Qed.


Lemma elems_le_tsize : forall t, sd_elems t <= tsize t.
Proof. intros [| |]; cbn; unfold L_CODES, D_CODES, BL_CODES, HEAP_SIZE; lia. Qed.

Lemma build_tree_fc15 : forall s t,
  bt_pre s t ->
  (forall j, 0 <= j < sd_elems t -> Freq s t j < 2 ^ 15) ->
  (forall j, 0 <= j <= bt_mc s t -> Len (build_tree s t) t j <> 0 -> 1 <= Len (build_tree s t) t j <= 15) ->
  forall i, 0 <= i < sd_elems t -> 0 <= arr_get (tree_fc (build_tree s t) t) i < 2 ^ 15.
Proof.
  intros s t P HF HL.
  destruct (build_tree_front s t (bp_lens _ _ P) (bp_freq _ _ P) (bp_tot _ _ P) (bp_ol _ _ P) (bp_sl _ _ P))
    as (FC & DL & HP & DP & sub & E & INV).
  pose proof (i_len _ _ _ _ _ _ _ _ _ _ INV) as (LFC & _). pose proof (i_fc _ _ _ _ _ _ _ _ _ _ INV) as IFC.
  pose proof (elems_le_tsize t) as ET.
  rewrite E in HL |- *. intros i Hi.
  apply (gen_codes_b15 _ t (MCP (tree_fc s t) t) (sd_elems t)); [| | | exact Hi].
  - rewrite tree_fc_gen_bitlen, bt_tree_fc. lia.
  - intros j Hj Hnz. specialize (HL j). rewrite !Len_gen_codes in HL. apply HL; [exact Hj | exact Hnz].
  - intros k Hk. rewrite tree_fc_gen_bitlen, bt_tree_fc, IFC by exact Hk.
    unfold FP. destruct (existsb (Z.eqb k) (pads (tree_fc s t) t)); [lia|].
    pose proof (bp_freq _ _ P k Hk) as F0. specialize (HF k Hk). unfold Freq in F0, HF. lia.
Qed.

Lemma build_tree_fc_other : forall s t t',
  bt_pre s t -> t' <> t -> tree_fc (build_tree s t) t' = tree_fc s t'.
Proof.
  intros s t t' P Ht.
  destruct (build_tree_front s t (bp_lens _ _ P) (bp_freq _ _ P) (bp_tot _ _ P) (bp_ol _ _ P) (bp_sl _ _ P))
    as (FC & DL & HP & DP & sub & E & _).
  rewrite E, tree_fc_gen_codes_other, tree_fc_gen_bitlen, bt_tree_fc_other by exact Ht. reflexivity.
Qed.


Lemma st_upd_hit : forall mn b cu pr ct,
  arr_len b = 39 -> bnn b -> 1 <= cu <= 15 -> pr <= 0 -> 1 <= ct -> bsum b + ct < 65536 ->
  arr_get b cu + 1 <= arr_get (st_upd mn b cu pr ct) cu.
Proof.
  intros mn b cu pr ct L NN Hcu Hpr Hct Hs.
  pose proof (bsum_ge b cu NN ltac:(lia)) as G. pose proof (NN cu ltac:(lia)) as G0.
  unfold st_upd. destruct (Z.ltb_spec ct mn).
  - rewrite arr_get_set_same by lia. rewrite wrap16_id by lia. lia.
  - replace (negb (cu =? 0)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
    replace (negb (cu =? pr)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
    unfold REP_3_6. rewrite arr_get_set_other by lia. rewrite arr_get_set_same by lia. rewrite wrap16_id by lia. lia.
Qed.

Lemma em_fold_mono : forall (s : deflate_state) f lens mc n p q c mx mn b,
  arr_len b = 39 -> bnn b -> 0 <= c -> 0 <= n -> (mn = 3 \/ mn = 4) ->
  (forall i, 0 <= i <= mc -> 0 <= lens i <= 15) -> (n <= mc -> q = lens n) ->
  bsum b + c + (mc + 1 - n) < 65536 ->
  forall j, arr_get b j <= arr_get (fold_left em_upd (emits f lens mc n p q c mx mn) b) j.
Proof.
  intros s f lens mc n p q c mx mn b L NN Hc Hn Hmn HL Hq Hs j.
  destruct (emits_bits s f lens mc n p q c mx mn b L NN Hc Hn Hmn HL Hq Hs) as (_ & _ & _ & _ & M). apply M.
Qed.

Lemma emits_hit : forall (s : deflate_state) f lens mc n p q c mx mn b,
  arr_len b = 39 -> bnn b -> 0 <= c -> 0 <= n <= mc -> (mn = 3 \/ mn = 4) ->
  (forall i, 0 <= i <= mc -> 0 <= lens i <= 15) -> q = lens n -> lens (mc + 1) = 65535 ->
  bsum b + c + (mc + 1 - n) < 65536 -> (Z.to_nat (mc + 1 - n) <= f)%nat ->
  p <= 0 -> (q <> 0 \/ exists n', n < n' <= mc /\ lens n' <> 0) ->
  exists y, 1 <= y <= 15 /\ arr_get b y + 1 <= arr_get (fold_left em_upd (emits f lens mc n p q c mx mn) b) y.
Proof.
  intros s. induction f as [|f IH]; intros lens mc n p q c mx mn b L NN Hc Hn Hmn HL Hq HG Hs Hf Hp Hnz; [exfalso; lia|].
  cbn [emits]. replace (n <=? mc) with true by (symmetry; apply Z.leb_le; lia). cbv zeta.
  pose proof (HL n ltac:(lia)) as HLn.
  destruct (Sumbool.sumbool_of_bool ((c + 1 <? mx) && (q =? lens (n + 1)))) as [CC|CC]; rewrite CC.
  -
    apply andb_prop in CC. destruct CC as [_ C2]. apply Z.eqb_eq in C2.
    assert (Hn1 : n + 1 <= mc) by (destruct (Z.eq_dec n mc) as [->|]; [rewrite HG in C2; subst q; lia | lia]).
    apply (IH lens mc (n + 1) p (lens (n + 1)) (c + 1) mx mn b L NN ltac:(lia) ltac:(lia) Hmn HL eq_refl HG ltac:(lia) ltac:(lia) Hp).
    destruct Hnz as [Hnz|(n' & Hn' & Hz')]; [left; congruence|].
    destruct (Z.eq_dec n' (n + 1)) as [->|]; [left; exact Hz' | right; exists n'; split; [lia | exact Hz']].
  - destruct (tree_counts q (lens (n + 1))) as [mx' mn'] eqn:TC.
    pose proof (tree_counts_range _ _ _ _ TC) as [_ Hmn'].
    cbn [fold_left]. change (em_upd b (mn, q, p, c + 1)) with (st_upd mn b q p (c + 1)).
    pose proof (st_upd_ok mn b q p (c + 1) L NN ltac:(subst q; lia) Hmn ltac:(lia) ltac:(lia)) as (L1 & NN1 & S1 & M1).
    destruct (Z.eq_dec q 0) as [Eq0|Eq0].
    +
      destruct Hnz as [Hnz|(n' & Hn' & Hz')]; [exfalso; exact (Hnz Eq0)|].
      assert (Hn1 : n + 1 <= mc) by lia.
      destruct (IH lens mc (n + 1) q (lens (n + 1)) 0 mx' mn' (st_upd mn b q p (c + 1)) L1 NN1 ltac:(lia) ltac:(lia) Hmn' HL eq_refl HG
                   ltac:(lia) ltac:(lia) ltac:(lia)
                   ltac:(destruct (Z.eq_dec n' (n + 1)) as [->|]; [left; exact Hz' | right; exists n'; split; [lia | exact Hz']]))
        as (y & Hy & Hhit).
      exists y. split; [exact Hy|]. specialize (M1 y). lia.
    +
      exists q. split; [subst q; lia|].
      pose proof (st_upd_hit mn b q p (c + 1) L NN ltac:(subst q; lia) Hp ltac:(lia) ltac:(lia)) as HIT.
      pose proof (em_fold_mono s f lens mc (n + 1) q (lens (n + 1)) 0 mx' mn' (st_upd mn b q p (c + 1)) L1 NN1 ltac:(lia) ltac:(lia) Hmn' HL
                    ltac:(intros; reflexivity) ltac:(lia) q) as M2.
      lia.
Qed.

Lemma scan_tree_bl : forall s t mc, 0 <= mc -> mc + 1 < arr_len (tree_dl s t) ->
  ds_bl_tree_fc (scan_tree s t mc) = fold_left em_upd (scan_E s t mc) (ds_bl_tree_fc s)
  /\ (forall t', t' <> TB -> tree_fc (scan_tree s t mc) t' = tree_fc s t').
Proof.
  intros s t mc Hmc Hlen. unfold scan_tree, scan_E. set (s1 := set_Len s t (mc + 1) 65535).
  assert (B1 : ds_bl_tree_fc s1 = ds_bl_tree_fc s) by (subst s1; unfold set_Len, set_Dad; destruct t; reflexivity).
  assert (L0 : Len s t 0 = Len s1 t 0).
  { subst s1. rewrite Len_set_Len by lia. replace (mc + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  rewrite L0.
  assert (SE : forall f n p q c mx mn, scan_tree_loop f s1 t mc n p q c mx mn
             = set_bl_tree_fc s1 (fold_left em_upd (emits f (Len s1 t) mc n p q c mx mn) (ds_bl_tree_fc s))).
  { intros. rewrite <- B1, <- scan_emits, sbf_self. reflexivity. }
  destruct (Len s1 t 0 =? 0); rewrite SE, sbf_get;
    (split; [reflexivity | intros t' Ht'; rewrite sbf_tree_fc by exact Ht'; subst s1; apply tree_fc_set_Len]).
Qed.

Lemma scan_tree_hit : forall s t mc,
  0 <= mc -> mc + 1 < arr_len (tree_dl s t) -> tree_lens s -> bnn (ds_bl_tree_fc s) ->
  (forall i, 0 <= i <= mc -> 0 <= Len s t i <= 15) -> bsum (ds_bl_tree_fc s) + (mc + 1) < 65536 ->
  (exists n, 0 <= n <= mc /\ Len s t n <> 0) ->
  exists y, 1 <= y <= 15 /\ 1 <= arr_get (ds_bl_tree_fc (scan_tree s t mc)) y.
Proof.
  intros s t mc Hmc Hlen TL NN L15 BS (n0 & Hn0 & Hz0).
  destruct (scan_tree_bl s t mc Hmc Hlen) as [E _]. rewrite E. unfold scan_E.
  set (s1 := set_Len s t (mc + 1) 65535).
  assert (LB : arr_len (ds_bl_tree_fc s) = 39) by (unfold tree_lens in TL; tauto).
  assert (L1 : forall i, 0 <= i <= mc -> Len s1 t i = Len s t i).
  { intros i Hi. subst s1. rewrite Len_set_Len by lia. destruct (Z.eqb_spec (mc + 1) i); [lia | reflexivity]. }
  assert (LG : Len s1 t (mc + 1) = 65535).
  { subst s1. rewrite Len_set_Len by lia. rewrite Z.eqb_refl. reflexivity. }
  assert (L15' : forall i, 0 <= i <= mc -> 0 <= Len s1 t i <= 15) by (intros i Hi; rewrite L1 by lia; apply L15; lia).
  assert (Hmn : (if Len s1 t 0 =? 0 then 3 else 4) = 3 \/ (if Len s1 t 0 =? 0 then 3 else 4) = 4) by (destruct (Len s1 t 0 =? 0); lia).
  assert (Hnz : Len s1 t 0 <> 0 \/ exists n', 0 < n' <= mc /\ Len s1 t n' <> 0).
  { destruct (Z.eq_dec n0 0) as [->|]; [left; rewrite L1 by lia; exact Hz0 | right; exists n0; split; [lia|]; rewrite L1 by lia; exact Hz0]. }
  destruct (emits_hit s (Z.to_nat (mc + 1)) (Len s1 t) mc 0 (-1) (Len s1 t 0) 0 (if Len s1 t 0 =? 0 then 138 else 7) (if Len s1 t 0 =? 0 then 3 else 4) (ds_bl_tree_fc s) LB NN ltac:(lia) ltac:(lia) Hmn
              L15' eq_refl LG ltac:(lia) ltac:(lia) ltac:(lia) Hnz) as (y & Hy & Hhit).
  exists y. split; [exact Hy|]. pose proof (NN y ltac:(lia)). lia.
Qed.

Lemma scan_tree_mono : forall s t mc,
  -1 <= mc -> mc + 1 < arr_len (tree_dl s t) -> tree_lens s -> bnn (ds_bl_tree_fc s) ->
  (forall i, 0 <= i <= mc -> 0 <= Len s t i <= 15) -> bsum (ds_bl_tree_fc s) + (mc + 1) < 65536 ->
  forall j, arr_get (ds_bl_tree_fc s) j <= arr_get (ds_bl_tree_fc (scan_tree s t mc)) j.
Proof.
  intros s t mc Hmc Hlen TL NN L15 BS j.
  destruct (scan_sum s t mc TL NN Hmc Hlen L15 BS) as (b' & E & _ & _ & _ & M). rewrite E, sbf_get. apply M.
Qed.

Lemma bblt_lt3 : forall f X m, 2 <= m -> build_bl_tree_loop f X m < 3 ->
  (Z.to_nat (m - 2) <= f)%nat -> forall k, 3 <= k <= m -> Len X TB (arr_get bl_order_a k) = 0.
Proof.
  induction f as [|f IH]; intros X m Hm Hr Hf k Hk; [exfalso; lia|].
  cbn [build_bl_tree_loop] in Hr.
  destruct (Z.leb_spec 3 m); [|exfalso; lia].
  destruct (Z.eqb_spec (Len X TB (arr_get bl_order_a m)) 0) as [E|E]; cbn [negb] in Hr; [|exfalso; lia].
  destruct (Z.eq_dec k m) as [->|]; [exact E|].
  apply (IH X (m - 1)); lia.
Qed.

Lemma bl_order_covers : forall y, 0 <= y <= 15 -> exists k, 3 <= k <= 18 /\ arr_get bl_order_a k = y.
Proof.
  intros y Hy.
  destruct (Z.eq_dec y 0) as [->|]; [exists 3; split; [lia | vm_compute; reflexivity]|].
  destruct (Z.eq_dec y 1) as [->|]; [exists 17; split; [lia | vm_compute; reflexivity]|].
  destruct (Z.eq_dec y 2) as [->|]; [exists 15; split; [lia | vm_compute; reflexivity]|].
  destruct (Z.eq_dec y 3) as [->|]; [exists 13; split; [lia | vm_compute; reflexivity]|].
  destruct (Z.eq_dec y 4) as [->|]; [exists 11; split; [lia | vm_compute; reflexivity]|].
  destruct (Z.eq_dec y 5) as [->|]; [exists 9; split; [lia | vm_compute; reflexivity]|].
  destruct (Z.eq_dec y 6) as [->|]; [exists 7; split; [lia | vm_compute; reflexivity]|].
  destruct (Z.eq_dec y 7) as [->|]; [exists 5; split; [lia | vm_compute; reflexivity]|].
  destruct (Z.eq_dec y 8) as [->|]; [exists 4; split; [lia | vm_compute; reflexivity]|].
  destruct (Z.eq_dec y 9) as [->|]; [exists 6; split; [lia | vm_compute; reflexivity]|].
  destruct (Z.eq_dec y 10) as [->|]; [exists 8; split; [lia | vm_compute; reflexivity]|].
  destruct (Z.eq_dec y 11) as [->|]; [exists 10; split; [lia | vm_compute; reflexivity]|].
  destruct (Z.eq_dec y 12) as [->|]; [exists 12; split; [lia | vm_compute; reflexivity]|].
  destruct (Z.eq_dec y 13) as [->|]; [exists 14; split; [lia | vm_compute; reflexivity]|].
  destruct (Z.eq_dec y 14) as [->|]; [exists 16; split; [lia | vm_compute; reflexivity]|].
  destruct (Z.eq_dec y 15) as [->|]; [exists 18; split; [lia | vm_compute; reflexivity]|].
  exfalso; lia.
Qed.

Lemma fmb_ge3 : forall X y, 0 <= y <= 15 -> Len X TB y <> 0 -> 3 <= build_bl_tree_loop 17 X 18.
Proof.
  intros X y Hy Hnz. destruct (Z_lt_le_dec (build_bl_tree_loop 17 X 18) 3) as [LT|GE]; [|exact GE].
  exfalso. destruct (bl_order_covers y Hy) as (k & Hk & Ek).
  pose proof (bblt_lt3 17 X 18 ltac:(lia) LT ltac:(cbn; lia) k Hk) as Z0. rewrite Ek in Z0. exact (Hnz Z0).
Qed.


Lemma zcount_le_len : forall {A} (f : A -> bool) l, zcount f l <= Z.of_nat (length l).
Proof. intros A f l. unfold zcount. induction l as [|x l IH]; cbn; [lia|]. destruct (f x); cbn; lia. Qed.
Lemma zcount_none : forall {A} (f : A -> bool) l, (forall x, In x l -> f x = false) -> zcount f l = 0.
Proof.
  intros A f l H. unfold zcount. induction l as [|x l IH]; cbn; [reflexivity|].
  rewrite (H x ltac:(left; reflexivity)). apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

Section Extra.
  Variable syms : list (Z * Z).
  Variable s : deflate_state.
  Variable buf : option Z.
  Variables len last : Z.
  Hypothesis FB : FBS syms s buf len last.
  Variables fY1 fY2 fY3 fY4 fY5 fY6 : deflate_state.
  Hypothesis EfY1 : fY1 = build_tree (fs0 s) TL.
  Hypothesis EfY2 : fY2 = build_tree fY1 TD.
  Hypothesis EfY3 : fY3 = scan_tree fY2 TL (ds_l_max_code fY2).
  Hypothesis EfY4 : fY4 = scan_tree fY3 TD (ds_d_max_code fY3).
  Hypothesis EfY5 : fY5 = build_tree fY4 TB.
  Hypothesis EfY6 : fY6 = set_opt_len fY5 (wrap64 (ds_opt_len fY5 + 3 * (fmb fY5 + 1) + 5 + 5 + 4)).

  Let nS : Z := Z.of_nat (length syms).

  Lemma freq_l_15 : forall j, 0 <= j < 286 -> Freq s TL j < 2 ^ 15.
  Proof.
    intros j Hj. pose proof (L_range syms s buf len last FB) as [LR NR].
    rewrite (fbs_freq_l _ _ _ _ _ FB j) by (unfold L_CODES; lia).
    pose proof (zcount_le_len (fun dl => sym_lcode dl =? j) syms) as ZC.
    change (2 ^ 15) with 32768. unfold nS, OverlayFlush.nS, OverlayFlush.LS in *.
    destruct (Z.eqb_spec j END_BLOCK) as [Ej|Ej]; [|lia].
    rewrite zcount_none; [lia|].
    intros x Hx. pose proof (fbs_syms_valid _ _ _ _ _ FB) as V. rewrite Forall_forall in V. specialize (V x Hx).
    destruct x as [d lc]. unfold sym_valid in V. unfold sym_lcode. apply Z.eqb_neq. unfold END_BLOCK in Ej. subst j.
    destruct (Z.eqb_spec d 0); [lia|]. pose proof (TreesTab.length_code_bound lc). unfold LITERALS. lia.
  Qed.

  Lemma freq_d_15 : forall j, 0 <= j < 30 -> Freq s TD j < 2 ^ 15.
  Proof.
    intros j Hj. pose proof (L_range syms s buf len last FB) as [LR NR].
    rewrite (fbs_freq_d _ _ _ _ _ FB j) by (unfold D_CODES; lia).
    pose proof (zcount_le_len (fun dl => match sym_dcode dl with Some j' => j' =? j | None => false end) syms) as ZC.
    change (2 ^ 15) with 32768. unfold OverlayFlush.nS, OverlayFlush.LS in *. lia.
  Qed.

  Theorem extra_facts :
    256 <= ds_l_max_code fY6 /\ 3 <= fmb fY5
    /\ (forall i, 0 <= i < 286 -> 0 <= arr_get (tree_fc fY6 TL) i < 2 ^ 15)
    /\ (forall i, 0 <= i < 30 -> 0 <= arr_get (tree_fc fY6 TD) i < 2 ^ 15)
    /\ (forall c, 0 <= c < 19 -> 0 <= arr_get (tree_fc fY6 TB) c < 2 ^ 15).
  Proof.
    destruct (flush_facts syms s buf len last FB fY1 fY2 fY3 fY4 fY5 fY6 EfY1 EfY2 EfY3 EfY4 EfY5 EfY6)
      as (LL & LzL & LD & LzD & LB & LzB & b4 & FR).
    pose proof (fs0_flush_pre syms s buf len last FB) as PRE.
    pose proof (fs0_fields syms s buf len last FB) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fbl & _).
    pose proof (bt_U_facts s TL) as (_ & RGL & _ & _ & INL & _).
    pose proof (bt_U_facts s TD) as (_ & RGD & _ & _ & IND & _).
    pose proof (bt_U_facts fY4 TB) as (_ & RGB & _ & _ & INB & _).
    pose proof (ff_S256 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as S256.
    pose proof (ff_RL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as RL. pose proof (ff_RD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as RD.
    pose proof (ff_MCL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as MCL. pose proof (ff_MCL2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as MCL2.
    pose proof (ff_MCD3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as MCD3.
    pose proof (ff_TL2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as TL2. pose proof (ff_TL3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as TL3.
    pose proof (ff_TL4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as TL4.
    pose proof (ff_BL2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as BL2. pose proof (ff_BL4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as BL4.
    pose proof (ff_NN4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as NN4. pose proof (ff_BS316 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as BS316.
    pose proof (ff_Lb4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as Lb4.
    pose proof (ff_LENS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as LENS. pose proof (ff_ZL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as ZL.
    pose proof (ff_LEND _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as LEND. pose proof (ff_ZD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as ZD.
    pose proof (ff_LENB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as LENB.
    pose proof (ff_LQ2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as LQ2. pose proof (ff_LQ3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as LQ3.
    pose proof (ff_EY3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as EY3. pose proof (ff_EY4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as EY4.
    pose proof (ff_P1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as P1. pose proof (ff_P2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as P2.
    pose proof (ff_P5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as P5.
    pose proof (ff_B1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as B1. pose proof (ff_B2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as B2.
    pose proof (ff_B5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as B5.
    pose proof (ff_FC6L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as FC6L. pose proof (ff_FC6D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as FC6D.
    pose proof (ff_FC1D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as FC1D.
    assert (M256 : 256 <= bt_mc s TL) by (pose proof (RGL 256 S256); lia).
    destruct (bt_same s (fs0 s) TL (fs0_tree_fc syms s buf len last FB TL)) as (UL & _ & MCLq & _).
    destruct (bt_same s fY1 TD ltac:(rewrite FC1D; reflexivity)) as (UD1 & _ & MCD1 & _).
    pose proof (tree_lens_dl fY2 TL TL2) as DL2. pose proof (tree_lens_dl fY3 TD TL3) as DL3. cbn [tsize] in DL2, DL3.
    assert (L2 : forall i, 0 <= i <= bt_mc s TL -> Len fY2 TL i = Len fY5 TL i).
    { intros i Hi. rewrite LQ2 by lia. rewrite Len_set_Len by lia. destruct (Z.eqb_spec (bt_mc s TL + 1) i); [lia | reflexivity]. }
    assert (L3 : forall i, 0 <= i <= bt_mc s TD -> Len fY3 TD i = Len fY5 TD i).
    { intros i Hi. rewrite LQ3 by lia. rewrite Len_set_Len by lia. destruct (Z.eqb_spec (bt_mc s TD + 1) i); [lia | reflexivity]. }
    assert (L2r : forall i, 0 <= i <= bt_mc s TL -> 0 <= Len fY2 TL i <= 15).
    { intros i Hi. rewrite L2 by exact Hi. destruct (in_dec Z.eq_dec i (bt_U s TL)) as [IN|NI].
      - destruct (LENS i IN) as [-> R]. lia.
      - rewrite (ZL i Hi NI). lia. }
    assert (L3r : forall i, 0 <= i <= bt_mc s TD -> 0 <= Len fY3 TD i <= 15).
    { intros i Hi. rewrite L3 by exact Hi. destruct (in_dec Z.eq_dec i (bt_U s TD)) as [IN|NI].
      - destruct (LEND i IN) as [-> R]. lia.
      - rewrite (ZD i Hi NI). lia. }
    pose proof (fp_fb _ PRE) as NN0. rewrite Fbl in NN0.
    pose proof (fp_totb _ PRE) as TB0. rewrite Fbl in TB0.
    assert (NN2 : bnn (ds_bl_tree_fc fY2)) by (rewrite BL2; exact NN0).
    assert (BS2 : bsum (ds_bl_tree_fc fY2) + (bt_mc s TL + 1) < 65536) by (rewrite BL2; lia).
    destruct (scan_tree_hit fY2 TL (bt_mc s TL) ltac:(lia) ltac:(rewrite DL2; lia) TL2 NN2 L2r BS2
                ltac:(exists 256; split; [lia|]; rewrite L2 by lia; destruct (LENS 256 S256) as [-> R]; lia))
      as (y & Hy & Hy3).
    rewrite <- EY3 in Hy3.
    destruct (scan_sum fY2 TL (bt_mc s TL) TL2 NN2 ltac:(lia) ltac:(rewrite DL2; lia) L2r BS2) as (b3 & E3 & Lb3 & NN3 & BS3 & _).
    rewrite <- EY3 in E3.
    assert (BL3 : ds_bl_tree_fc fY3 = b3) by (rewrite E3; apply sbf_get).
    pose proof (scan_tree_mono fY3 TD (bt_mc s TD) ltac:(lia) ltac:(rewrite DL3; lia) TL3 ltac:(rewrite BL3; exact NN3) L3r
                  ltac:(rewrite BL3; rewrite BL2 in BS3; lia) y) as Hy4.
    rewrite <- EY4, BL4 in Hy4.
    assert (INy : In y (bt_U fY4 TB)).
    { apply (fun H => proj1 (INB y ltac:(cbn; unfold BL_CODES; lia) H)). unfold Freq. cbn [tree_fc]. rewrite BL4. lia. }
    destruct (LENB y INy) as [Ly5 RLy].
    split; [rewrite EfY6, l_max_code_set_opt_len, MCL; exact M256|].
    split; [apply (fmb_ge3 fY5 y); [lia | rewrite Ly5; lia]|].
    pose proof (tree_lens_dl fY2 TL TL2) as _x.
    assert (FC21 : tree_fc fY2 TL = tree_fc fY1 TL) by (rewrite EfY2; apply build_tree_fc_other; [exact P2 | discriminate]).
    destruct (scan_tree_bl fY2 TL (bt_mc s TL) ltac:(lia) ltac:(rewrite DL2; lia)) as [_ O3]. rewrite <- EY3 in O3.
    destruct (scan_tree_bl fY3 TD (bt_mc s TD) ltac:(lia) ltac:(rewrite DL3; lia)) as [_ O4]. rewrite <- EY4 in O4.
    assert (FC5L : tree_fc fY5 TL = tree_fc fY4 TL) by (rewrite EfY5; apply build_tree_fc_other; [exact P5 | discriminate]).
    assert (FC5D : tree_fc fY5 TD = tree_fc fY4 TD) by (rewrite EfY5; apply build_tree_fc_other; [exact P5 | discriminate]).
    split.
    { intros i Hi. rewrite FC6L, FC5L, (O4 TL ltac:(discriminate)), (O3 TL ltac:(discriminate)), FC21, EfY1.
      apply build_tree_fc15; [exact P1 | | | cbn; unfold L_CODES; lia].
      - intros j Hj. unfold Freq. rewrite (fs0_tree_fc syms s buf len last FB TL). apply freq_l_15. cbn in Hj; unfold L_CODES in Hj; lia.
      - intros j Hj Hnz. rewrite <- EfY1 in Hnz |- *. rewrite MCLq in Hj.
        pose proof B1 as (_ & _ & _ & _ & _ & _ & LZ1 & Z1 & _). rewrite UL in LZ1, Z1.
        destruct (in_dec Z.eq_dec j (bt_U s TL)) as [IN|NI].
        + destruct (LZ1 j IN) as [-> R]. cbn in R. unfold MAX_BITS in R. lia.
        + exfalso. apply Hnz. apply Z1; [cbn; unfold L_CODES; lia | exact NI]. }
    split.
    { intros i Hi. rewrite FC6D, FC5D, (O4 TD ltac:(discriminate)), (O3 TD ltac:(discriminate)), EfY2.
      apply build_tree_fc15; [exact P2 | | | cbn; unfold D_CODES; lia].
      - intros j Hj. unfold Freq. rewrite FC1D. apply freq_d_15. cbn in Hj; unfold D_CODES in Hj; lia.
      - intros j Hj Hnz. rewrite <- EfY2 in Hnz |- *. rewrite MCD1 in Hj.
        pose proof B2 as (_ & _ & _ & _ & _ & _ & LZ2 & Z2 & _). rewrite UD1 in LZ2, Z2.
        destruct (in_dec Z.eq_dec j (bt_U s TD)) as [IN|NI].
        + destruct (LZ2 j IN) as [-> R]. cbn in R. unfold MAX_BITS in R. lia.
        + exfalso. apply Hnz. apply Z2; [cbn; unfold D_CODES; lia | exact NI]. }
    { intros c Hc. rewrite EfY6, tree_fc_set_opt_len, EfY5.
      apply build_tree_fc15; [exact P5 | | | cbn; unfold BL_CODES; lia].
      - intros j Hj. unfold Freq. cbn [tree_fc]. rewrite BL4. cbn in Hj; unfold BL_CODES in Hj.
        pose proof (bsum_ge b4 j NN4 ltac:(lia)). change (2 ^ 15) with 32768. lia.
      - intros j Hj Hnz. rewrite <- EfY5 in Hnz |- *.
        pose proof B5 as (_ & _ & _ & _ & _ & _ & LZ5 & Z5 & _).
        destruct (in_dec Z.eq_dec j (bt_U fY4 TB)) as [IN|NI].
        + destruct (LZ5 j IN) as [-> R]. cbn in R. unfold MAX_BL_BITS in R. lia.
        + exfalso. apply Hnz. pose proof (RGB _ (proj1 (proj2 (proj2 (bt_U_facts fY4 TB))))) as MX. apply Z5; [cbn; unfold BL_CODES; cbn in MX; unfold BL_CODES in MX; lia | exact NI]. }
  Qed.
End Extra.


End FXG.
Ltac name_let x E rhs := intro x; generalize (@eq_refl _ x : x = rhs); clearbody x; revert x; intros x E.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Theorem FB6_FBSAFE6u : forall s buf len last, FB6 s buf len last -> FBSAFE6u s buf len last.
Proof.
  intros s buf len last HF. pose proof HF as (FS & _ & _ & _ & _ & _ & _ & (syms & FB)).
  split; [exact FS|]. cbv beta delta [fb_extra6u]. intros _.
  name_let s0 Es0 (fs0 s). subst s0.
  name_let X1 E1 (build_tree (fs0 s) TL).
  name_let X2 E2 (build_tree X1 TD).
  name_let mcl Emcl (ds_l_max_code X2). subst mcl.
  name_let X3 E3 (scan_tree X2 TL (ds_l_max_code X2)).
  name_let mcd Emcd (ds_d_max_code X3). subst mcd.
  name_let X4 E4 (scan_tree X3 TD (ds_d_max_code X3)).
  name_let X5 E5 (build_tree X4 TB).
  name_let mb Emb (fmb X5). subst mb.
  name_let X6 E6 (set_opt_len X5 (wrap64 (ds_opt_len X5 + 3 * (fmb X5 + 1) + 5 + 5 + 4))).
  exact (extra_facts syms s buf len last FB X1 X2 X3 X4 X5 X6 E1 E2 E3 E4 E5 E6).
Qed.

Theorem tr_flush_block_run6u_FB6 : tr_flush_block_run6u FB6.
Proof.
  unfold tr_flush_block_run6u. intros F mem0 mem S p PBL ds ra regs sp buf bufp len last MS MC HL HFS Hret HB HBI HRC HS.
  exact (tr_flush_block_run6u_ok F mem0 mem S p PBL ds ra regs sp buf bufp len last MS MC HL HFS Hret HB HBI HRC (FB6_FBSAFE6u _ _ _ _ HS)).
Qed.
End FXG.
