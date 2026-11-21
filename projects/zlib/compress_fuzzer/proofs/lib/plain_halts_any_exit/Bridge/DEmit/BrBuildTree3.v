(** * Bridge.DEmit.BrBuildTree3 — pair D27: [gen_bitlen], S5 vs RT.

    Three passes on both sides:
    - pass 1 (S5 [gen_bitlen_loop1], RT [gb_pass1]): walk the heap array
      top-down, a node's length is its parent's plus one, capped at
      [max_length] (counting the overflows);
    - pass 2 (S5 [gen_bitlen_loop2], RT [gb_adjust]): move overflowed
      leaves down; both search [bl_count] for the deepest populated length
      below [max_length] (S5 in 15 steps, RT in 16), and S5's own
      [gb2_ok] says the search succeeds, so both find the same length;
    - pass 3 (S5's nested [gen_bitlen_loop3]/[loop3i], RT's one flattened
      [gb_pass2]): reassign lengths in heap order, S5's inner loop matched
      by a run of RT steps ([pass3i_rel]).

    S5's per-step safety facts come from [GenBitlenModel.bt_safe]
    ([gb1_ok], [gb2_ok], [gb3_ok]); they keep every array index inside the
    related ranges. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees TreeModel GenBitlenModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require BrBits.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitDefs DTreeDefs BrBuildTree0 BrBuildTree1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require BrTally.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module GBM := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.GenBitlenModel.

(* ------------------------------------------------------------------------- *)
(* 1.  Tables and constants                                                  *)
(* ------------------------------------------------------------------------- *)

Lemma ml_agree : forall t, RT.sd_max_length (tk_of t) = DS.sd_max_length t.
Proof. intros []; reflexivity. Qed.
Lemma base_agree : forall t, RT.sd_extra_base (tk_of t) = DS.sd_extra_base t.
Proof. intros []; reflexivity. Qed.
Lemma ml_range : forall t, 7 <= DS.sd_max_length t <= 15.
Proof. intros []; cbn; unfold DS.MAX_BITS, DS.MAX_BL_BITS; lia. Qed.
Lemma base_range : forall t, 0 <= DS.sd_extra_base t.
Proof. intros []; cbn; unfold DS.LITERALS; lia. Qed.

Lemma xbits_agree : forall t n, 0 <= n ->
  GBM.xbits t n = (if DS.sd_extra_base t <=? n then RT.sd_extra (tk_of t) (n - DS.sd_extra_base t) else 0).
Proof.
  intros t n Hn. unfold GBM.xbits. destruct (Z.leb_spec (DS.sd_extra_base t) n); [|reflexivity].
  destruct t; cbn [DS.sd_extra_bits RT.sd_extra tk_of]; cbn [RT.TK_L RT.TK_D RT.TK_BL Z.eqb];
    unfold DS.extra_lbits_a, DS.extra_dbits_a, DS.extra_blbits_a, RT.extra_lbits, RT.extra_dbits, RT.extra_blbits;
    rewrite BrTally.arr_of_list_zlist by lia; reflexivity.
Qed.

Lemma stree_agree_n : forall t node, 0 <= node ->
  match RT.sd_stree (tk_of t) with
  | None => DS.stree_has t = false
  | Some st => DS.stree_has t = true /\ DS.stree_Len t node = RT.t_len st node
  end.
Proof.
  intros [] node Hn; cbn [RT.sd_stree tk_of DS.stree_has DS.stree_Len]; try reflexivity;
    (split; [reflexivity|]); unfold RT.t_len; cbn [RT.tr_dl RT.static_ltree RT.static_dtree];
    unfold DS.static_ltree_dl, DS.static_dtree_dl; rewrite BrTally.arr_of_list_zlist by lia; reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  Pass 1                                                                *)
(* ------------------------------------------------------------------------- *)

Definition dlr (t : DS.tree_id) (DL : arr) : Prop := forall i, 0 <= i < TM.tsize t -> 0 <= arr_get DL i < 65536.
Definition bcr (BC : arr) : Prop := forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536.

Lemma dlr_set : forall t DL i v, dlr t DL -> dlr t (arr_set DL i (wrap16 v)).
Proof.
  intros t DL i v H j Hj. rewrite arr_get_set. destruct (_ && _); [pose proof (wrap16_range v); lia | apply H; exact Hj].
Qed.
Lemma bcr_set : forall BC i v, bcr BC -> bcr (arr_set BC i (wrap16 v)).
Proof.
  intros BC i v H j Hj. rewrite arr_get_set. destruct (_ && _); [pose proof (wrap16_range v); lia | apply H; exact Hj].
Qed.

Ltac csplit := repeat match goal with |- _ /\ _ => split end.

Ltac p1_close IH :=
  match goal with |- context [RT.gb_pass1 ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j ?k ?l ?m ?n] =>
    destruct (RT.gb_pass1 a b c d e f g h i j k l m n) as [[[[?T' ?blc'] ?ol'] ?sl'] ?ov'] end;
  let DL' := fresh "DL'" in let BC' := fresh "BC'" in let OL' := fresh "OL'" in let SL' := fresh "SL'" in
  destruct IH as (DL' & BC' & OL' & SL' & ? & ? & ? & ? & ? & ? & ? & ?);
  exists DL', BC', OL', SL'; csplit; first [assumption | lia].

Lemma pass1_rel : forall f g s0 t FC DL HP HL HM DP BC OL SL MC T hp dep blc h ovf,
  brel t FC DL HP DP BC T hp dep blc -> 0 <= h <= 573 -> -1 <= MC < DS.sd_elems t ->
  (forall h', h <= h' < 573 -> 0 <= arr_get HP h' < TM.tsize t) ->
  dlr t DL -> bcr BC -> 0 <= ovf ->
  GBM.gb1_ok t MC f (bt_upd s0 t FC DL HP HL HM DP BC OL SL MC) h ovf ->
  (Z.to_nat (573 - h) <= f)%nat -> (Z.to_nat (573 - h) < g)%nat ->
  let r := DT.gen_bitlen_loop1 f (bt_upd s0 t FC DL HP HL HM DP BC OL SL MC) t MC
             (DS.sd_extra_base t) (DS.sd_max_length t) h ovf in
  match RT.gb_pass1 g (tk_of t) hp MC (DS.sd_max_length t) (DS.sd_extra_base t)
                    (RT.sd_extra (tk_of t)) (RT.sd_stree (tk_of t)) h T blc OL SL ovf with
  | (T', blc', ol', sl', ov') =>
    exists DL' BC' OL' SL', fst r = bt_upd s0 t FC DL' HP HL HM DP BC' OL' SL' MC /\ snd r = ov'
      /\ brel t FC DL' HP DP BC' T' hp dep blc' /\ OL' = ol' /\ SL' = sl' /\ ovf <= ov' <= ovf + (573 - h)
      /\ dlr t DL' /\ bcr BC'
  end.
Proof.
  induction f as [|f IH]; intros g s0 t FC DL HP HL HM DP BC OL SL MC T hp dep blc h ovf
    H Hh HMC Hhp Hdl Hbc Hov Hok Hf Hg r; subst r;
    pose proof (tsize_le t) as Ht; pose proof (ml_range t) as Hml; destruct (elems_range t) as [HE Hts].
  - assert (h = 573) by lia. subst h.
    destruct g as [|g]; [lia|]. cbn [DT.gen_bitlen_loop1 RT.gb_pass1 fst snd]. change RT.HEAP_SIZE with 573.
    rewrite Z.leb_refl. exists DL, BC, OL, SL. csplit; first [assumption | reflexivity | lia].
  - destruct g as [|g]; [lia|].
    rewrite GBM.GL1_step. cbn [RT.gb_pass1]. change RT.HEAP_SIZE with 573. change DS.HEAP_SIZE with 573.
    destruct (Z.ltb_spec h 573) as [Hlt|Hge].
    2:{ assert (h = 573) by lia. subst h. rewrite Z.leb_refl. cbn [fst snd].
        exists DL, BC, OL, SL. csplit; first [assumption | reflexivity | lia]. }
    replace (573 <=? h) with false by (symmetry; apply Z.leb_gt; lia).
    cbn [GBM.gb1_ok] in Hok. change DS.HEAP_SIZE with 573 in Hok.
    replace (h <? 573) with true in Hok by (symmetry; apply Z.ltb_lt; lia).
    autorewrite with btupd in Hok.
    rewrite GBM.GB1_flat in Hok |- *. cbv zeta in Hok |- *.
    destruct Hok as [Hd Hok].
    rewrite <- (brel_hp_get _ _ _ _ _ _ _ _ _ _ h H) by lia.
    assert (Hn : 0 <= arr_get HP h < TM.tsize t) by (apply Hhp; lia).
    set (n := arr_get HP h) in *.
    unfold RT.t_dad, RT.t_len.
    rewrite <- (brel_dl_get _ _ _ _ _ _ _ _ _ _ n H) by lia.
    rewrite <- (brel_dl_get _ _ _ _ _ _ _ _ _ _ (arr_get DL n) H) by lia.
    assert (Hb0 : 1 <= arr_get DL (arr_get DL n) + 1) by (pose proof (Hdl (arr_get DL n) Hd); lia).
    set (bits0 := arr_get DL (arr_get DL n) + 1) in *.
    set (bits := if DS.sd_max_length t <? bits0 then DS.sd_max_length t else bits0) in *.
    set (ovf' := if DS.sd_max_length t <? bits0 then ovf + 1 else ovf) in *.
    assert (Hbits : 1 <= bits <= 15 /\ ovf <= ovf' <= ovf + 1)
      by (subst bits ovf'; destruct (Z.ltb_spec (DS.sd_max_length t) bits0); lia).
    assert (B1 : brel t FC (arr_set DL n (wrap16 bits)) HP DP BC (RT.t_setlen T n bits) hp dep blc)
      by (apply brel_dl_set; [exact H | lia]).
    destruct (Z.ltb_spec MC n) as [Cm|Cm].
    + specialize (IH g s0 t FC (arr_set DL n (wrap16 bits)) HP HL HM DP BC OL SL MC (RT.t_setlen T n bits) hp dep blc
                    (h + 1) ovf' B1 ltac:(lia) HMC ltac:(intros; apply Hhp; lia) (dlr_set _ _ _ _ Hdl) Hbc ltac:(lia) Hok
                    ltac:(lia) ltac:(lia)).
      cbv zeta in IH. p1_close IH.
    + unfold RT.t_freq. cbn [RT.tr_fc RT.t_setlen].
      rewrite <- (brel_fc_get _ _ _ _ _ _ _ _ _ _ n H) by lia.
      rewrite <- (brel_bc_get _ _ _ _ _ _ _ _ _ _ bits H) by lia.
      rewrite xbits_agree in Hok |- * by lia.
      set (xb := if DS.sd_extra_base t <=? n then RT.sd_extra (tk_of t) (n - DS.sd_extra_base t) else 0) in *.
      pose proof (stree_agree_n t n ltac:(lia)) as ST.
      set (SL' := if DS.stree_has t then wrap64 (SL + arr_get FC n * (DS.stree_Len t n + xb)) else SL) in *.
      set (sl' := match RT.sd_stree (tk_of t) with
                  | Some st => RT.u64 (SL + arr_get FC n * (RT.tr_dl st n + xb)) | None => SL end).
      assert (ESL : SL' = sl').
      { subst SL' sl'. destruct (RT.sd_stree (tk_of t)) as [st|];
          [destruct ST as [-> ->]; apply wrap64_u64 | rewrite ST; reflexivity]. }
      rewrite <- ESL. rewrite <- wrap64_u64.
      assert (B2 : brel t FC (arr_set DL n (wrap16 bits)) HP DP (arr_set BC bits (wrap16 (arr_get BC bits + 1)))
                     (RT.t_setlen T n bits) hp dep (Base.zset blc bits (Base.u16 (arr_get BC bits + 1))))
        by (apply brel_bc_set; [exact B1 | lia]).
      specialize (IH g s0 t FC (arr_set DL n (wrap16 bits)) HP HL HM DP (arr_set BC bits (wrap16 (arr_get BC bits + 1)))
                    (wrap64 (OL + arr_get FC n * (bits + xb))) SL' MC (RT.t_setlen T n bits) hp dep
                    (Base.zset blc bits (Base.u16 (arr_get BC bits + 1))) (h + 1) ovf' B2 ltac:(lia) HMC
                    ltac:(intros; apply Hhp; lia) (dlr_set _ _ _ _ Hdl) (bcr_set _ _ _ Hbc) ltac:(lia) Hok
                    ltac:(lia) ltac:(lia)).
      cbv zeta in IH. p1_close IH.
Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  Pass 2: the overflow adjustment                                       *)
(* ------------------------------------------------------------------------- *)

Lemma findbits_at : forall F (blc : Base.zarr) b r,
  r <= b -> (forall j, r < j <= b -> blc j = 0) -> blc r <> 0 -> (Z.to_nat (b - r) < F)%nat ->
  RT.gb_findbits F blc b = r.
Proof.
  induction F as [|F IH]; intros blc b r Hr Hz Hnz HF; [lia|].
  cbn [RT.gb_findbits]. destruct (Z.eq_dec b r) as [->|Ne].
  - replace (blc r =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hnz). reflexivity.
  - rewrite (Hz b) by lia. rewrite Z.eqb_refl. apply IH; [lia | intros; apply Hz; lia | exact Hnz | lia].
Qed.

(** S5's search ([gen_bitlen_find], [max_length] steps) and RT's
    ([gb_findbits], 16 steps) agree once S5's succeeds. *)
Lemma find_agree : forall s0 t FC DL HP HL HM DP BC OL SL MC T hp dep blc ML,
  brel t FC DL HP DP BC T hp dep blc -> 1 <= ML <= 15 ->
  0 <= DT.gen_bitlen_find (Z.to_nat ML) (bt_upd s0 t FC DL HP HL HM DP BC OL SL MC) (ML - 1) ->
  RT.gb_findbits (Z.to_nat RT.MAX_BITS + 1) blc (ML - 1)
  = DT.gen_bitlen_find (Z.to_nat ML) (bt_upd s0 t FC DL HP HL HM DP BC OL SL MC) (ML - 1)
  /\ 0 <= DT.gen_bitlen_find (Z.to_nat ML) (bt_upd s0 t FC DL HP HL HM DP BC OL SL MC) (ML - 1) <= ML - 1.
Proof.
  intros s0 t FC DL HP HL HM DP BC OL SL MC T hp dep blc ML H HML Hr.
  destruct (GBM.find_spec _ _ _ Hr) as (A & B & C).
  set (r := DT.gen_bitlen_find (Z.to_nat ML) (bt_upd s0 t FC DL HP HL HM DP BC OL SL MC) (ML - 1)) in *.
  assert (Cr : DT.bl_count_get (bt_upd s0 t FC DL HP HL HM DP BC OL SL MC) r <> 0) by (destruct C; [lia | exact H0]).
  autorewrite with btupd in B, Cr.
  split; [|lia].
  apply findbits_at; [lia | | | change RT.MAX_BITS with 15; lia].
  - intros j Hj. rewrite <- (brel_bc_get _ _ _ _ _ _ _ _ _ _ j H) by lia.
    pose proof (B j Hj) as Bj. autorewrite with btupd in Bj. exact Bj.
  - rewrite <- (brel_bc_get _ _ _ _ _ _ _ _ _ _ r H) by lia. exact Cr.
Qed.

Lemma pass2_rel : forall f g s0 t FC DL HP HL HM DP BC OL SL MC T hp dep blc ovf,
  brel t FC DL HP DP BC T hp dep blc -> bcr BC -> 1 <= ovf -> ovf <= 2 * Z.of_nat f ->
  (Z.to_nat ovf < g)%nat ->
  GBM.gb2_ok (DS.sd_max_length t) f (bt_upd s0 t FC DL HP HL HM DP BC OL SL MC) ovf ->
  exists BC', DT.gen_bitlen_loop2 f (bt_upd s0 t FC DL HP HL HM DP BC OL SL MC) (DS.sd_max_length t) ovf
              = bt_upd s0 t FC DL HP HL HM DP BC' OL SL MC
    /\ brel t FC DL HP DP BC' T hp dep (RT.gb_adjust g (DS.sd_max_length t) blc ovf) /\ bcr BC'.
Proof.
  induction f as [|f IH]; intros g s0 t FC DL HP HL HM DP BC OL SL MC T hp dep blc ovf H Hbc Hov1 Hov2 Hg Hok; [lia|].
  destruct g as [|g]; [lia|].
  pose proof (ml_range t) as Hml.
  destruct (GBM.gb2_ok_step t (DS.sd_max_length t) f s0 FC DL HP HL HM DP BC OL SL MC ovf Hok) as [Hr Hnext].
  cbv zeta in Hr, Hnext.
  destruct (find_agree s0 t FC DL HP HL HM DP BC OL SL MC T hp dep blc (DS.sd_max_length t) H ltac:(lia) Hr)
    as [Ef Rr].
  rewrite GBM.GL2_step. cbn [RT.gb_adjust]. cbv zeta. rewrite Ef.
  set (r := DT.gen_bitlen_find (Z.to_nat (DS.sd_max_length t)) (bt_upd s0 t FC DL HP HL HM DP BC OL SL MC)
                               (DS.sd_max_length t - 1)) in *.
  set (ML := DS.sd_max_length t) in *.
  unfold GBM.bl_adj. cbv zeta.
  rewrite <- (brel_bc_get _ _ _ _ _ _ _ _ _ _ r H) by lia.
  set (BC1 := arr_set BC r (wrap16 (arr_get BC r - 1))).
  assert (B1 : brel t FC DL HP DP BC1 T hp dep (Base.zset blc r (Base.u16 (arr_get BC r - 1))))
    by (apply brel_bc_set; [exact H | lia]).
  rewrite <- (brel_bc_get _ _ _ _ _ _ _ _ _ _ (r + 1) B1) by lia.
  set (BC2 := arr_set BC1 (r + 1) (wrap16 (arr_get BC1 (r + 1) + 2))).
  assert (B2 : brel t FC DL HP DP BC2 T hp dep
                 (Base.zset (Base.zset blc r (Base.u16 (arr_get BC r - 1))) (r + 1) (Base.u16 (arr_get BC1 (r + 1) + 2))))
    by (apply brel_bc_set; [exact B1 | lia]).
  rewrite <- (brel_bc_get _ _ _ _ _ _ _ _ _ _ ML B2) by lia.
  set (BC3 := arr_set BC2 ML (wrap16 (arr_get BC2 ML - 1))).
  assert (B3 : brel t FC DL HP DP BC3 T hp dep
                 (Base.zset (Base.zset (Base.zset blc r (Base.u16 (arr_get BC r - 1))) (r + 1)
                                       (Base.u16 (arr_get BC1 (r + 1) + 2))) ML (Base.u16 (arr_get BC2 ML - 1))))
    by (apply brel_bc_set; [exact B2 | lia]).
  assert (R3 : bcr BC3) by (subst BC3 BC2 BC1; apply bcr_set, bcr_set, bcr_set, Hbc).
  destruct (Z.ltb_spec 0 (ovf - 2)) as [C|C].
  - replace (2 <? ovf) with true by (symmetry; apply Z.ltb_lt; lia).
    destruct (IH g s0 t FC DL HP HL HM DP BC3 OL SL MC T hp dep _ (ovf - 2) B3 R3 ltac:(lia) ltac:(lia) ltac:(lia)
                (Hnext C)) as (BC' & E1 & E2 & E3).
    exists BC'. split; [exact E1|]. split; [exact E2 | exact E3].
  - replace (2 <? ovf) with false by (symmetry; apply Z.ltb_ge; lia).
    exists BC3. split; [reflexivity|]. split; [exact B3 | exact R3].
Qed.

(* ------------------------------------------------------------------------- *)
(* 4.  Pass 3: S5's inner loop is a run of RT steps                          *)
(* ------------------------------------------------------------------------- *)

Lemma pass3i_rel : forall fi s0 t FC DL HP HL HM DP BC OL SL MC T hp dep blc bits n h,
  brel t FC DL HP DP BC T hp dep blc -> -1 <= MC < DS.sd_elems t -> 1 <= bits <= 15 ->
  0 <= n -> 0 <= h <= 573 -> (Z.to_nat h < fi)%nat ->
  GBM.gb3i_ok t MC fi (bt_upd s0 t FC DL HP HL HM DP BC OL SL MC) bits n h ->
  exists DL' OL' h' T',
    DT.gen_bitlen_loop3i fi (bt_upd s0 t FC DL HP HL HM DP BC OL SL MC) t MC bits n h
      = (bt_upd s0 t FC DL' HP HL HM DP BC OL' SL MC, h')
    /\ 0 <= h' <= h
    /\ (forall F, RT.gb_pass2 (Z.to_nat (h - h') + F) hp MC T blc bits n h OL
                  = RT.gb_pass2 F hp MC T' blc bits 0 h' OL')
    /\ brel t FC DL' HP DP BC T' hp dep blc.
Proof.
  induction fi as [|fi IH]; intros s0 t FC DL HP HL HM DP BC OL SL MC T hp dep blc bits n h H HMC Hb Hn Hh Hf Hok; [lia|].
  pose proof (tsize_le t) as Ht. destruct (elems_range t) as [HE Hts].
  rewrite GBM.GL3i_step.
  destruct (Z.eqb_spec n 0) as [E0|E0].
  - subst n. cbn [negb]. exists DL, OL, h, T. split; [reflexivity|]. split; [lia|]. split; [|exact H].
    intros F. replace (h - h) with 0 by lia. reflexivity.
  - cbn [negb]. cbn [GBM.gb3i_ok] in Hok.
    replace (negb (n =? 0)) with true in Hok by (symmetry; apply negb_true_iff, Z.eqb_neq; exact E0).
    destruct Hok as (Hh1 & Hm & Hok). autorewrite with btupd in Hm.
    rewrite GBM.GB3i_flat in Hok |- *. cbv zeta in Hok |- *.
    set (m := arr_get HP (h - 1)) in *.
    assert (Hstep : forall F, RT.gb_pass2 (S F) hp MC T blc bits n h OL
                    = if MC <? m then RT.gb_pass2 F hp MC T blc bits n (h - 1) OL
                      else if RT.t_len T m =? bits then RT.gb_pass2 F hp MC T blc bits (n - 1) (h - 1) OL
                      else RT.gb_pass2 F hp MC (RT.t_setlen T m bits) blc bits (n - 1) (h - 1)
                                       (RT.u64 (OL + (bits - RT.t_len T m) * RT.t_freq T m))).
    { intros F. cbn [RT.gb_pass2]. replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; exact E0).
      cbv zeta. rewrite <- (brel_hp_get _ _ _ _ _ _ _ _ _ _ (h - 1) H) by lia. reflexivity. }
    destruct (Z.ltb_spec MC m) as [Cm|Cm].
    + destruct (IH s0 t FC DL HP HL HM DP BC OL SL MC T hp dep blc bits n (h - 1) H HMC Hb Hn ltac:(lia) ltac:(lia) Hok)
        as (DL' & OL' & h' & T' & E1 & E2 & E3 & E4).
      exists DL', OL', h', T'. split; [exact E1|]. split; [lia|]. split; [|exact E4].
      intros F. replace (Z.to_nat (h - h') + F)%nat with (S (Z.to_nat (h - 1 - h') + F)) by lia.
      rewrite Hstep. replace (MC <? m) with true by (symmetry; apply Z.ltb_lt; lia). apply E3.
    + destruct (Z.eqb_spec (arr_get DL m) bits) as [Cb|Cb].
      * destruct (IH s0 t FC DL HP HL HM DP BC OL SL MC T hp dep blc bits (n - 1) (h - 1) H HMC Hb ltac:(lia) ltac:(lia) ltac:(lia) Hok)
          as (DL' & OL' & h' & T' & E1 & E2 & E3 & E4).
        exists DL', OL', h', T'. split; [exact E1|]. split; [lia|]. split; [|exact E4].
        intros F. replace (Z.to_nat (h - h') + F)%nat with (S (Z.to_nat (h - 1 - h') + F)) by lia.
        rewrite Hstep. replace (MC <? m) with false by (symmetry; apply Z.ltb_ge; lia).
        unfold RT.t_len. rewrite <- (brel_dl_get _ _ _ _ _ _ _ _ _ _ m H) by lia. rewrite Cb, Z.eqb_refl. apply E3.
      * rewrite wrap64_u64 in Hok |- *.
        assert (B1 : brel t FC (arr_set DL m (wrap16 bits)) HP DP BC (RT.t_setlen T m bits) hp dep blc)
          by (apply brel_dl_set; [exact H | lia]).
        destruct (IH s0 t FC (arr_set DL m (wrap16 bits)) HP HL HM DP BC (RT.u64 (OL + (bits - arr_get DL m) * arr_get FC m))
                     SL MC (RT.t_setlen T m bits) hp dep blc bits (n - 1) (h - 1) B1 HMC Hb ltac:(lia) ltac:(lia) ltac:(lia) Hok)
          as (DL' & OL' & h' & T' & E1 & E2 & E3 & E4).
        exists DL', OL', h', T'. split; [exact E1|]. split; [lia|]. split; [|exact E4].
        intros F. replace (Z.to_nat (h - h') + F)%nat with (S (Z.to_nat (h - 1 - h') + F)) by lia.
        rewrite Hstep. replace (MC <? m) with false by (symmetry; apply Z.ltb_ge; lia).
        unfold RT.t_len, RT.t_freq. rewrite <- (brel_dl_get _ _ _ _ _ _ _ _ _ _ m H) by lia.
        rewrite <- (brel_fc_get _ _ _ _ _ _ _ _ _ _ m H) by lia.
        replace (arr_get DL m =? bits) with false by (symmetry; apply Z.eqb_neq; exact Cb). apply E3.
Qed.

Lemma pass3_rel : forall f g s0 t FC DL HP HL HM DP BC OL SL MC T hp dep blc bits h,
  brel t FC DL HP DP BC T hp dep blc -> -1 <= MC < DS.sd_elems t -> bcr BC -> 1 <= bits <= 15 -> 0 <= h <= 573 ->
  (Z.to_nat bits <= f)%nat -> (Z.to_nat h + Z.to_nat bits < g)%nat ->
  GBM.gb3_ok t MC f (bt_upd s0 t FC DL HP HL HM DP BC OL SL MC) bits h ->
  exists DL' OL',
    DT.gen_bitlen_loop3 f (bt_upd s0 t FC DL HP HL HM DP BC OL SL MC) t MC bits h
      = bt_upd s0 t FC DL' HP HL HM DP BC OL' SL MC
    /\ brel t FC DL' HP DP BC (fst (RT.gb_pass2 g hp MC T blc bits (blc bits) h OL)) hp dep blc
    /\ OL' = snd (RT.gb_pass2 g hp MC T blc bits (blc bits) h OL).
Proof.
  induction f as [|f IH]; intros g s0 t FC DL HP HL HM DP BC OL SL MC T hp dep blc bits h H HMC Hbc Hb Hh Hf Hg Hok; [lia|].
  rewrite GBM.GL3_step. cbn [GBM.gb3_ok] in Hok.
  replace (negb (bits =? 0)) with true in Hok |- * by (symmetry; apply negb_true_iff, Z.eqb_neq; lia).
  destruct Hok as [Hi Hok]. autorewrite with btupd in Hi, Hok |- *.
  assert (Hn : 0 <= arr_get BC bits) by (pose proof (Hbc bits ltac:(lia)); lia).
  destruct (pass3i_rel 574 s0 t FC DL HP HL HM DP BC OL SL MC T hp dep blc bits (arr_get BC bits) h H HMC Hb Hn Hh
              ltac:(lia) Hi) as (DL1 & OL1 & h1 & T1 & E1 & E2 & E3 & E4).
  rewrite E1 in Hok |- *.
  rewrite <- (brel_bc_get _ _ _ _ _ _ _ _ _ _ bits H) by lia.
  replace g with (Z.to_nat (h - h1) + S (g - Z.to_nat (h - h1) - 1))%nat by lia.
  rewrite E3. cbn [RT.gb_pass2]. rewrite Z.eqb_refl.
  destruct (Z.leb_spec bits 1) as [C1|C1].
  - assert (bits = 1) by lia. subst bits. rewrite GBM.GL3_done. cbn [fst snd].
    exists DL1, OL1. split; [reflexivity|]. split; [exact E4 | reflexivity].
  - destruct (IH (g - Z.to_nat (h - h1) - 1)%nat s0 t FC DL1 HP HL HM DP BC OL1 SL MC T1 hp dep blc (bits - 1) h1
                 E4 HMC Hbc ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hok) as (DL2 & OL2 & F1 & F2 & F3).
    exists DL2, OL2. split; [exact F1|]. split; [exact F2 | exact F3].
Qed.

(* ------------------------------------------------------------------------- *)
(* 5.  [gen_bitlen]                                                          *)
(* ------------------------------------------------------------------------- *)

Lemma brel_bc_replace : forall t FC DL HP DP BC BC' T hp dep blc blc',
  brel t FC DL HP DP BC T hp dep blc -> arr_rel BC' blc' 0 16 -> arr_len BC' = 16 ->
  brel t FC DL HP DP BC' T hp dep blc'.
Proof. intros t FC DL HP DP BC BC' T hp dep blc blc' H R L. destruct H. constructor; assumption. Qed.

Lemma fill_zero : forall BC (blc : Base.zarr), arr_len BC = 16 ->
  arr_rel (arr_fill BC 0 (DS.MAX_BITS + 1) 0) (RT.arr_zero (Z.to_nat RT.MAX_BITS + 1) 0 blc) 0 16
  /\ bcr (arr_fill BC 0 (DS.MAX_BITS + 1) 0) /\ arr_len (arr_fill BC 0 (DS.MAX_BITS + 1) 0) = 16.
Proof.
  intros BC blc HL. change (DS.MAX_BITS + 1) with 16. change (Z.to_nat RT.MAX_BITS + 1)%nat with 16%nat.
  assert (F : forall i, 0 <= i < 16 -> arr_get (arr_fill BC 0 16 0) i = 0).
  { intros i Hi. rewrite arr_get_fill. unfold arr_inb. rewrite HL.
    replace ((0 <=? i) && (i <? 0 + Z.max 0 16) && ((0 <=? i) && (i <? 16))) with true
      by (symmetry; rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt; lia). reflexivity. }
  split; [|split; [|rewrite arr_len_fill; exact HL]].
  - intros i Hi. rewrite F by exact Hi. rewrite RT.arr_zero_hit by (cbn; lia). reflexivity.
  - intros i Hi. rewrite F by exact Hi. lia.
Qed.

Lemma rt_gb_install : forall k T blc ol sl (ts : RT.TSt),
  let ts' := RT.set_statlen sl (RT.set_optlen ol (RT.set_blcount blc (RT.set_tree k T ts))) in
  RT.ts_trees ts' k = T /\ RT.ts_blcount ts' = blc /\ RT.ts_optlen ts' = ol /\ RT.ts_statlen ts' = sl
  /\ RT.ts_heap ts' = RT.ts_heap ts /\ RT.ts_depth ts' = RT.ts_depth ts
  /\ RT.ts_heaplen ts' = RT.ts_heaplen ts /\ RT.ts_heapmax ts' = RT.ts_heapmax ts
  /\ RT.ts_maxcode ts' = RT.ts_maxcode ts
  /\ (forall j, j <> k -> RT.ts_trees ts' j = RT.ts_trees ts j)
  /\ RT.ts_symbuf ts' = RT.ts_symbuf ts /\ RT.ts_symnext ts' = RT.ts_symnext ts
  /\ RT.ts_matches ts' = RT.ts_matches ts /\ RT.ts_bw ts' = RT.ts_bw ts.
Proof.
  intros k T blc ol sl ts ts'. subst ts'. cbn.
  rewrite Z.eqb_refl. csplit; try reflexivity.
  intros j Hj. replace (j =? k) with false by (symmetry; apply Z.eqb_neq; exact Hj). reflexivity.
Qed.

Lemma gen_bitlen_rel : forall s0 t FC DL HP HL HM DP BC OL SL MC (ts : RT.TSt),
  brel t FC DL HP DP BC (RT.ts_trees ts (tk_of t)) (RT.ts_heap ts) (RT.ts_depth ts) (RT.ts_blcount ts) ->
  HM = RT.ts_heapmax ts -> MC = RT.ts_maxcode ts (tk_of t) -> OL = RT.ts_optlen ts -> SL = RT.ts_statlen ts ->
  0 <= HM < 573 -> -1 <= MC < DS.sd_elems t ->
  0 <= arr_get HP HM < TM.tsize t ->
  (forall h, HM + 1 <= h < 573 -> 0 <= arr_get HP h < TM.tsize t) ->
  dlr t DL ->
  GBM.gb1_ok t MC 573 (bt_upd s0 t FC (arr_set DL (arr_get HP HM) (wrap16 0)) HP HL HM DP
                         (arr_fill BC 0 (DS.MAX_BITS + 1) 0) OL SL MC) (HM + 1) 0 ->
  (let '(X10, ovf) := DT.gen_bitlen_loop1 573 (bt_upd s0 t FC (arr_set DL (arr_get HP HM) (wrap16 0)) HP HL HM DP
                                                 (arr_fill BC 0 (DS.MAX_BITS + 1) 0) OL SL MC)
                         t MC (DS.sd_extra_base t) (DS.sd_max_length t) (HM + 1) 0 in
   ovf <> 0 -> GBM.gb2_ok (DS.sd_max_length t) 573 X10 ovf
               /\ GBM.gb3_ok t MC (Z.to_nat (DS.sd_max_length t)) (DT.gen_bitlen_loop2 573 X10 (DS.sd_max_length t) ovf)
                     (DS.sd_max_length t) DS.HEAP_SIZE) ->
  exists DL' BC' OL' SL',
    DT.gen_bitlen (bt_upd s0 t FC DL HP HL HM DP BC OL SL MC) t = bt_upd s0 t FC DL' HP HL HM DP BC' OL' SL' MC
    /\ brel t FC DL' HP DP BC' (RT.ts_trees (RT.gen_bitlen (tk_of t) ts) (tk_of t))
            (RT.ts_heap (RT.gen_bitlen (tk_of t) ts)) (RT.ts_depth (RT.gen_bitlen (tk_of t) ts))
            (RT.ts_blcount (RT.gen_bitlen (tk_of t) ts))
    /\ OL' = RT.ts_optlen (RT.gen_bitlen (tk_of t) ts) /\ SL' = RT.ts_statlen (RT.gen_bitlen (tk_of t) ts)
    /\ RT.ts_heap (RT.gen_bitlen (tk_of t) ts) = RT.ts_heap ts /\ RT.ts_depth (RT.gen_bitlen (tk_of t) ts) = RT.ts_depth ts
    /\ RT.ts_heaplen (RT.gen_bitlen (tk_of t) ts) = RT.ts_heaplen ts
    /\ RT.ts_heapmax (RT.gen_bitlen (tk_of t) ts) = RT.ts_heapmax ts
    /\ RT.ts_maxcode (RT.gen_bitlen (tk_of t) ts) = RT.ts_maxcode ts
    /\ (forall j, j <> tk_of t -> RT.ts_trees (RT.gen_bitlen (tk_of t) ts) j = RT.ts_trees ts j)
    /\ RT.ts_symbuf (RT.gen_bitlen (tk_of t) ts) = RT.ts_symbuf ts
    /\ RT.ts_symnext (RT.gen_bitlen (tk_of t) ts) = RT.ts_symnext ts
    /\ RT.ts_matches (RT.gen_bitlen (tk_of t) ts) = RT.ts_matches ts
    /\ RT.ts_bw (RT.gen_bitlen (tk_of t) ts) = RT.ts_bw ts.
Proof.
  intros s0 t FC DL HP HL HM DP BC OL SL MC ts H EHM EMC EOL ESL HHM HMC Hroot Htop Hdl Hg1 Hg2.
  pose proof (ml_range t) as Hml. pose proof (tsize_le t) as Ht.
  unfold DT.gen_bitlen. cbv zeta. autorewrite with btupd.
  unfold RT.gen_bitlen. cbv zeta. rewrite <- EHM, <- EMC, <- EOL, <- ESL, ml_agree, base_agree.
  rewrite <- (brel_hp_get _ _ _ _ _ _ _ _ _ _ HM H) by lia.
  destruct (fill_zero BC (RT.ts_blcount ts) (b_lbc _ _ _ _ _ _ _ _ _ _ H)) as (FZ1 & FZ2 & FZ3).
  assert (B9 : brel t FC (arr_set DL (arr_get HP HM) (wrap16 0)) HP DP (arr_fill BC 0 (DS.MAX_BITS + 1) 0)
                 (RT.t_setlen (RT.ts_trees ts (tk_of t)) (arr_get HP HM) 0) (RT.ts_heap ts) (RT.ts_depth ts)
                 (RT.arr_zero (Z.to_nat RT.MAX_BITS + 1) 0 (RT.ts_blcount ts))).
  { apply brel_bc_replace with (BC := arr_fill BC 0 (DS.MAX_BITS + 1) 0)
      (blc := RT.arr_zero (Z.to_nat RT.MAX_BITS + 1) 0 (RT.ts_blcount ts)); [|exact FZ1 | exact FZ3].
    apply brel_dl_set; [|lia]. apply brel_bc_replace with (BC := BC) (blc := RT.ts_blcount ts); [exact H | exact FZ1 | exact FZ3]. }
  pose proof (pass1_rel 573 (Z.to_nat RT.HEAP_SIZE + 1) s0 t FC (arr_set DL (arr_get HP HM) (wrap16 0)) HP HL HM DP
                (arr_fill BC 0 (DS.MAX_BITS + 1) 0) OL SL MC _ _ _ _ (HM + 1) 0 B9 ltac:(lia) HMC
                ltac:(intros; apply Htop; lia) (dlr_set _ _ _ _ Hdl) FZ2 ltac:(lia) Hg1 ltac:(lia)
                ltac:(change RT.HEAP_SIZE with 573; lia)) as P1.
  cbv zeta in P1.
  destruct (DT.gen_bitlen_loop1 573 _ t MC (DS.sd_extra_base t) (DS.sd_max_length t) (HM + 1) 0) as [X10 ovf] eqn:EL1.
  match goal with |- context [RT.gb_pass1 ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j ?k ?l ?m ?n] =>
    destruct (RT.gb_pass1 a b c d e f g h i j k l m n) as [[[[T2 blc1] ol1] sl1] ov] end.
  destruct P1 as (DL10 & BC10 & OL10 & SL10 & E1 & E2 & B10 & EO & ES & Hov & Hdl10 & Hbc10).
  cbn [fst snd] in E1, E2. subst X10 ovf.
  try rewrite EL1 in Hg2. cbv beta iota in Hg2 |- *.
  destruct (Z.eqb_spec ov 0) as [Z0|Z0].
  - subst ov.
    destruct (rt_gb_install (tk_of t) T2 blc1 ol1 sl1 ts) as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12 & I13 & I14).
    exists DL10, BC10, OL10, SL10. rewrite I1, I2, I3, I4, I5, I6.
    csplit; first [reflexivity | assumption | rewrite I8; symmetry; exact EHM].
  -
    destruct (Hg2 Z0) as [G2 G3].
    destruct (pass2_rel 573 (Z.to_nat ov + 1) s0 t FC DL10 HP HL HM DP BC10 OL10 SL10 MC T2 (RT.ts_heap ts) (RT.ts_depth ts)
                blc1 ov B10 Hbc10 ltac:(lia) ltac:(lia) ltac:(lia) G2) as (BC11 & E11 & B11 & Hbc11).
    rewrite E11 in G3 |- *.
    change DS.HEAP_SIZE with 573 in G3 |- *.
    destruct (pass3_rel (Z.to_nat (DS.sd_max_length t)) (2 * Z.to_nat RT.HEAP_SIZE + Z.to_nat RT.MAX_BITS + 4)
                s0 t FC DL10 HP HL HM DP BC11 OL10 SL10 MC T2 (RT.ts_heap ts) (RT.ts_depth ts)
                (RT.gb_adjust (Z.to_nat ov + 1) (DS.sd_max_length t) blc1 ov) (DS.sd_max_length t) 573
                B11 HMC Hbc11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(change RT.HEAP_SIZE with 573; change RT.MAX_BITS with 15; lia) G3)
      as (DL12 & OL12 & E12 & B12 & EO12).
    rewrite E12. change RT.HEAP_SIZE with 573. rewrite <- EO.
    destruct (RT.gb_pass2 _ (RT.ts_heap ts) MC T2 _ (DS.sd_max_length t) _ 573 OL10) as [T3 ol2] eqn:EP.
    cbn [fst snd] in B12, EO12.
    destruct (rt_gb_install (tk_of t) T3 (RT.gb_adjust (Z.to_nat ov + 1) (DS.sd_max_length t) blc1 ov) ol2 sl1 ts)
      as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12 & I13 & I14).
    exists DL12, BC11, OL12, SL10. rewrite I1, I2, I3, I4, I5, I6.
    csplit; first [reflexivity | assumption | rewrite I8; symmetry; exact EHM].
Qed.
