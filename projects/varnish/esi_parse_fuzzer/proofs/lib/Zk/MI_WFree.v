(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc Mall7vg KInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_S421.

Module MI_Read.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc Mall7vg KInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Inv MI_Kit MI_Arith.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall7vg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List.MI_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Arith.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rd8_known {R} st q v (k : Z -> M R) :
  cell_read (get_shadow st (fst q)) (snd q) = Known v -> rd8 st q k = k v.
Proof. intros H. unfold rd8. rewrite H. reflexivity. Qed.

Lemma known_at st rid o v rid' o' :
  known st (rid, o) v -> o' = o -> rid' = rid -> cell_read (get_shadow st rid') o' = Known v.
Proof. intros H -> ->. exact H. Qed.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma rd8_ftree {R} L st q (k : Z -> M R) Post :
  (forall v, cell_read (get_shadow st (fst q)) (snd q) = Known v -> 0 <= v < 256) ->
  (forall v, 0 <= v < 256 -> ftree L (k v) Post) ->
  ftree L (rd8 st q k) Post.
Proof.
  intros Hk H. unfold rd8. destruct (cell_read _ _) as [v|h] eqn:E.
  - apply H. apply Hk. reflexivity.
  - cbn [ftree]. intros v Hv. unfold peek_answer_ok.
    destruct (Z.leb_spec 0 v), (Z.ltb_spec v 256); cbn [andb]; try lia. apply H. lia.
Qed.

Lemma rd16_ftree {R} L st q (k : Z -> M R) Post :
  (forall q' v, cell_read (get_shadow st (fst q')) (snd q') = Known v -> 0 <= v < 256) ->
  (forall v, 0 <= v < 65536 -> ftree L (k v) Post) ->
  ftree L (rd16 st q k) Post.
Proof.
  intros Hk H. unfold rd16. apply rd8_ftree; [apply Hk|]. intros b0 H0. apply rd8_ftree; [apply Hk|]. intros b1 H1. apply H. lia.
Qed.

End CEIL.

(* [comment removed for export] *)
Lemma known_byte st rid o v :
  (forall sh o' v' t, s_shadow st !! rid = Some sh -> r_cells sh !! o' = Some (v', t) -> 0 <= v' < 256) ->
  cell_read (get_shadow st rid) o = Known v -> 0 <= v < 256.
Proof.
  intros Hc H. unfold cell_read, get_shadow in H. destruct (s_shadow st !! rid) as [sh|] eqn:E; cbn [default id] in H.
  - destruct (r_cells sh !! o) as [[v' t]|] eqn:E2.
    + match type of H with (if ?c then _ else _) = _ => destruct c end; inversion H. subst. eapply Hc; eauto.
    + match type of H with (if ?c then _ else _) = _ => destruct c end; inversion H. lia.
  - rewrite !lookup_empty in H. cbn in H. inversion H. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_255 x : 0 <= x -> Z.land x 255 = x mod 256.
Proof. intros. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma byte_of_0 x : 0 <= x -> byte_of x 0 = x mod 256.
Proof. intros. unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r. apply land_255. lia. Qed.
Lemma byte_of_1 x : 0 <= x -> byte_of x 1 = (x / 256) mod 256.
Proof. intros. unfold byte_of. replace (8 * 1) with 8 by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. apply land_255. apply Z.div_pos; lia. Qed.
Lemma byte_of_2 x : 0 <= x -> byte_of x 2 = (x / 65536) mod 256.
Proof. intros. unfold byte_of. replace (8 * 2) with 16 by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with 65536. apply land_255. apply Z.div_pos; lia. Qed.
Lemma byte_of_3 x : 0 <= x -> byte_of x 3 = (x / 16777216) mod 256.
Proof. intros. unfold byte_of. replace (8 * 3) with 24 by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 24) with 16777216. apply land_255. apply Z.div_pos; lia. Qed.

Lemma byte_of_range x k : 0 <= x -> 0 <= k -> 0 <= byte_of x k < 256.
Proof.
  intros. unfold byte_of. rewrite land_255 by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_pos; [lia| apply Z.pow_pos_nonneg; lia]).
  apply Z.mod_pos_bound. lia.
Qed.

Lemma u16_bytes q : 0 <= q < 2^16 -> byte_of q 0 + 256 * byte_of q 1 = q.
Proof. intros. rewrite byte_of_0, byte_of_1 by lia. rewrite (Z.mod_small (q / 256)) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]). pose proof (Z.div_mod q 256 ltac:(lia)). lia. Qed.

Lemma u32_bytes r : 0 <= r < 2^32 ->
  byte_of r 0 + 256 * byte_of r 1 + 65536 * byte_of r 2 + 16777216 * byte_of r 3 = r.
Proof.
  intros. rewrite byte_of_0, byte_of_1, byte_of_2, byte_of_3 by lia.
  pose proof (Z.div_mod r 256 ltac:(lia)) as E1.
  pose proof (Z.div_mod (r / 256) 256 ltac:(lia)) as E2. rewrite (Z.div_div r 256 256) in E2 by lia. change (256 * 256) with 65536 in E2.
  pose proof (Z.div_mod (r / 65536) 256 ltac:(lia)) as E3. rewrite (Z.div_div r 65536 256) in E3 by lia. change (65536 * 256) with 16777216 in E3.
  rewrite (Z.mod_small (r / 16777216)) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  lia.
Qed.

(* [comment removed for export] *)
Lemma land31_idx i r : 0 <= i <= 31 -> 0 <= r -> Z.land (i + 32 * r) 31 = i.
Proof.
  intros. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2 ^ 5) with 32.
  replace (i + 32 * r) with (i + r * 32) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma shiftr5_res i r : 0 <= i <= 31 -> 0 <= r -> Z.shiftr (i + 32 * r) 5 = r.
Proof.
  intros. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32.
  replace (i + 32 * r) with (r * 32 + i) by lia. rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma area_of_mslot a k : snd a mod PGSZ = 0 -> 0 <= k < NSLOTS -> area_of (mslot a k) = a.
Proof.
  intros Ha Hk. unfold area_of, mslot, aadd, AREA_HDR, META_SIZE, NSLOTS, PGSZ in *. destruct a as [r o]; cbn in *. f_equal.
  rewrite <- Zplus_mod_idemp_l, Ha. cbn [Z.add]. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
End MI_Read.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall7vg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List.MI_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Arith OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Geom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ext OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_S421 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.MI_Read OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2.MI_Pres1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.

Module LB_Dead.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc KInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Inv MI_Kit MI_List.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List.MI_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lookup_del_group g st b :
  s_groups (del_group g st) !! b = if aptr_eqb b g then None else s_groups st !! b.
Proof.
  rewrite s_groups_del_group. destruct (aptr_eqb_spec b g) as [->|NE];
  [rewrite lookup_delete_eq| rewrite lookup_delete_ne by congruence]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma queue_key_g (h : lhead) (g : aptr) (st : mstate) : s_metas (queue_st h g st) !! g <> None.
Proof.
  unfold queue_st, q_link, q_single.
  destruct (get_head st h) as [a|].
  - rewrite lookup_metas_upd. destruct (aptr_eqb g a); [discriminate|].
    destruct (m_prev (get_meta_rec st a)) as [z|]; rewrite ?lookup_metas_upd; [destruct (aptr_eqb g z); [discriminate|]|];
      rewrite aptr_eqb_refl; discriminate.
  - rewrite set_head_metas, lookup_metas_upd, aptr_eqb_refl. discriminate.
Qed.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.
Lemma ftree_guard_inv {R} L tag (c : bool) (k bail : M R) Post :
  ftree L (guard tag c k bail) Post -> c = true /\ ftree L k Post.
Proof. unfold guard. destruct c; cbn; [auto| intros H; destruct H]. Qed.
End CEIL.
End LB_Dead.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Open Scope Z_scope.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma guard_true {R} tag (c : bool) (k bail : M R) : c = true -> guard tag c k bail = k.
Proof. intros ->. reflexivity. Qed.

Lemma size_class_28 sc : 28 <= sc < 48 -> 292 <= size_class sc.
Proof.
  intros H. unfold size_class.
  assert (E : exists n, Z.to_nat sc = (28 + n)%nat /\ (n < 20)%nat) by (exists (Z.to_nat sc - 28)%nat; lia).
  (first [ dex1 E as n; destruct E as [-> Hn] | dand3 E as n -> Hn | destruct E as (n & -> & Hn) ]).
  do 20 (destruct n as [|n]; [cbn; lia|]). lia.
Qed.

(* [comment removed for export] *)
Lemma guard16_arith S stride i off n q last :
  1 <= S -> 16 * q = stride * i + 16 * off -> 16 * off + n <= stride - 4 -> 0 <= n -> 0 <= off <= 255 -> 0 <= i <= last ->
  (stride = 16 * S \/ last = 0) -> (stride <= 16 * S \/ 292 <= S) ->
  S * i <= q < S * (i + 1).
Proof.
  intros HS Hq Hfit Hn Hoff Hi A B.
  destruct A as [E|L0].
  - subst stride. assert (q = S * i + off) by lia. subst q. nia.
  - assert (i = 0) by lia. subst i. assert (q = off) by lia. subst q. lia.
Qed.

Lemma guard17_arith stride i off n q last maplen :
  16 <= stride -> 16 * q = stride * i + 16 * off -> 16 * off + n <= stride - 4 -> 0 <= n -> 0 <= off -> 0 <= i <= last ->
  16 + stride * (last + 1) <= maplen * 4096 ->
  q <= maplen * 4096 / 16 - 1.
Proof.
  intros. replace (maplen * 4096 / 16) with (maplen * 256) by (rewrite <- (Z.div_mul (maplen * 256) 16) by lia; f_equal; lia).
  assert (stride * i + stride <= stride * (last + 1)) by nia. lia.
Qed.

(* [comment removed for export] *)
Section BLOCK.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Variables (c : cptr) (off n : Z).
Hypothesis Hk : In ((c, off), n) BL.

Local Notation R := (MR st).

Record blk_facts (m bm : aptr) (i ai : Z) (a : aptr) (ar : area) (ka : Z) : Prop := mkBF {
  bf_slot : s_slots st !! c = Some (m, i);
  bf_hosts : s_groups st !! bm = Some (mkGhdr (Some m) ai);
  bf_mem : m_mem (R m) = Some bm;
  bf_c : c = (fst bm, sstart (R m) i);
  bf_i : 0 <= i <= m_last_idx (R m);
  bf_li : m_last_idx (R m) <= 31;
  bf_ai : 0 <= ai <= m_last_idx (R m);
  bf_off : 0 <= off <= 255;
  bf_n : 0 <= n;
  bf_fit : UNIT * off + n <= get_stride (R m) - IB;
  bf_stride : UNIT <= get_stride (R m) /\ get_stride (R m) mod UNIT = 0;
  bf_b16 : 0 <= snd bm /\ snd bm mod UNIT = 0;
  bf_notA : tbit (m_avail (R m)) i = false;
  bf_notF : tbit (m_freed (R m)) i = false;
  bf_notH : s_groups st !! c = None;
  bf_sc : (0 <= m_sizeclass (R m) < 48 /\ (get_stride (R m) <= UNIT * size_class (m_sizeclass (R m)) \/ 28 <= m_sizeclass (R m))
            /\ (get_stride (R m) = UNIT * size_class (m_sizeclass (R m)) \/ (m_last_idx (R m) = 0 /\ m_maplen (R m) <> 0)))
          \/ m_sizeclass (R m) = 63;
  bf_top : m_maplen (R m) <> 0 -> snd bm = 0 /\ gend (R m) <= m_maplen (R m) * 4096;
  bf_maplen : 0 <= m_maplen (R m);
  bf_area : s_areas st !! a = Some ar /\ a_check ar = c_secret (s_ctx st) /\ snd a mod PGSZ = 0 /\ 0 <= ka < NSLOTS /\ m = mslot a ka;
  bf_shadow : blk_shadow_ok st ((c, off), n) m i;
  bf_hdr0 : known st (fst bm, sstart (R m) (i + 1) - IB) 0;
  bf_bytes : forall q v, cell_read (get_shadow st (fst q)) (snd q) = Known v -> 0 <= v < 256
}.

Lemma block_facts : exists m bm i ai a ar ka, blk_facts m bm i ai a ar ka.
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  (first [ pose proof ((is_blocks _ _ _ IS _ Hk)) as dR_2; dex2 dR_2 as m i; dand4 dR_2 as Hs Hoff Hn Hfit | pose proof ((is_blocks _ _ _ IS _ Hk)) as dR_2; dand6 dR_2 as m i Hs Hoff Hn Hfit | destruct (is_blocks _ _ _ IS _ Hk) as (m & i & Hs & Hoff & Hn & Hfit) ]). cbn [bslot boff bsize fst snd] in Hs, Hoff, Hn, Hfit.
  (first [ pose proof ((is_valid _ _ _ IS _ _ _ Hs)) as dR_3; dand3 dR_3 as [bm Hm] Hi Ec | destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bm Hm] & Hi & Ec) ]).
  pose proof Hm as [ai Hm'].
  pose proof (ig_ok _ _ _ IG _ _ _ Hm') as GO.
  pose proof (hosts_mem _ _ _ IM _ _ Hm) as Hmem.
  rewrite (slot_start'_eq _ _ _ IM _ _ _ Hm) in Ec.
  pose proof (g_present _ _ _ _ _ _ GO) as Pr. destruct (s_metas st !! m) as [mr|] eqn:Em; [| congruence].
  (first [ pose proof ((ia_metas _ IA _ _ Em)) as dR_4; dex3 dR_4 as a ar ka; dand3 dR_4 as Ha Hka Emk | pose proof ((ia_metas _ IA _ _ Em)) as dR_4; dand6 dR_4 as a ar ka Ha Hka Emk | destruct (ia_metas _ IA _ _ Em) as (a & ar & ka & Ha & Hka & Emk) ]).
  (first [ pose proof ((ia_areas _ IA _ _ Ha)) as dR_5; dand4 dR_5 as (r & Hr & Hmk & Hal & Hpg & Hfr) Hck Hns _ | destruct (ia_areas _ IA _ _ Ha) as ((r & Hr & Hmk & Hal & Hpg & Hfr) & Hck & Hns & _) ]).
  exists m, bm, i, ai, a, ar, ka.
  pose proof (is_part _ _ _ IS _ _ _ _ Hm' Hi) as P. cbn zeta in P. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hm), <- Ec in P.
  assert (U : In c (map bslot BL)) by (change c with (bslot ((c, off), n)); apply in_map; exact Hk).
  unfold one5 in P.
  constructor; auto.
  - pose proof (g_li _ _ _ _ _ _ GO). lia.
  - exact (g_ai _ _ _ _ _ _ GO).
  - exact (stride_ge _ _ _ IG _ _ Hm).
  - exact (g_align _ _ _ _ _ _ GO).
  - destruct (tbit (m_avail (R m)) i) eqn:E; [exfalso; tauto| reflexivity].
  - destruct (tbit (m_freed (R m)) i) eqn:E; [exfalso; tauto| reflexivity].
  - destruct (s_groups st !! c) eqn:E; [| reflexivity]. exfalso. assert (s_groups st !! c <> None) by congruence. tauto.
  - destruct (g_sc _ _ _ _ _ _ GO) as [[Hsc Hml]|(Hsc & Hli & Hml & _)]; [left| right; exact Hsc].
    (first [ pose proof ((g_stride _ _ _ _ _ _ GO ltac:(lia))) as dR_6; dand3 dR_6 as S1 S2 S3 | destruct (g_stride _ _ _ _ _ _ GO ltac:(lia)) as (S1 & S2 & S3) ]).
    split; [exact Hsc|]. split; [exact S1|].
    unfold get_stride. destruct (m_last_idx (R m) =? 0) eqn:E0; destruct (m_maplen (R m) =? 0) eqn:EM; cbn [andb negb];
      first [left; reflexivity | right; split; [apply Z.eqb_eq; exact E0| apply Z.eqb_neq; exact EM]].
  - intros Hml. (first [ pose proof ((g_top _ _ _ _ _ _ GO Hml)) as dR_7; dand6 dR_7 as H0 r' _ _ _ Hge | destruct (g_top _ _ _ _ _ _ GO Hml) as (H0 & r' & _ & _ & _ & Hge) ]). auto.
  - exact (g_maplen _ _ _ _ _ _ GO).
  - exact (ish_blk _ _ ISH _ m i Hk Hs).
  - apply (ish_hdr0 _ _ ISH _ _ _ Hm). unfold cnt_of. lia.
  - intros q v Hq. eapply known_byte; [| exact Hq]. intros sh o' v' t Hsh Hc. exact (proj1 (proj1 (ish_ticks _ _ ISH _ _ Hsh) o' v' t Hc)).
Qed.
End BLOCK.

Section HDR.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (c : cptr) (off n : Z).
Variables (m bm : aptr) (i ai : Z) (a : aptr) (ar : area) (ka : Z).
Hypothesis BF : blk_facts st c off n m bm i ai a ar ka.
Local Notation R := (MR st).
Let p : aptr := aadd c (UNIT * off).
Let stride := get_stride (R m).
Let e : Z := snd c + stride - IB.
Let res : Z := e - snd p - n.
Let q : Z := (snd p - snd bm - UNIT) / UNIT.

Lemma p_snd : snd p = sstart (R m) i + UNIT * off.
Proof. subst p. rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF). reflexivity. Qed.
Lemma p_fst : fst p = fst bm.
Proof. subst p. rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF). reflexivity. Qed.
Lemma gbase_bm : gbase (R m) = bm.
Proof. unfold gbase. rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF). reflexivity. Qed.
Lemma c_snd : snd c = sstart (R m) i.
Proof. rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF). reflexivity. Qed.

Lemma q16 : UNIT * q = stride * i + UNIT * off /\ 0 <= q < 2^16.
Proof.
  (first [ pose proof ((bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF)) as dR_8; dand6 dR_8 as _ _ _ _ Q _ | destruct (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as (_ & _ & _ & _ & Q & _) ]). cbn [bslot boff fst snd] in Q.
  rewrite gbase_bm in Q. subst q p. cbn [snd aadd] in *. rewrite c_snd in *. unfold sstart in *. rewrite gbase_bm in *.
  destruct (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S1 S2]. subst stride.
  replace (snd bm + UNIT + get_stride (R m) * i + UNIT * off - snd bm - UNIT) with (get_stride (R m) * i + UNIT * off) in Q |- * by lia.
  split; [| exact Q].
  unfold UNIT in *. pose proof (Z.div_mod (get_stride (R m)) 16 ltac:(lia)). rewrite S2 in H.
  replace (get_stride (R m) * i + 16 * off) with ((get_stride (R m) / 16 * i + off) * 16) by lia.
  rewrite Z.div_mul by lia. lia.
Qed.

Let SH := bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF.

Lemma p_mod16 : snd p mod 16 = 0.
Proof.
  rewrite p_snd. unfold sstart. rewrite gbase_bm.
  destruct (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S1 S2]. destruct (bf_b16 _ _ _ _ _ _ _ _ _ _ _ BF) as [B1 B2]. unfold UNIT in *.
  pose proof (Z.div_mod (get_stride (R m)) 16 ltac:(lia)). pose proof (Z.div_mod (snd bm) 16 ltac:(lia)).
  rewrite S2 in H. rewrite B2 in H0.
  replace (snd bm + 16 + get_stride (R m) * i + 16 * off) with ((snd bm / 16 + 1 + get_stride (R m) / 16 * i + off) * 16) by lia.
  apply Z_mod_mult.
Qed.

Lemma res_nonneg : 0 <= res.
Proof.
  subst res e p stride. cbn [snd aadd]. pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF). pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF). unfold IB, UNIT in *. lia.
Qed.

Lemma get_meta_eq {T} (k : aptr -> Z -> Z -> M T) bail : get_meta st p k bail = k m q i.
Proof.
  pose proof SH as S. unfold blk_shadow_ok in S. cbn [bslot boff bsize fst snd] in S. rewrite gbase_bm in S.
  (first [ dand8 S as K4 K3 K2 K1 Q K5 Kr KU | destruct S as (K4 & K3 & K2 & K1 & Q & K5 & Kr & KU) ]).
  pose proof res_nonneg as RES. pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi. pose proof (bf_li _ _ _ _ _ _ _ _ _ _ _ BF) as Hli.
  unfold get_meta.
  rewrite (guard_true 10) by (apply Z.eqb_eq; exact p_mod16).
  unfold rd16.
  rewrite (rd8_known st (aadd p (-2)) (byte_of q 0)) by (eapply known_at; [exact K2| cbn; lia| reflexivity]).
  rewrite (rd8_known st (aadd (aadd p (-2)) 1) (byte_of q 1)) by (eapply known_at; [exact K1| cbn; lia| reflexivity]).
  rewrite (rd8_known st (aadd p (-3)) (i + 32 * Z.min res 5)) by (eapply known_at; [exact K3| cbn; lia| reflexivity]).
  rewrite (rd8_known st (aadd p (-4)) 0) by (eapply known_at; [exact K4| cbn; lia| reflexivity]).
  cbn [Z.eqb negb].
  rewrite (u16_bytes q Q).
  assert (Ebase : aadd p (- (UNIT * q) - UNIT) = bm).
  { pose proof q16 as [Q1 _]. pose proof p_snd as PS. pose proof p_fst as PF. unfold sstart in PS. rewrite gbase_bm in PS.
    subst stride. unfold aadd. destruct bm as [br bo]. cbn [fst snd] in *. f_equal; [exact PF| lia]. }
  rewrite Ebase. unfold get_group. rewrite (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF). cbn [g_meta].
  rewrite (land31_idx i (Z.min res 5)) by lia. fold (MR st m).
  rewrite (guard_true 11) by (rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF); apply optr_eqb_refl).
  rewrite (guard_true 12) by (apply Z.leb_le; lia).
  rewrite (guard_true 13) by (unfold testbit; rewrite (bf_notA _ _ _ _ _ _ _ _ _ _ _ BF : Z.testbit _ _ = false); reflexivity).
  rewrite (guard_true 14) by (unfold testbit; rewrite (bf_notF _ _ _ _ _ _ _ _ _ _ _ BF : Z.testbit _ _ = false); reflexivity).
  (first [ pose proof ((bf_area _ _ _ _ _ _ _ _ _ _ _ BF)) as dR_10; dand5 dR_10 as Ha Hck Hal Hka Em | destruct (bf_area _ _ _ _ _ _ _ _ _ _ _ BF) as (Ha & Hck & Hal & Hka & Em) ]).
  rewrite (guard_true 15) by (rewrite Em, (area_of_mslot a ka Hal Hka), Ha; apply Z.eqb_eq; exact Hck).
  pose proof q16 as [Q1 _]. pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF) as FIT. pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF) as N0.
  pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as OFF. fold stride in FIT.
  unfold UNIT, IB in Q1, FIT. fold stride in FIT.
  rewrite (guard_true 16).
  2:{ clear K4 K3 K2 K1 K5 Kr KU RES Ebase.
      destruct (bf_sc _ _ _ _ _ _ _ _ _ _ _ BF) as [(Hsc & Hle & Hst)| E63].
      - fold stride in Hle, Hst. unfold UNIT in Hle, Hst.
        pose proof (size_class_bound _ Hsc) as SB.
        assert (A : stride = 16 * size_class (m_sizeclass (R m)) \/ m_last_idx (R m) = 0) by tauto.
        assert (B : stride <= 16 * size_class (m_sizeclass (R m)) \/ 292 <= size_class (m_sizeclass (R m))).
        { destruct Hle as [Hle|H28]; [left; exact Hle| right; apply size_class_28; lia]. }
        clearbody p stride e res q. clear SH Hle Hst.
        pose proof (guard16_arith _ _ _ _ _ _ _ (proj1 SB) Q1 FIT N0 OFF Hi A B) as [G1 G2].
        destruct (Z.ltb_spec (m_sizeclass (R m)) 48); [|lia].
        apply Bool.andb_true_iff. split; [apply Z.leb_le; exact G1| apply Z.ltb_lt; exact G2].
      - clearbody p stride e res q. clear SH. destruct (Z.ltb_spec (m_sizeclass (R m)) 48); [lia|]. apply Z.eqb_eq. exact E63. }
  rewrite (guard_true 17).
  2:{ clear K4 K3 K2 K1 K5 Kr KU RES Ebase.
      destruct (Z.eqb_spec (m_maplen (R m)) 0) as [|NM]; cbn [negb]; [reflexivity|].
      destruct (bf_top _ _ _ _ _ _ _ _ _ _ _ BF NM) as [B0 GE]. apply Z.leb_le.
      unfold gend, cnt_of, sstart in GE. rewrite gbase_bm, B0 in GE. fold stride in GE. unfold UNIT in GE.
      pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S1 _]. fold stride in S1. unfold UNIT in S1.
      clearbody p stride e res q. clear SH.
      eapply (guard17_arith stride i off n q); try eassumption; lia. }
  reflexivity.
Qed.


(* [comment removed for export] *)
Let ea : aptr := aadd (aadd bm (UNIT + stride * i)) (stride - IB).

(* [comment removed for export] *)
Lemma ea_snd : snd ea = e.
Proof. subst ea e stride. cbn [snd aadd]. rewrite c_snd. unfold sstart. rewrite gbase_bm. lia. Qed.

Lemma ea_off d : snd (aadd ea d) = e + d.
Proof. pose proof ea_snd as EA. unfold aadd at 1. cbn [snd]. rewrite <- EA. reflexivity. Qed.

Lemma get_nominal_size_eq {T} (k : Z -> M T) bail : get_nominal_size st p ea k bail = k n.
Proof.
  pose proof SH as S. unfold blk_shadow_ok in S. cbn [bslot boff bsize fst snd] in S. rewrite gbase_bm in S.
  (first [ dand8 S as K4 K3 K2 K1 Q K5 Kr KU | destruct S as (K4 & K3 & K2 & K1 & Q & K5 & Kr & KU) ]).
  pose proof res_nonneg as RES. pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi. pose proof (bf_li _ _ _ _ _ _ _ _ _ _ _ BF) as Hli.
  pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF) as N0.
  pose proof ea_snd as EA. pose proof p_fst as PF. pose proof c_snd as CS.
  assert (CF : fst c = fst bm) by (rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF); reflexivity).
  assert (Hres : res = e - snd p - n) by reflexivity.
  assert (He : e = snd c + stride - IB) by reflexivity.
  assert (Hst : stride = get_stride (R m)) by reflexivity.
  assert (Hp2 : snd p = snd c + UNIT * off) by reflexivity.
  pose proof (bf_hdr0 _ _ _ _ _ _ _ _ _ _ _ BF) as H0. rewrite sstart_succ, <- CS, <- Hst in H0.
  (* [comment removed for export] *)
  assert (OFF : forall d, snd (aadd ea d) = snd c + get_stride (R m) - IB + d) by (intros d; rewrite ea_off, He, Hst; reflexivity).
  clearbody q. clear SH.
  unfold get_nominal_size.
  rewrite (rd8_known st (aadd p (-3)) (i + 32 * Z.min res 5)) by (eapply known_at; [exact K3| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
  cbv beta. rewrite (shiftr5_res i (Z.min res 5)) by lia. cbv zeta.
  destruct (Z.leb_spec 5 (Z.min res 5)) as [R5|R5].
  - (* [comment removed for export] *)
    (first [ pose proof ((K5 ltac:(lia))) as dR_12; dand6 dR_12 as B0 B1 B2 B3 B5 R32 | destruct (K5 ltac:(lia)) as (B0 & B1 & B2 & B3 & B5 & R32) ]).
    rewrite (guard_true 20) by (apply Z.eqb_eq; lia).
    unfold rd32.
    rewrite (rd8_known st (aadd ea (-4)) (byte_of res 0)) by (eapply known_at; [exact B0| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
    rewrite (rd8_known st (aadd (aadd ea (-4)) 1) (byte_of res 1)) by (eapply known_at; [exact B1| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
    rewrite (rd8_known st (aadd (aadd ea (-4)) 2) (byte_of res 2)) by (eapply known_at; [exact B2| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
    rewrite (rd8_known st (aadd (aadd ea (-4)) 3) (byte_of res 3)) by (eapply known_at; [exact B3| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
    rewrite (u32_bytes res) by lia.
    rewrite (guard_true 21) by (apply Z.leb_le; lia).
    rewrite (rd8_known st (aadd ea (-5)) 0) by (eapply known_at; [exact B5| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
    rewrite (guard_true 25) by reflexivity.
    rewrite (guard_true 22) by (apply Z.leb_le; rewrite EA; lia).
    rewrite (rd8_known st (aadd ea (- res)) 0) by (eapply known_at; [apply Kr; lia| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
    rewrite (guard_true 23) by reflexivity.
    rewrite (rd8_known st ea 0) by (eapply known_at; [exact H0| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
    rewrite (guard_true 24) by reflexivity.
    f_equal. rewrite EA. lia.
  - (* [comment removed for export] *)
    replace (Z.min res 5) with res by lia.
    rewrite (guard_true 22) by (apply Z.leb_le; rewrite EA; lia).
    assert (Kr0 : known st (fst c, snd c + get_stride (R m) - IB - res) 0).
    { destruct (Z.eq_dec res 0) as [E0|NE]; [| apply Kr; lia]. rewrite E0, Z.sub_0_r, CF, <- Hst. exact H0. }
    rewrite (rd8_known st (aadd ea (- res)) 0) by (eapply known_at; [exact Kr0| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
    rewrite (guard_true 23) by reflexivity.
    rewrite (rd8_known st ea 0) by (eapply known_at; [exact H0| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
    rewrite (guard_true 24) by reflexivity.
    f_equal. rewrite EA. lia.
Qed.

Lemma free_hdr_eq : free_hdr st p = SRet (Some (wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st), m, i)).
Proof.
  unfold free_hdr. rewrite get_meta_eq. cbv beta zeta.
  unfold slot_start. rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF). cbv beta zeta iota.
  match goal with |- get_nominal_size st p ?e ?k ?b = _ => change (get_nominal_size st p e k b) with (get_nominal_size st p ea k b) end.
  rewrite get_nominal_size_eq. reflexivity.
Qed.
End HDR.
