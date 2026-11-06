(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Shadow
  MI_Pres1 MI_Pres2 MI_Read MI_WFree MI_WFree2 MI_WGroup MI_Cnt MI_TF2 MI_WEnframe MI_WEnframe2 MI_WMalloc MI_WRelay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ss_list (c : cptr) (off n stride i : Z) : list (aptr * Z) :=
  let p := snd c + UNIT * off in
  let e := snd c + stride - IB in
  let res := e - p - n in
  (if res =? 0 then [] else [((fst c, e - res), 0)])
  ++ (if 5 <=? res then [((fst c, e - 5), 0); ((fst c, e - 4), res); ((fst c, e - 3), Z.shiftr res 8);
                         ((fst c, e - 2), Z.shiftr res 16); ((fst c, e - 1), Z.shiftr res 24)] else [])
  ++ [((fst c, p - 3), i + 32 * Z.min res 5)].

Section SET_SIZE.
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (c : cptr) (off n n' : Z).
Variables (m bm : aptr) (i ai : Z) (a : aptr) (ar : area) (ka : Z).
Hypothesis INV : INVL x0 st L BL LS.
Hypothesis Hk : In ((c, off), n) BL.
Hypothesis BF : blk_facts st c off n m bm i ai a ar ka.
Hypothesis Hn' : 0 <= n'.
Hypothesis Hfit' : UNIT * off + n' <= get_stride (MR st m) - IB.
Hypothesis SC : m_sizeclass (MR st m) < 48.
Let stride := get_stride (MR st m).
Let W := ss_list c off n' stride i.
Let p := snd c + UNIT * off.
Let e := snd c + stride - IB.
Let res := e - p - n'.

Lemma ss_stride : 16 <= stride < 2 ^ 20 /\ stride mod 16 = 0.
Proof.
  pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S1 S2]. fold stride in S1, S2.
  pose proof (small_stride x0 st L BL LS bm m INV (ex_intro _ ai (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) SC). fold stride in H.
  unfold UNIT in *. lia.
Qed.

Lemma ss_c16 : snd c mod 16 = 0.
Proof.
  rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF). cbn [snd]. unfold sstart. rewrite (MI_WFree.gbase_bm st c off n m bm i ai a ar ka BF).
  pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S1 S2]. pose proof (bf_b16 _ _ _ _ _ _ _ _ _ _ _ BF) as [B1 B2].
  unfold UNIT in *.
  pose proof (Z.div_mod (get_stride (MR st m)) 16 ltac:(lia)). pose proof (Z.div_mod (snd bm) 16 ltac:(lia)).
  rewrite S2 in H. rewrite B2 in H0.
  replace (snd bm + 16 + get_stride (MR st m) * i) with ((snd bm / 16 + 1 + get_stride (MR st m) / 16 * i) * 16) by lia.
  apply Z_mod_mult.
Qed.

Lemma ss_addrs q : In q (map fst W) ->
  fst q = fst c /\ snd c - 3 <= snd q < snd c + stride - 4 /\ ~ (snd c + UNIT * off <= snd q < snd c + UNIT * off + n').
Proof.
  intros Hin. pose proof ss_stride as [S16 _]. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as OFF.
  unfold W, ss_list in Hin. fold stride in Hin.
  destruct (Z.eqb_spec (snd c + stride - IB - (snd c + UNIT * off) - n') 0) as [R0|R0];
  destruct (Z.leb_spec 5 (snd c + stride - IB - (snd c + UNIT * off) - n')) as [R5|R5];
    cbn [app map fst In] in Hin; unfold IB, UNIT in *;
    repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end; cbn [fst snd]; (split; [reflexivity| lia]).
Qed.

Ltac ss_aeq :=
  match goal with
  | |- context [aptr_eqb ?x ?y] =>
      first [ rewrite (aptr_eqb_neq x y) by (cbn [fst snd]; intros E; apply (f_equal snd) in E; cbn [snd] in E; unfold IB, UNIT in *; lia)
            | rewrite (proj2 (aptr_eqb_eq x y)) by (cbn [fst snd]; unfold IB, UNIT in *; f_equal; lia) ]
  end.

Lemma ss_shadow_ok : blk_shadow_ok (relay st W c off n') ((c, off), n') m i.
Proof.
  pose proof ss_stride as [S16 SM]. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as OFF. pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi.
  pose proof (bf_li _ _ _ _ _ _ _ _ _ _ _ BF) as LI.
  pose proof (TKS_of _ _ _ _ _ INV) as TK. pose proof ss_c16 as C16.
  assert (WNU : forall q, In q (map fst W) -> ~ (fst q = fst c /\ snd c + UNIT * off <= snd q < snd c + UNIT * off + n')).
  { intros q Hq [_ R]. destruct (ss_addrs q Hq) as (_ & _ & NR). exact (NR R). }
  destruct (relay_ctrl st W c off n') as [CE _].
  assert (MRE : MR (relay st W c off n') m = MR st m) by (apply MR_ext; exact (ce_metas _ _ CE)).
  destruct (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as (K4 & K3 & K2 & K1 & QR & _ & _ & _). cbn [bslot boff bsize fst snd] in K4, K3, K2, K1, QR.
  unfold blk_shadow_ok. cbn [bslot boff bsize fst snd]. rewrite MRE. fold stride. fold stride in Hfit'.
  assert (R0 : 0 <= snd c + stride - IB - (snd c + UNIT * off) - n') by (unfold IB, UNIT in *; lia).
  assert (R32 : snd c + stride - IB - (snd c + UNIT * off) - n' < 2 ^ 32) by (unfold IB, UNIT in *; lia).
  set (rs := snd c + stride - IB - (snd c + UNIT * off) - n') in *.
  assert (NP : forall x, x < snd c + UNIT * off \/ snd c + UNIT * off + n' <= x ->
               ~ (snd (aadd c (UNIT * off)) <= x < snd (aadd c (UNIT * off)) + n')) by (unfold aadd; cbn [snd]; intros; lia).
  assert (NPq : forall q, snd q < snd c + UNIT * off \/ snd c + UNIT * off + n' <= snd q ->
               ~ (fst q = fst c /\ snd (aadd c (UNIT * off)) <= snd q < snd (aadd c (UNIT * off)) + n')) by (unfold aadd; cbn [snd]; intros q Hq [_ R]; lia).
  assert (EW : W = (if rs =? 0 then [] else [((fst c, snd c + stride - IB - rs), 0)])
                   ++ (if 5 <=? rs then [((fst c, snd c + stride - IB - 5), 0); ((fst c, snd c + stride - IB - 4), rs); ((fst c, snd c + stride - IB - 3), Z.shiftr rs 8);
                                         ((fst c, snd c + stride - IB - 2), Z.shiftr rs 16); ((fst c, snd c + stride - IB - 1), Z.shiftr rs 24)] else [])
                   ++ [((fst c, snd c + UNIT * off - 3), i + 32 * Z.min rs 5)]) by reflexivity.
  split; [| split; [| split; [| split; [| split; [exact QR| split; [| split]]]]]].
  - (* [comment removed for export] *) apply (relay_known_old st W c off n' TK C16 (fst c, snd c + UNIT * off - 4)); [apply NPq; cbn [snd]; lia| | exact K4].
    rewrite EW. destruct (rs =? 0); destruct (5 <=? rs); cbn [app lastw]; repeat ss_aeq; reflexivity.
  - (* [comment removed for export] *)
    assert (L255 : Z.land (i + 32 * Z.min rs 5) 255 = i + 32 * Z.min rs 5)
      by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; apply Z.mod_small; lia).
    rewrite <- L255.
    apply (relay_known_w st W c off n' TK C16); [apply NP; lia|].
    rewrite EW. destruct (rs =? 0); destruct (5 <=? rs); cbn [app lastw]; repeat ss_aeq; reflexivity.
  - (* [comment removed for export] *) apply (relay_known_old st W c off n' TK C16 (fst c, snd c + UNIT * off - 2)); [apply NPq; cbn [snd]; lia| | exact K2].
    rewrite EW. destruct (Z.eqb_spec rs 0); destruct (Z.leb_spec 5 rs); cbn [app lastw]; repeat ss_aeq; reflexivity.
  - (* [comment removed for export] *) apply (relay_known_old st W c off n' TK C16 (fst c, snd c + UNIT * off - 1)); [apply NPq; cbn [snd]; lia| | exact K1].
    rewrite EW. destruct (Z.eqb_spec rs 0); destruct (Z.leb_spec 5 rs); cbn [app lastw]; repeat ss_aeq; reflexivity.
  - (* [comment removed for export] *) intros R5. unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.mul_1_r.
    assert (E5 : (5 <=? rs) = true) by (apply Z.leb_le; exact R5).
    assert (EZ : (rs =? 0) = false) by (apply Z.eqb_neq; lia).
    split; [| split; [| split; [| split; [| split; [| exact R32]]]]].
    1-4: apply (relay_known_w st W c off n' TK C16); [apply NP; unfold IB, UNIT in *; lia|];
         rewrite EW, E5, EZ; cbn [app lastw]; repeat ss_aeq; try reflexivity.
    all: try (change (8 * 2) with 16; reflexivity). all: try (change (8 * 3) with 24; reflexivity).
    apply (relay_known_w st W c off n' TK C16 _ 0); [apply NP; unfold IB, UNIT in *; lia|].
    rewrite EW, E5, EZ; cbn [app lastw]; repeat ss_aeq; reflexivity.
  - (* [comment removed for export] *) intros RP.
    assert (EZ : (rs =? 0) = false) by (apply Z.eqb_neq; lia).
    apply (relay_known_w st W c off n' TK C16 _ 0); [apply NP; unfold IB, UNIT in *; lia|].
    rewrite EW, EZ. destruct (Z.leb_spec 5 rs); [destruct (Z.eq_dec rs 5)|]; cbn [app lastw]; repeat ss_aeq; reflexivity.
  - (* [comment removed for export] *) intros x Hx. apply (relay_unknown st W c off n' TK C16 WNU). unfold aadd. cbn [snd]. exact Hx.
Qed.

(* [comment removed for export] *)
Hypothesis HCLS' : 27 <= m_sizeclass (MR st m) -> 2028 < n'.

Theorem relay_ok_set_size : relay_ok st c W off n'.
Proof.
  exists m, i. split; [exact (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF)|]. split; [exact SC|]. split; [exact HCLS'|].
  split; [exact (bf_off _ _ _ _ _ _ _ _ _ _ _ BF)|]. split; [exact Hn'|]. split; [exact Hfit'|].
  split; [exact ss_addrs| exact ss_shadow_ok].
Qed.
End SET_SIZE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition aa_list (c : cptr) (off' n stride i q : Z) : list (aptr * Z) :=
  let p := snd c + UNIT * off' in
  let e := snd c + stride - IB in
  let res := e - p - n in
  [((fst c, p - 4), 0); ((fst c, p - 3), i); ((fst c, p - 2), q); ((fst c, p - 1), Z.shiftr q 8)]
  ++ (if res =? 0 then [] else [((fst c, e - res), 0)])
  ++ (if 5 <=? res then [((fst c, e - 5), 0); ((fst c, e - 4), res); ((fst c, e - 3), Z.shiftr res 8);
                         ((fst c, e - 2), Z.shiftr res 16); ((fst c, e - 1), Z.shiftr res 24)] else [])
  ++ [((fst c, p - 3), i + 32 * Z.min res 5); ((fst c, snd c - 3), 224); ((fst c, snd c - 2), off'); ((fst c, snd c - 1), Z.shiftr off' 8)].

Ltac aa_aeq :=
  match goal with
  | |- context [aptr_eqb ?x ?y] =>
      first [ rewrite (aptr_eqb_neq x y) by (cbn [fst snd]; intros E; apply (f_equal snd) in E; cbn [snd] in E; unfold IB, UNIT in *; lia)
            | rewrite (proj2 (aptr_eqb_eq x y)) by (cbn [fst snd]; unfold IB, UNIT in *; f_equal; lia) ]
  end.

Section AALIGN.
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (c : cptr) (off n off' n' : Z).
Variables (m bm : aptr) (i ai : Z) (a : aptr) (ar : area) (ka : Z).
Hypothesis INV : INVL x0 st L BL LS.
Hypothesis Hk : In ((c, off), n) BL.
Hypothesis BF : blk_facts st c off n m bm i ai a ar ka.
Hypothesis Hoff' : 1 <= off' <= 258.
Hypothesis Hn' : 0 <= n'.
Hypothesis Hfit' : UNIT * off' + n' <= get_stride (MR st m) - IB.
Hypothesis SC : m_sizeclass (MR st m) < 48.
Let stride := get_stride (MR st m).
Definition aa_q : Z := (snd c + UNIT * off' - (snd bm + UNIT)) / UNIT.
Let W := aa_list c off' n' stride i aa_q.
Let p := snd c + UNIT * off'.
Let e := snd c + stride - IB.
Let res := e - p - n'.

Lemma aa_stride : 16 <= stride < 2 ^ 20 /\ stride mod 16 = 0 /\ stride * (i + 1) <= stride * (m_last_idx (MR st m) + 1) < 2 ^ 20.
Proof.
  pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S1 S2]. fold stride in S1, S2.
  pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi.
  pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) as GO.
  destruct (g_stride _ _ _ _ _ _ GO SC) as (_ & _ & LT). unfold cnt_of in LT. fold stride in LT.
  assert (M : stride * (i + 1) <= stride * (m_last_idx (MR st m) + 1)) by (apply Z.mul_le_mono_nonneg_l; unfold UNIT in *; lia).
  unfold UNIT in *. lia.
Qed.

Lemma aa_q_facts : UNIT * aa_q = stride * i + UNIT * off' /\ 0 <= aa_q < 2 ^ 16.
Proof.
  pose proof aa_stride as (S16 & SM & SPAN & LT). pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi.
  unfold aa_q. rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF). cbn [snd]. unfold sstart. rewrite (MI_WFree.gbase_bm st c off n m bm i ai a ar ka BF). fold stride.
  pose proof (Z.div_mod stride 16 ltac:(lia)) as DM. rewrite SM in DM. set (s := stride / 16) in *.
  assert (E : stride = 16 * s) by lia.
  replace (snd bm + UNIT + stride * i + UNIT * off' - (snd bm + UNIT)) with ((s * i + off') * UNIT) by (unfold UNIT; rewrite E; ring).
  unfold UNIT. rewrite Z.div_mul by lia.
  assert (0 <= s * i) by (apply Z.mul_nonneg_nonneg; lia).
  assert (E1 : stride * i = 16 * (s * i)) by (rewrite E; ring).
  assert (E2 : stride * (i + 1) = stride * i + stride) by ring.
  unfold IB, UNIT in Hfit'. fold stride in Hfit'. lia.
Qed.

Lemma aa_c16 : snd c mod 16 = 0.
Proof. exact (ss_c16 st c off n 0 m bm i ai a ar ka BF). Qed.

Lemma aa_addrs x : In x (map fst W) ->
  fst x = fst c /\ snd c - 3 <= snd x < snd c + stride - 4 /\ ~ (snd c + UNIT * off' <= snd x < snd c + UNIT * off' + n').
Proof.
  intros Hin. pose proof aa_stride as (S16 & _).
  unfold W, aa_list in Hin. fold stride in Hin.
  destruct (Z.eqb_spec (snd c + stride - IB - (snd c + UNIT * off') - n') 0) as [R0|R0];
  destruct (Z.leb_spec 5 (snd c + stride - IB - (snd c + UNIT * off') - n')) as [R5|R5];
    cbn [app map fst In] in Hin; unfold IB, UNIT in *;
    repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end; cbn [fst snd]; (split; [reflexivity| lia]).
Qed.

Lemma aa_shadow_ok : blk_shadow_ok (relay st W c off' n') ((c, off'), n') m i.
Proof.
  pose proof aa_stride as (S16 & SM & _ & _). pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi.
  pose proof (bf_li _ _ _ _ _ _ _ _ _ _ _ BF) as LI.
  pose proof (TKS_of _ _ _ _ _ INV) as TK. pose proof aa_c16 as C16. pose proof aa_q_facts as [Q16 QR].
  assert (WNU : forall x, In x (map fst W) -> ~ (fst x = fst c /\ snd c + UNIT * off' <= snd x < snd c + UNIT * off' + n')).
  { intros x Hx [_ R]. destruct (aa_addrs x Hx) as (_ & _ & NR). exact (NR R). }
  destruct (relay_ctrl st W c off' n') as [CE _].
  assert (MRE : MR (relay st W c off' n') m = MR st m) by (apply MR_ext; exact (ce_metas _ _ CE)).
  unfold blk_shadow_ok. cbn [bslot boff bsize fst snd]. rewrite MRE. fold stride. fold stride in Hfit'.
  rewrite (MI_WFree.gbase_bm st c off n m bm i ai a ar ka BF).
  replace ((snd c + UNIT * off' - snd bm - UNIT) / UNIT) with aa_q by (unfold aa_q; f_equal; lia).
  assert (R0 : 0 <= snd c + stride - IB - (snd c + UNIT * off') - n') by (unfold IB, UNIT in *; lia).
  assert (R32 : snd c + stride - IB - (snd c + UNIT * off') - n' < 2 ^ 32) by (unfold IB, UNIT in *; lia).
  set (rs := snd c + stride - IB - (snd c + UNIT * off') - n') in *.
  assert (NP : forall x, x < snd c + UNIT * off' \/ snd c + UNIT * off' + n' <= x ->
               ~ (snd (aadd c (UNIT * off')) <= x < snd (aadd c (UNIT * off')) + n')) by (unfold aadd; cbn [snd]; intros; lia).
  assert (EW : W = [((fst c, snd c + UNIT * off' - 4), 0); ((fst c, snd c + UNIT * off' - 3), i); ((fst c, snd c + UNIT * off' - 2), aa_q); ((fst c, snd c + UNIT * off' - 1), Z.shiftr aa_q 8)]
                   ++ (if rs =? 0 then [] else [((fst c, snd c + stride - IB - rs), 0)])
                   ++ (if 5 <=? rs then [((fst c, snd c + stride - IB - 5), 0); ((fst c, snd c + stride - IB - 4), rs); ((fst c, snd c + stride - IB - 3), Z.shiftr rs 8);
                                         ((fst c, snd c + stride - IB - 2), Z.shiftr rs 16); ((fst c, snd c + stride - IB - 1), Z.shiftr rs 24)] else [])
                   ++ [((fst c, snd c + UNIT * off' - 3), i + 32 * Z.min rs 5); ((fst c, snd c - 3), 224); ((fst c, snd c - 2), off'); ((fst c, snd c - 1), Z.shiftr off' 8)]) by reflexivity.
  split; [| split; [| split; [| split; [| split; [exact QR| split; [| split]]]]]].
  - (* [comment removed for export] *) apply (relay_known_w st W c off' n' TK C16 _ 0); [apply NP; lia|].
    rewrite EW. destruct (Z.eqb_spec rs 0); destruct (Z.leb_spec 5 rs); try (exfalso; lia); cbn [app lastw]; repeat aa_aeq; reflexivity.
  - (* [comment removed for export] *)
    assert (L255 : Z.land (i + 32 * Z.min rs 5) 255 = i + 32 * Z.min rs 5)
      by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; apply Z.mod_small; lia).
    rewrite <- L255.
    apply (relay_known_w st W c off' n' TK C16); [apply NP; lia|].
    rewrite EW. destruct (Z.eqb_spec rs 0); destruct (Z.leb_spec 5 rs); try (exfalso; lia); cbn [app lastw]; repeat aa_aeq; reflexivity.
  - (* [comment removed for export] *) unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r.
    apply (relay_known_w st W c off' n' TK C16); [apply NP; lia|].
    rewrite EW. destruct (Z.eqb_spec rs 0); destruct (Z.leb_spec 5 rs); try (exfalso; lia); cbn [app lastw]; repeat aa_aeq; reflexivity.
  - (* [comment removed for export] *) unfold byte_of. rewrite Z.mul_1_r.
    apply (relay_known_w st W c off' n' TK C16); [apply NP; lia|].
    rewrite EW. destruct (Z.eqb_spec rs 0); destruct (Z.leb_spec 5 rs); try (exfalso; lia); cbn [app lastw]; repeat aa_aeq; reflexivity.
  - (* [comment removed for export] *) intros R5. unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.mul_1_r.
    assert (E5 : (5 <=? rs) = true) by (apply Z.leb_le; exact R5).
    assert (EZ : (rs =? 0) = false) by (apply Z.eqb_neq; lia).
    split; [| split; [| split; [| split; [| split; [| exact R32]]]]].
    1-4: apply (relay_known_w st W c off' n' TK C16); [apply NP; unfold IB, UNIT in *; lia|];
         rewrite EW, E5, EZ; cbn [app lastw]; repeat aa_aeq; try reflexivity.
    all: try (change (8 * 2) with 16; reflexivity). all: try (change (8 * 3) with 24; reflexivity).
    apply (relay_known_w st W c off' n' TK C16 _ 0); [apply NP; unfold IB, UNIT in *; lia|].
    rewrite EW, E5, EZ; cbn [app lastw]; repeat aa_aeq; reflexivity.
  - (* [comment removed for export] *) intros RP.
    assert (EZ : (rs =? 0) = false) by (apply Z.eqb_neq; lia).
    apply (relay_known_w st W c off' n' TK C16 _ 0); [apply NP; unfold IB, UNIT in *; lia|].
    rewrite EW, EZ. destruct (Z.leb_spec 5 rs); [destruct (Z.eq_dec rs 5)|]; cbn [app lastw]; repeat aa_aeq; reflexivity.
  - (* [comment removed for export] *) intros x Hx. apply (relay_unknown st W c off' n' TK C16 WNU). unfold aadd. cbn [snd]. exact Hx.
Qed.

(* [comment removed for export] *)
Hypothesis HCLS' : 27 <= m_sizeclass (MR st m) -> 2028 < n'.

Theorem relay_ok_aalign : relay_ok st c W off' n'.
Proof.
  exists m, i. split; [exact (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF)|]. split; [exact SC|]. split; [exact HCLS'|].
  split; [lia|]. split; [exact Hn'|]. split; [exact Hfit'|].
  split; [exact aa_addrs| exact aa_shadow_ok].
Qed.
End AALIGN.
