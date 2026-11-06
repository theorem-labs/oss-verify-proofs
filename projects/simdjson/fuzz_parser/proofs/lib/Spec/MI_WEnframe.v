(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import STree Malloc KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Shadow
  MI_Pres1 MI_Pres2 MI_Read MI_WFree2 MI_WGroup MI_Cnt MI_TF2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fold_f (s : Z) : bool := forallb (fun off => negb (s <? off) || ((0 <=? fold_off off s) && (fold_off off s <=? s))) (zrange 0 256).
Lemma fold_all : forallb fold_f (zrange 0 256) = true. Proof. vm_compute. reflexivity. Qed.

Lemma fold_off_le off slack : 0 <= off < 256 -> 0 <= slack -> 0 <= fold_off off slack <= slack.
Proof.
  intros Ho Hs. destruct (Z.ltb_spec slack off) as [LT|GE].
  - pose proof (forallb_zrange fold_f 0 256 slack fold_all ltac:(lia) ltac:(lia)) as H. unfold fold_f in H.
    pose proof (forallb_zrange _ 0 256 off H ltac:(lia) ltac:(lia)) as H2. cbn beta in H2.
    replace (slack <? off) with true in H2 by (symmetry; apply Z.ltb_lt; exact LT). cbn in H2.
    apply andb_true_iff in H2 as [A B]. apply Z.leb_le in A. apply Z.leb_le in B. lia.
  - unfold fold_off. replace (slack <? off) with false by (symmetry; apply Z.ltb_ge; exact GE). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma s_shadow_havoc p n st : 0 < n ->
  s_shadow (havoc p n st) = <[fst p := get_shadow (havoc p n st) (fst p)]> (s_shadow st).
Proof.
  intros Hn. unfold havoc at 1. replace (n <=? 0) with false by (symmetry; apply Z.leb_gt; lia). unfold upd_shadow. cbn -[havoc get_shadow Z.add Z.mul Z.div Z.ltb].
  f_equal. unfold havoc. replace (n <=? 0) with false by (symmetry; apply Z.leb_gt; lia). rewrite get_shadow_upd_shadow, N.eqb_refl. reflexivity.
Qed.

Lemma TKS_havoc p n st : snd p mod 16 = 0 -> 0 < n -> TKS st (s_tick st) -> TKS (havoc p n st) (s_tick st).
Proof.
  intros Al Hn TK rid sh. rewrite s_shadow_havoc by exact Hn.
  destruct (N.eq_dec rid (fst p)) as [->|NE]; [| rewrite lookup_insert_ne by congruence; apply TK].
  rewrite lookup_insert_eq. intros E. inversion E. subst sh. clear E.
  pose proof (sh_ticks_of st (fst p) TK) as [T1 T2].
  destruct (havoc_ticks p n st Hn ltac:(intros u hl Hu ch Hch; exact (T1 u hl ch Hu Hch)) (fst p)
              ltac:(intros u hl Hu ch Hch; exact (T1 u hl ch Hu Hch)) T2) as [A B].
  split; [| split; [intros u hl ch Hu Hch; exact (A u hl Hu ch Hch)| exact B]].
  rewrite havoc_cells by exact Hn. unfold get_shadow. destruct (s_shadow st !! fst p) as [sh0|] eqn:E0; cbn.
  - exact (proj1 (TK _ _ E0)).
  - intros o w t Ho. rewrite lookup_empty in Ho. discriminate.
Qed.

Lemma DOMS_havoc st0 p n st : 0 < n -> DOMS st0 st -> (exists r, s_regions st0 !! fst p = Some r /\ r_kind r = RKGroup) -> DOMS st0 (havoc p n st).
Proof.
  intros Hn D Hp rid sh. rewrite s_shadow_havoc by exact Hn.
  destruct (N.eq_dec rid (fst p)) as [->|NE]; [intros _; exact Hp|]. rewrite lookup_insert_ne by congruence. apply D.
Qed.

Lemma havoc_ctrl p n st : ctrl_eq st (havoc p n st) /\ s_tick (havoc p n st) = s_tick st.
Proof. unfold havoc. destruct (n <=? 0); [split; [apply ctrl_eq_refl| reflexivity]|]. split; [constructor; reflexivity| reflexivity]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section EF.
Variables (st : mstate) (g : aptr) (idx n off : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let gm := default (0%N, 0) (m_mem mr).
Let c : aptr := aadd gm (UNIT + stride * idx).
Let e : aptr := aadd c (stride - IB).
Let p0 : aptr := if off =? 0 then c else aadd c (UNIT * off).
Let res := snd e - snd p0 - n.
Let q := (snd p0 - (snd gm + UNIT)) / UNIT.

Definition ef_list : list (aptr * Z) :=
  (if negb (off =? 0) then [(aadd c (-2), off); (aadd (aadd c (-2)) 1, Z.shiftr off 8); (aadd c (-3), 224); (aadd p0 (-4), 0)] else [])
  ++ [(aadd p0 (-2), q); (aadd (aadd p0 (-2)) 1, Z.shiftr q 8); (aadd p0 (-3), idx)]
  ++ (if negb (res =? 0) then [(aadd e (- res), 0)] else [])
  ++ (if 5 <=? res then [(aadd e (-4), res); (aadd (aadd e (-4)) 1, Z.shiftr res 8); (aadd (aadd e (-4)) 2, Z.shiftr res 16); (aadd (aadd e (-4)) 3, Z.shiftr res 24); (aadd e (-5), 0)] else [])
  ++ [(aadd p0 (-3), Z.land idx 31 + Z.shiftl (if 5 <=? res then 5 else res) 5)].

Lemma enframe_at_eq : enframe_at st g idx n off = (wrs ef_list st, p0).
Proof.
  unfold enframe_at, set_size, ef_list. unfold q, res, p0, e, c, gm, stride, mr.
  (* [comment removed for export] *)
  destruct (off =? 0); cbn beta iota delta [negb];
    match goal with |- context [if negb (?x =? 0) then _ else _] => destruct (x =? 0) end; cbn beta iota delta [negb];
    match goal with |- context [if 5 <=? ?x then _ else _] => destruct (5 <=? x) end; cbn beta iota delta [wr16 wr32 wrs app negb]; reflexivity.
Qed.

Lemma p0_eq : p0 = aadd c (UNIT * off).
Proof. unfold p0. destruct (Z.eqb_spec off 0) as [->|]; [| reflexivity]. unfold c, aadd. cbn. f_equal. lia. Qed.
End EF.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint lastw (l : list (aptr * Z)) (r : aptr) (acc : option Z) : option Z :=
  match l with
  | [] => acc
  | (a, v) :: l' => lastw l' r (if aptr_eqb a r then Some v else acc)
  end.

Lemma lastw_acc l r v : lastw l r (Some v) = match lastw l r None with Some w => Some w | None => Some v end.
Proof.
  revert v. induction l as [|[a w] l IH]; intros v; cbn; [reflexivity|].
  destruct (aptr_eqb a r); [| apply IH]. rewrite !(IH w). destruct (lastw l r None); reflexivity.
Qed.

Lemma wrs_lastw l : forall st r, TKS st (s_tick st) ->
  cell_read (get_shadow (wrs l st) (fst r)) (snd r) =
  match lastw l r None with Some w => Known (Z.land w 255) | None => cell_read (get_shadow st (fst r)) (snd r) end.
Proof.
  induction l as [|[a v] l IH]; intros st r TK; cbn [wrs lastw]; [reflexivity|].
  rewrite IH by (apply TKS_wr8; [cbn; lia| exact TK]).
  destruct (aptr_eqb_spec a r) as [<-|NE].
  - rewrite lastw_acc. destruct (lastw l a None); [reflexivity|]. apply cell_read_wr8_same. apply sh_ticks_of. exact TK.
  - destruct (lastw l r None); [reflexivity|]. apply cell_read_wr8_other. congruence.
Qed.

Lemma known_range X st L BL LS q v : INVL X st L BL LS -> cell_read (get_shadow st (fst q)) (snd q) = Known v -> 0 <= v < 256.
Proof.
  intros INV H. eapply known_byte; [| exact H]. intros sh o' v' t Hs Hc. exact (proj1 (proj1 (TKS_of _ _ _ _ _ INV _ _ Hs) o' v' t Hc)).
Qed.

Lemma havoc_0 p st : havoc p 0 st = st.
Proof. reflexivity. Qed.

Lemma land255_range a : 0 <= Z.land a 255 < 256.
Proof.
  split; [apply Z.land_nonneg; right; lia|].
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.
