(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Ops OpsTwin GLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem St HeapOp UO UOT UG.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.

Module UOK.

Lemma kind_untied : forall E w, (match kind_of w with Some kd => (1 <=? kd) && (kd <? 7) | None => false end) = true -> ~ aw_tied (wden E w).
Proof.
  intros E w H. destruct (kind_of w) as [kd|] eqn:KO; [|discriminate]. pose proof (kind_of_sound E w kd KO) as K.
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  unfold aw_tied, K_STACK, K_GHOST. rewrite K. lia.
Qed.
Lemma kind_sub : forall E w, (match kind_of w with Some kd => (2 <=? kd) && (kd <? 7) | None => false end) = true -> K_SUB <= w_kind (wden E w) < K_GHOST.
Proof.
  intros E w H. destruct (kind_of w) as [kd|] eqn:KO; [|discriminate]. rewrite (kind_of_sound E w kd KO).
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold K_SUB, K_GHOST. lia.
Qed.

Lemma kind_new_sub : forall E w (ws' : list window), (match kind_of w with Some kd => (2 <=? kd) && (kd <? 7) | None => false end) = true ->
  ~ aw_tied (wden E w) /\ (w_kind (wden E w) = K_BLOCK ->
     forall g, In g ws' -> K_GHOST <= w_kind g -> forall a, in_iv (w_iv g) a -> ~ in_iv (w_iv (wden E w)) a).
Proof.
  intros E w ws' H. destruct (kind_sub E w H) as [K1 K2]. split; [unfold aw_tied, K_SUB, K_STACK, K_GHOST in *; lia|].
  intros K. exfalso. unfold K_SUB, K_BLOCK in *. lia.
Qed.
Lemma kind_sub_untied : forall E w, (match kind_of w with Some kd => (2 <=? kd) && (kd <? 7) | None => false end) = true ->
  ~ aw_tied (wden E w) /\ w_kind (wden E w) <> K_BLOCK.
Proof. intros E w H. destruct (kind_sub E w H) as [K1 K2]. unfold aw_tied, K_SUB, K_STACK, K_GHOST, K_BLOCK in *. lia. Qed.

Lemma map_replace_old : forall (ws : list (sv * sv * sv)) wold wnew x, In x ws ->
  In x (map (fun w => if win3_eqb w wold then wnew else w) ws) \/ x = wold.
Proof.
  intros ws wold wnew x Hx. destruct (win3_eqb x wold) eqn:Q; [right; exact (win3_eqb_eq _ _ Q)| left].
  apply in_map_iff. exists x. rewrite Q. split; [reflexivity| exact Hx].
Qed.
Lemma filter_old : forall (ws l : list (sv * sv * sv)) f x, In x ws -> In x (List.filter f ws ++ l) \/ f x = false.
Proof.
  intros ws l f x Hx. destruct (f x) eqn:Q; [left| right; reflexivity]. apply in_or_app. left. apply filter_In. split; assumption.
Qed.

Lemma wins_keep_map_intro : forall E LB (ws ws' : list (sv * sv * sv)),
  (forall x, In x ws' -> In x ws \/ (~ aw_tied (wden E x) /\ (w_kind (wden E x) = K_BLOCK ->
       forall g, In g (map (wden E) ws') -> K_GHOST <= w_kind g -> forall a, in_iv (w_iv g) a -> ~ in_iv (w_iv (wden E x)) a))) ->
  (forall x, In x ws -> In x ws' \/ (~ aw_tied (wden E x) /\ (heap_kind (wden E x) -> 0 < w_len (wden E x) ->
       exists o, In o LB /\ in_iv o (w_lo (wden E x)) /\
                 (~ c24 (snd o) \/ exists w', In w' (map (wden E) ws') /\ heap_kind w' /\ 0 < w_len w' /\ in_iv o (w_lo w'))))) ->
  wins_keep LB (map (wden E) ws) (map (wden E) ws').
Proof.
  intros E LB ws ws' NEW OLD. apply wins_keep_intro.
  - intros w Hw. apply in_map_iff in Hw as (x & <- & Hx). destruct (NEW x Hx) as [H0|N]; [left; apply in_map; exact H0| right; exact N].
  - intros w Hw. apply in_map_iff in Hw as (x & <- & Hx). destruct (OLD x Hx) as [H0|R]; [left; apply in_map; exact H0| right; exact R].
Qed.

Lemma block_evidence : forall LB (ws' : list window) (w : window), In (w_iv w) LB -> ~ c24 (w_len w) -> 0 < w_len w ->
  exists o, In o LB /\ in_iv o (w_lo w) /\ (~ c24 (snd o) \/ exists w', In w' ws' /\ heap_kind w' /\ 0 < w_len w' /\ in_iv o (w_lo w')).
Proof.
  intros LB ws' w INB N24 POS. exists (w_iv w). split; [exact INB|]. split; [unfold in_iv, w_iv; cbn [fst snd]; lia| left; exact N24].
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma lv_k_nonneg : forall l, level_valid l -> 0 <= lv_k l.
Proof. intros l (V1 & V2 & _). unfold lv_k. destruct (lv_t l); lia. Qed.

Lemma last_opt_In : forall (A : Type) (l : list A) x, last_opt l = Some x -> In x l.
Proof.
  intros A l x H. unfold last_opt in H. destruct (rev l) as [|y r] eqn:R; [discriminate|]. injection H as ->.
  apply in_rev. rewrite R. left. reflexivity.
Qed.

Lemma in_alloc_owned : forall g a n, pure_ok g -> in_alloc (u_zone g) a n -> 0 < n ->
  forall x, a <= x < a + n -> exists o, In o (owned g) /\ in_iv o x.
Proof.
  intros g a n P IA POS x Hx. destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ZV).
  destruct ZV as (NE & _ & _ & V4 & V5 & V6 & _).
  destruct IA as [(c & Hc & LO & HI)|[LO HI]].
  - exists (chunk_block c). split.
    + right; right. apply in_map. destruct (z_chunks (u_zone g)) as [|h t]; [destruct Hc| right; exact Hc].
    + unfold in_iv, chunk_block, chunk_lo, chunk_hi, CHUNK_HDR in *. cbn [fst snd]. lia.
  - destruct (z_chunks (u_zone g)) as [|h t] eqn:EC; [exfalso; exact (NE eq_refl)|]. cbn [hd] in *.
    exists (chunk_block h). split.
    + right; right. apply in_map. rewrite EC. left. reflexivity.
    + unfold in_iv, chunk_block, chunk_lo, chunk_hi, CHUNK_HDR in *. cbn [fst snd]. lia.
Qed.

Lemma sub_in_owned : forall md g w, pure_ok g -> sub_ok md g w -> 0 < w_len w -> exists o, In o (owned g) /\ in_iv o (w_lo w).
Proof.
  intros md g w P SO POS. pose proof P as (VC & EC & SC & CC & VV & EV & SV & CV & LV & DL & LA & ZV).
  unfold sub_ok in SO. cbv zeta in SO.
  destruct SO as [(_ & B1 & _ & B3)|[(_ & B1 & _ & B3)|[(_ & lD & HlD & I2 & I3)|(_ & Z1 & Z2)]]].
  - exists (cstk_block g). split; [left; reflexivity|]. unfold in_iv, cstk_block, v_capend, v_bytes in *. cbn [fst snd]. lia.
  - exists (vstk_block g). split; [right; left; reflexivity|]. unfold in_iv, vstk_block, v_capend, v_bytes in *. cbn [fst snd]. lia.
  - pose proof (last_opt_In _ _ _ HlD) as INl.
    pose proof (proj1 (Forall_forall _ _) LV lD INl) as VL. pose proof (lv_k_nonneg lD VL) as K0.
    assert (BYTES : 0 < lv_bytes lD).
    { unfold lv_unfilled, lv_slot, OBJ_SIZE in *. destruct (md =? CM_CONS); lia. }
    apply (in_alloc_owned g (lv_P lD) (lv_bytes lD) P (proj1 LA lD INl) BYTES).
    unfold lv_unfilled, lv_slot in *. unfold OBJ_SIZE in *. destruct (md =? CM_CONS); lia.
  - destruct ZV as (NE & _ & _ & V4 & V5 & V6 & _).
    destruct (z_chunks (u_zone g)) as [|h t] eqn:ECH; [exfalso; exact (NE eq_refl)|]. cbn [hd] in *.
    exists (chunk_block h). split; [right; right; apply in_map; rewrite ECH; left; reflexivity|].
    unfold in_iv, chunk_block, chunk_lo, chunk_hi, CHUNK_HDR in *. cbn [fst snd]. lia.
Qed.

Lemma unp_sub_evidence : forall md g LB ws w, pure_ok g -> own_ok g LB -> wins_ok md g ws -> In w ws ->
  K_SUB <= w_kind w < K_GHOST -> 0 < w_len w -> exists o, In o LB /\ in_iv o (w_lo w) /\ ~ c24 (snd o).
Proof.
  intros md g LB ws w P O Wk Hw K POS.
  destruct (proj1 (Forall_forall _ _) Wk w Hw ltac:(unfold K_SUB, K_STACK in *; lia)) as [[[KB|KG] _]|[_ SO]];
    [unfold K_SUB, K_BLOCK in *; lia| unfold K_GHOST in *; lia|].
  destruct (sub_in_owned md g w P SO POS) as (o & Ho & IN). exists o. split; [exact (proj1 O o Ho)|]. split; [exact IN|].
  exact (unp_owned_not_c24 g P o Ho).
Qed.

Definition pseudo (w : window) : Prop := w_kind w = K_STACK /\ AW_BAND <= w_lo w.
Lemma pseudo_untied : forall w, pseudo w -> ~ aw_tied w.
Proof. intros w [K B] [[_ L]|G]; [lia| unfold K_GHOST, K_STACK in *; lia]. Qed.

Lemma pot_map_old : forall E (l l' : list (sv * sv * sv)), (forall x, In x l' -> In x l \/ w_kind (wden E x) <> K_STACK) ->
  forall w, In w (map (wden E) l') -> pot_win w -> In w (map (wden E) l).
Proof.
  intros E l l' HW w Hw (K & _). apply in_map_iff in Hw as (x & <- & Hx). destruct (HW x Hx) as [H0|N]; [apply in_map; exact H0| exfalso; exact (N K)].
Qed.

Lemma unp_wins_keep : forall md g LB ws ws', pure_ok g -> own_ok g LB -> wins_ok md g ws ->
  (forall w, In w ws' -> In w ws \/ (K_SUB <= w_kind w < K_GHOST) \/ (w_kind w = K_BLOCK /\ In (w_iv w) (owned g))) ->
  (forall w, In w ws -> In w ws' \/ (K_SUB <= w_kind w < K_GHOST) \/ (w_kind w = K_BLOCK /\ In (w_iv w) LB /\ ~ c24 (w_len w))) ->
  wins_keep LB ws ws'.
Proof.
  intros md g LB ws ws' P O Wk NEW OLD. apply wins_keep_intro.
  - intros w Hw. destruct (NEW w Hw) as [S|[K|(K & OWN)]]; [left; exact S| right| right].
    + split; [unfold aw_tied, K_SUB, K_STACK, K_GHOST in *; lia|]. intros KB. exfalso. unfold K_SUB, K_BLOCK in *. lia.
    + split; [unfold aw_tied, K_BLOCK, K_STACK, K_GHOST in *; lia|]. intros _ gw Hg KG a Ha Hb.

      assert (Hg0 : In gw ws).
      { destruct (NEW gw Hg) as [S|[K2|(K2 & _)]]; [exact S| exfalso; unfold K_GHOST in *; lia| exfalso; unfold K_GHOST, K_BLOCK in *; lia]. }
      destruct (proj1 (Forall_forall _ _) Wk gw Hg0 ltac:(unfold K_GHOST, K_STACK in *; lia)) as [[_ D]|[_ SO]].
      * exact (D (w_iv w) OWN a Ha Hb).
      * unfold sub_ok in SO. cbv zeta in SO. unfold K_CTOP, K_VTOP, K_SLOT, K_ZONE, K_GHOST in *.
        destruct SO as [(KK & _)|[(KK & _)|[(KK & _)|(KK & _)]]]; lia.
  - intros w Hw. destruct (OLD w Hw) as [S|[K|(K & INB & N24)]]; [left; exact S| right| right].
    + split; [unfold aw_tied, K_SUB, K_STACK, K_GHOST in *; lia|]. intros _ POS.
      destruct (unp_sub_evidence md g LB ws w P O Wk Hw K POS) as (o & Ho & IN & N24). exists o. split; [exact Ho|]. split; [exact IN| left; exact N24].
    + split; [unfold aw_tied, K_BLOCK, K_STACK, K_GHOST in *; lia|]. intros _ POS.
      exists (w_iv w). split; [exact INB|]. split; [unfold in_iv, w_iv; cbn [fst snd]; lia| left; exact N24].
Qed.

Lemma unp_wins_keep_map : forall E md g LB (ws ws' : list (sv * sv * sv)), pure_ok g -> own_ok g LB -> wins_ok md g (map (wden E) ws) ->
  (forall x, In x ws' -> In x ws \/ (K_SUB <= w_kind (wden E x) < K_GHOST) \/ (w_kind (wden E x) = K_BLOCK /\ In (w_iv (wden E x)) (owned g))) ->
  (forall x, In x ws -> In x ws' \/ (K_SUB <= w_kind (wden E x) < K_GHOST)
                        \/ (w_kind (wden E x) = K_BLOCK /\ In (w_iv (wden E x)) LB /\ ~ c24 (w_len (wden E x)))) ->
  wins_keep LB (map (wden E) ws) (map (wden E) ws').
Proof.
  intros E md g LB ws ws' P O Wk NEW OLD. apply (unp_wins_keep md g LB _ _ P O Wk).
  - intros w Hw. apply in_map_iff in Hw as (x & <- & Hx). destruct (NEW x Hx) as [H0|R]; [left; apply in_map; exact H0| right; exact R].
  - intros w Hw. apply in_map_iff in Hw as (x & <- & Hx). destruct (OLD x Hx) as [H0|R]; [left; apply in_map; exact H0| right; exact R].
Qed.

Lemma sub_in_owned_all : forall md g w, pure_ok g -> sub_ok md g w -> forall a, in_iv (w_iv w) a -> exists o, In o (owned g) /\ in_iv o a.
Proof.
  intros md g w P SO a Ha. pose proof P as (VC & EC & SC & CC & VV & EV & SV & CV & LV & DL & LA & ZV).
  unfold sub_ok in SO. cbv zeta in SO. unfold in_iv, w_iv in Ha. cbn [fst snd] in Ha.
  destruct SO as [(_ & B1 & _ & B3)|[(_ & B1 & _ & B3)|[(_ & lD & HlD & I2 & I3)|(_ & Z1 & Z2)]]].
  - exists (cstk_block g). split; [left; reflexivity|]. unfold in_iv, cstk_block, v_capend, v_bytes in *. cbn [fst snd]. lia.
  - exists (vstk_block g). split; [right; left; reflexivity|]. unfold in_iv, vstk_block, v_capend, v_bytes in *. cbn [fst snd]. lia.
  - pose proof (last_opt_In _ _ _ HlD) as INl.
    pose proof (proj1 (Forall_forall _ _) LV lD INl) as VL. pose proof (lv_k_nonneg lD VL) as K0.
    assert (BYTES : 0 < lv_bytes lD).
    { unfold lv_unfilled, lv_slot, OBJ_SIZE in *. destruct (md =? CM_CONS); lia. }
    apply (in_alloc_owned g (lv_P lD) (lv_bytes lD) P (proj1 LA lD INl) BYTES).
    unfold lv_unfilled, lv_slot in *. unfold OBJ_SIZE in *. destruct (md =? CM_CONS); lia.
  - destruct ZV as (NE & _ & _ & V4 & V5 & V6 & _).
    destruct (z_chunks (u_zone g)) as [|h t] eqn:ECH; [exfalso; exact (NE eq_refl)|]. cbn [hd] in *.
    exists (chunk_block h). split; [right; right; apply in_map; rewrite ECH; left; reflexivity|].
    unfold in_iv, chunk_block, chunk_lo, chunk_hi, CHUNK_HDR in *. cbn [fst snd]. lia.
Qed.

Lemma cw_unp_sub_ghost : forall XW md ca LB ws m w gw a, cw_unp_holds segs XW md ca LB ws m -> (md = CM_NONE \/ md = CM_UNP \/ md = CM_CONS) ->
  In w ws -> In gw ws -> K_SUB <= w_kind w < K_GHOST -> K_GHOST <= w_kind gw -> in_iv (w_iv w) a -> in_iv (w_iv gw) a -> False.
Proof.
  intros XW md ca LB ws m w gw a H MD Hw Hg KS KG Ia Ig. unfold cw_unp_holds in H.
  destruct MD as [->|MD].
  - cbn [CM_NONE Z.eqb] in H. exact (proj1 (Forall_forall _ _) H w Hw KS).
  - assert (M0 : (md =? CM_NONE) = false) by (apply Z.eqb_neq; unfold CM_NONE, CM_UNP, CM_CONS in *; lia). rewrite M0 in H.
    assert (M1 : ((md =? CM_UNP) || (md =? CM_CONS)) = true) by (apply orb_true_iff; destruct MD as [->| ->]; [left| right]; apply Z.eqb_refl). rewrite M1 in H.
    destruct (decode_uc ca) as [u|]; [| contradiction].
    destruct H as (g & L & P & O & Wk & _).
    destruct (proj1 (Forall_forall _ _) Wk w Hw ltac:(unfold K_SUB, K_STACK in *; lia)) as [[[KB|KG'] _]|[_ SO]];
      [unfold K_SUB, K_BLOCK in *; lia| unfold K_GHOST in *; lia|].
    destruct (sub_in_owned_all md g w P SO a Ia) as (o & Ho & INo).
    destruct (proj1 (Forall_forall _ _) Wk gw Hg ltac:(unfold K_GHOST, K_STACK in *; lia)) as [[_ DJ]|[_ SOg]].
    + exact (DJ o Ho a Ig INo).
    + unfold sub_ok in SOg. cbv zeta in SOg.
      destruct SOg as [(KK & _)|[(KK & _)|[(KK & _)|(KK & _)]]]; unfold K_CTOP, K_VTOP, K_SLOT, K_ZONE, K_GHOST in *; lia.
Qed.

End WithSegs.
End UOK.
