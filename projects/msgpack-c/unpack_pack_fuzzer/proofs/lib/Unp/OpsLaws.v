(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val Mem State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Ops Seal SealX OpsTwin OpsKeep.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import HeapOp UO.
Open Scope Z_scope.
Unset Lia Cache.

Module UOL.
Section WithSegs.
Variable segs : list Segment.
Variable XW : client_world.
Local Abbreviation cwh := (cw_unp_holds segs XW).

Hypothesis XW_sub_ghost : forall md ca LB ws m w g a, cw_holds XW md ca LB ws m -> In w ws -> In g ws ->
  K_SUB <= w_kind w < K_GHOST -> K_GHOST <= w_kind g -> in_iv (w_iv w) a -> in_iv (w_iv g) a -> False.
Hypothesis XW_zc : forall md ca LB ws ws' m z z', cw_holds XW md ca LB ws m -> z' < 2 ^ 48 ->
  (forall w, In w ws' <-> (In w ws /\ w <> Win z 0 K_STACK) \/ w = Win z' 0 K_STACK) -> cw_holds XW md ca LB ws' m.

Theorem cw_sub_ghost : forall md ca LB ws m w g a, cwh md ca LB ws m -> In w ws -> In g ws ->
  K_SUB <= w_kind w < K_GHOST -> K_GHOST <= w_kind g -> in_iv (w_iv w) a -> in_iv (w_iv g) a -> False.
Proof.
  intros md ca LB ws m w g a H Hw Hg KS KG Ia Ig.
  destruct (Z.eq_dec md CM_NONE) as [M0|M0]; [exact (UOK.cw_unp_sub_ghost segs XW md ca LB ws m w g a H (or_introl M0) Hw Hg KS KG Ia Ig)|].
  destruct (Z.eq_dec md CM_UNP) as [M1|M1]; [exact (UOK.cw_unp_sub_ghost segs XW md ca LB ws m w g a H (or_intror (or_introl M1)) Hw Hg KS KG Ia Ig)|].
  destruct (Z.eq_dec md CM_CONS) as [M2|M2]; [exact (UOK.cw_unp_sub_ghost segs XW md ca LB ws m w g a H (or_intror (or_intror M2)) Hw Hg KS KG Ia Ig)|].
  unfold cw_unp_holds in H.
  rewrite (proj2 (Z.eqb_neq _ _) M0) in H. rewrite (proj2 (Z.eqb_neq _ _) M1), (proj2 (Z.eqb_neq _ _) M2) in H. cbn [orb] in H.
  exact (XW_sub_ghost md ca LB ws m w g a H Hw Hg KS KG Ia Ig).
Qed.

Theorem cw_zc : forall md ca LB ws ws' m z z', cwh md ca LB ws m -> z' < 2 ^ 48 ->
  (forall w, In w ws' <-> (In w ws /\ w <> Win z 0 K_STACK) \/ w = Win z' 0 K_STACK) -> cwh md ca LB ws' m.
Proof.
  intros md ca LB ws ws' m z z' H Z48 Hws'. unfold cw_unp_holds in *.
  assert (OLD : forall w, In w ws' -> w <> Win z' 0 K_STACK -> In w ws).
  { intros w Hw NE. apply Hws' in Hw as [[Hw _]|E]; [exact Hw| exfalso; exact (NE E)]. }
  destruct (md =? CM_NONE).
  - apply Forall_forall. intros w Hw. destruct (proj1 (Hws' w) Hw) as [[Hw0 _]| ->]; [exact (proj1 (Forall_forall _ _) H w Hw0)|].
    unfold no_sub. cbn [w_kind]. unfold K_SUB, K_STACK. lia.
  - destruct ((md =? CM_UNP) || (md =? CM_CONS)); [| exact (XW_zc md ca LB ws ws' m z z' H Z48 Hws')].
    destruct (decode_uc ca) as [u|]; [|exact H].
    assert (NP : forall w, In w ws' -> pot_win w -> In w ws).
    { intros w Hw (K0 & L0 & PB & _). apply OLD; [exact Hw|]. intros ->. cbn [w_lo] in PB. unfold POT_BASE in PB. lia. }
    destruct H as (g & L & P & O & Wk & M & CS & AX & SE). exists g.
    split; [exact L|]. split; [exact P|]. split; [exact O|]. split; [| split; [exact M| split; [exact (cons_ok_ws _ _ _ _ _ _ CS NP)| split; [exact (acct_pot_ws _ _ _ _ _ AX NP)|]]]].
    + unfold wins_ok in *. apply Forall_forall. intros w Hw NS. apply (proj1 (Forall_forall _ _) Wk w); [| exact NS].
      apply OLD; [exact Hw|]. intros ->. apply NS. reflexivity.
    + apply (Seal.seal_ok_ws ws _ ws' SE). intros w Hw K9. apply OLD; [exact Hw|]. intros ->. cbn [w_kind] in K9. unfold Seal.K_TWIN, K_STACK in K9. lia.
Qed.

Hypothesis XW_k0_del : forall md ca LB ws ws' m w0, cw_holds XW md ca LB ws m -> w_kind w0 = K_STACK ->
  (forall w, In w ws' <-> In w ws /\ w <> w0) -> cw_holds XW md ca LB ws' m.
Theorem cw_k0_del : forall md ca LB ws ws' m w0, cwh md ca LB ws m -> w_kind w0 = K_STACK ->
  (forall w, In w ws' <-> In w ws /\ w <> w0) -> cwh md ca LB ws' m.
Proof.
  intros md ca LB ws ws' m w0 H K0 Hws'. unfold cw_unp_holds in *.
  assert (SUB : forall w, In w ws' -> In w ws) by (intros w Hw; exact (proj1 (proj1 (Hws' w) Hw))).
  destruct (md =? CM_NONE).
  - apply Forall_forall. intros w Hw. exact (proj1 (Forall_forall _ _) H w (SUB w Hw)).
  - destruct ((md =? CM_UNP) || (md =? CM_CONS)); [| exact (XW_k0_del md ca LB ws ws' m w0 H K0 Hws')].
    destruct (decode_uc ca) as [u|]; [|exact H].
    destruct H as (g & L & P & O & Wk & M & CS & AX & SE). exists g.
    split; [exact L|]. split; [exact P|]. split; [exact O|]. split; [| split; [exact M| split; [exact (cons_ok_ws _ _ _ _ _ _ CS (fun w Hw _ => SUB w Hw))| split; [exact (acct_pot_ws _ _ _ _ _ AX (fun w Hw _ => SUB w Hw))|]]]].
    + unfold wins_ok in *. apply Forall_forall. intros w Hw. exact (proj1 (Forall_forall _ _) Wk w (SUB w Hw)).
    + apply (Seal.seal_ok_ws ws _ ws' SE). intros w Hw _. exact (SUB w Hw).
Qed.

Theorem cw_unp_vecs_distinct : forall md ca LB ws m a b, cwh md ca LB ws m -> (md = CM_UNP \/ md = CM_CONS) ->
  nth_error ca 1 = Some a -> nth_error ca 4 = Some b -> bv_unsigned a <> bv_unsigned b.
Proof.
  intros md ca LB ws m a b H MD NA NB. unfold cw_unp_holds in H.
  assert (M0 : (md =? CM_NONE) = false) by (apply Z.eqb_neq; unfold CM_NONE, CM_UNP, CM_CONS in *; lia). rewrite M0 in H.
  assert (M1 : ((md =? CM_UNP) || (md =? CM_CONS)) = true) by (apply orb_true_iff; destruct MD as [->| ->]; [left| right]; apply Z.eqb_refl). rewrite M1 in H.
  destruct (decode_uc ca) as [u|] eqn:DU; [| contradiction].
  destruct H as (g & L & P & O & _).
  unfold decode_uc in DU.
  destruct ca as [|a0 [|a1 [|a2 [|a3 [|a4 [|a5 [|a6 [|a7 [|a8 [|a9 [|a10 [|a11 [|a12 [|a13 [|a14 [|a15 [|zh [|? ?]]]]]]]]]]]]]]]]]]; try discriminate DU.
  injection DU as <-. cbn [nth_error] in NA, NB. injection NA as <-. injection NB as <-.
  destruct L as (_ & LCB & _ & _ & LVB & _). cbn [c_cb c_vb] in LCB, LVB.
  pose proof (owned_pos g P _ (owned_cstk g)) as PC. pose proof (owned_pos g P _ (owned_vstk g)) as PV. cbn [snd cstk_block vstk_block] in PC, PV.
  pose proof (disj_cv g LB O) as D. unfold rdisj in D.
  rewrite <- LCB, <- LVB. intros E. rewrite E in D. lia.
Qed.

Theorem cw_unp_vecs_distinct_ij : forall md ca LB ws m i j a b, cwh md ca LB ws m -> (md = CM_UNP \/ md = CM_CONS) ->
  (i = 1 \/ i = 4)%nat -> (j = 1 \/ j = 4)%nat -> i <> j -> nth_error ca i = Some a -> nth_error ca j = Some b -> bv_unsigned a <> bv_unsigned b.
Proof.
  intros md ca LB ws m i j a b H MD [->| ->] [->| ->] NE NA NB; try (exfalso; exact (NE eq_refl)).
  - exact (cw_unp_vecs_distinct md ca LB ws m a b H MD NA NB).
  - intros E. exact (cw_unp_vecs_distinct md ca LB ws m b a H MD NB NA (eq_sym E)).
Qed.

Lemma in_alloc_chunk : forall g a n, pure_ok g -> in_alloc (u_zone g) a n -> 0 < n ->
  forall x, a <= x < a + n -> exists c, In c (z_chunks (u_zone g)) /\ in_iv (chunk_block c) x.
Proof.
  intros g a n P IA POS x Hx. destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ZV).
  destruct ZV as (NE & _ & _ & V4 & V5 & V6 & _).
  destruct IA as [(c & Hc & LO & HI)|[LO HI]].
  - exists c. split.
    + destruct (z_chunks (u_zone g)) as [|h t]; [destruct Hc| right; exact Hc].
    + unfold in_iv, chunk_block, chunk_lo, chunk_hi, CHUNK_HDR in *. cbn [fst snd]. lia.
  - destruct (z_chunks (u_zone g)) as [|h t] eqn:EC; [exfalso; exact (NE eq_refl)|]. cbn [hd] in *.
    exists h. split; [left; reflexivity|].
    unfold in_iv, chunk_block, chunk_lo, chunk_hi, CHUNK_HDR in *. cbn [fst snd]. lia.
Qed.

Definition zone_sealed (LB : blocks) (ws : list window) (a : Z) : Prop :=
  exists cs c, Seal.seal_ok ws cs /\ In c cs /\ In (chunk_block c) LB /\ in_iv (chunk_block c) a /\
    (forall w', In w' ws -> (w_kind w' = K_BLOCK \/ K_GHOST <= w_kind w') -> forall x, in_iv (w_iv w') x -> ~ in_iv (chunk_block c) x).

Theorem cw_unp_zone_sealed : forall md ca LB ws m w a, cwh md ca LB ws m -> (md = CM_UNP \/ md = CM_CONS) -> In w ws ->
  (w_kind w = K_SLOT \/ w_kind w = K_ZONE) -> in_iv (w_iv w) a -> zone_sealed LB ws a.
Proof.
  intros md ca LB ws m w a H MD Hw KW Ia. unfold cw_unp_holds in H.
  assert (M0 : (md =? CM_NONE) = false) by (apply Z.eqb_neq; unfold CM_NONE, CM_UNP, CM_CONS in *; lia). rewrite M0 in H.
  assert (M1 : ((md =? CM_UNP) || (md =? CM_CONS)) = true) by (apply orb_true_iff; destruct MD as [->| ->]; [left| right]; apply Z.eqb_refl). rewrite M1 in H.
  destruct (decode_uc ca) as [u|]; [| contradiction].
  destruct H as (g & L & P & O & Wk & M & CS & AX & SE).
  assert (CH : exists c, In c (z_chunks (u_zone g)) /\ in_iv (chunk_block c) a).
  { destruct (proj1 (Forall_forall _ _) Wk w Hw ltac:(unfold K_SLOT, K_ZONE, K_STACK in *; lia)) as [[[KB|KG] _]|[_ SO]];
      [unfold K_SLOT, K_ZONE, K_BLOCK in *; lia| unfold K_SLOT, K_ZONE, K_GHOST in *; lia|].
    pose proof P as (VC & EC & SC & CC & VV & EV & SV & CV & LV & DL & LA & ZV).
    unfold sub_ok in SO. cbv zeta in SO. unfold in_iv, w_iv in Ia. cbn [fst snd] in Ia.
    destruct SO as [(KK & _)|[(KK & _)|[(_ & lD & HlD & I2 & I3)|(_ & Z1 & Z2)]]];
      [unfold K_CTOP, K_SLOT, K_ZONE in *; lia| unfold K_VTOP, K_SLOT, K_ZONE in *; lia| |].
    - pose proof (UOK.last_opt_In _ _ _ HlD) as INl.
      pose proof (proj1 (Forall_forall _ _) LV lD INl) as VL. pose proof (UOK.lv_k_nonneg lD VL) as K0.
      assert (BYTES : 0 < lv_bytes lD).
      { unfold lv_unfilled, lv_slot, OBJ_SIZE in *. destruct (md =? CM_CONS); lia. }
      apply (in_alloc_chunk g (lv_P lD) (lv_bytes lD) P (proj1 LA lD INl) BYTES).
      unfold lv_unfilled, lv_slot in *. unfold OBJ_SIZE in *. destruct (md =? CM_CONS); lia.
    - destruct ZV as (NE & _ & _ & V4 & V5 & V6 & _).
      destruct (z_chunks (u_zone g)) as [|h t] eqn:ECH; [exfalso; exact (NE eq_refl)|]. cbn [hd] in *.
      exists h. split; [left; reflexivity|].
      unfold in_iv, chunk_block, chunk_lo, chunk_hi, CHUNK_HDR in *. cbn [fst snd]. lia. }
  destruct CH as (c & Hc & INc).
  assert (OWN : In (chunk_block c) (owned g)) by (right; right; apply in_map; exact Hc).
  exists (z_chunks (u_zone g)), c. split; [exact SE|]. split; [exact Hc|]. split; [exact (proj1 O _ OWN)|]. split; [exact INc|].
  intros w' Hw' KK x Ix IC.
  destruct (proj1 (Forall_forall _ _) Wk w' Hw' ltac:(unfold K_BLOCK, K_GHOST, K_STACK in *; lia)) as [[_ DJ]|[_ SO]].
  - exact (DJ _ OWN x Ix IC).
  - unfold sub_ok in SO. cbv zeta in SO.
    destruct SO as [(K2 & _)|[(K2 & _)|[(K2 & _)|(K2 & _)]]]; unfold K_CTOP, K_VTOP, K_SLOT, K_ZONE, K_BLOCK, K_GHOST in *; lia.
Qed.

Hypothesis XW_no_zone : forall md ca LB ws m w, cw_holds XW md ca LB ws m -> In w ws -> (w_kind w = K_SLOT \/ w_kind w = K_ZONE) -> False.

Theorem cw_zone_sealed : forall md ca LB ws m w a, cwh md ca LB ws m -> In w ws ->
  (w_kind w = K_SLOT \/ w_kind w = K_ZONE) -> in_iv (w_iv w) a -> zone_sealed LB ws a.
Proof.
  intros md ca LB ws m w a H Hw KW Ia.
  destruct (Z.eq_dec md CM_UNP) as [M1|M1]; [exact (cw_unp_zone_sealed md ca LB ws m w a H (or_introl M1) Hw KW Ia)|].
  destruct (Z.eq_dec md CM_CONS) as [M2|M2]; [exact (cw_unp_zone_sealed md ca LB ws m w a H (or_intror M2) Hw KW Ia)|].
  exfalso. unfold cw_unp_holds in H. destruct (md =? CM_NONE) eqn:M0.
  - apply (proj1 (Forall_forall _ _) H w Hw). unfold K_SUB, K_GHOST, K_SLOT, K_ZONE in *. lia.
  - rewrite (proj2 (Z.eqb_neq _ _) M1), (proj2 (Z.eqb_neq _ _) M2) in H. cbn [orb] in H.
    exact (XW_no_zone md ca LB ws m w H Hw KW).
Qed.

End WithSegs.
End UOL.
