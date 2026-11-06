(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_Ext MI_Cnt MI_WFree2 MI_WGroup MI_WMalloc MI_WFree MI_Sim MI_Contracts MI_Ledger Realloc MI_Realloc MI_Realloc2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Prog.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import A_MallocRep A_MallocTree A_MallocBlocks.

Set Keyed Unification.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Section REALLOC.
Variables (resv : list (Z * Z)) (st : mstate) (LB : list block) (bp : bptr) (A old n off : Z).
Hypothesis AR : AREACH_from resv st LB.
Hypothesis Hb : In (bp, A, old) LB.
Hypothesis Hn : 0 <= n < 2 ^ 48.
Let c : cptr := fst bp.
Hypothesis HA : A = conc st c + UNIT * off.
Definition rLB' (A' : Z) : list block := (bp, A', n) :: filter (fun b' => negb (aptr_eqb (blk_slot b') c)) LB.

Lemma In_filter_b {T} (f : T -> bool) x (l : list T) : In x (filter f l) -> In x l /\ f x = true.
Proof.
  intros H. apply (proj2 (list_elem_of_In _ _)) in H. apply list_elem_of_filter in H as [P H].
  split; [apply (proj1 (list_elem_of_In _ _)); exact H|]. destruct (f x); [reflexivity| destruct P].
Qed.

Lemma CORR_resize (st' : mstate) (BL : list blk) (A' : Z) :
  CORR st LB BL -> NoDup (map bslot BL) ->
  (forall k, In k BL -> bslot k <> c -> conc st' (bslot k) = conc st (bslot k)) ->
  A' = conc st' c + UNIT * off ->
  CORR st' (rLB' A') (((c, off), n) :: bl_remove c BL).
Proof.
  intros CR ND KEEP HA'. constructor.
  - split; [reflexivity|]. split; [reflexivity|]. exact HA'.
  - rewrite (bl_remove_filter c BL ND).
    pose proof (Forall2_filter (corr1 st) (fun b' : block => negb (aptr_eqb (blk_slot b') c)) (fun k0 : blk => negb (aptr_eqb (bslot k0) c)) LB BL CR
                  ltac:(intros b' k' (D1 & _ & _); rewrite D1; reflexivity)) as CRF.
    eapply Forall2_impl_in; [exact CRF|]. intros b' k' Hb' Hk' (D1 & D2 & D3). split; [exact D1|]. split; [exact D2|]. rewrite D3.
    apply In_filter_b in Hk' as [Hk' NE]. destruct (aptr_eqb_spec (bslot k') c) as [E|NE']; [discriminate|].
    rewrite (KEEP k' Hk' NE'). reflexivity.
Qed.

Lemma realloc_blk : exists L LS BL, INVL x0 st L BL LS /\ ld_resv L = resv /\ s_secret st = ctx_secret /\ CORR st LB BL /\ In ((c, off), old) BL.
Proof.
  destruct AR as (L & LS & BL & INV & LIVE & RESV & SEC & CR).
  destruct (Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3)).
  destruct k as [[c' off'] n']. cbn [bslot boff bsize blk_slot blk_size blk_addr fst snd] in C1, C2, C3. subst n'.
  assert (Ec : c' = c) by (symmetry; exact C1). clear C1. subst c'. assert (off' = off) by (rewrite HA in C3; unfold UNIT in C3; clear - C3; lia). subst off'.
  exists L, LS, BL. split; [exact INV|]. split; [exact RESV|]. split; [exact SEC|]. split; [exact CR| exact Hk].
Qed.

Theorem areach_realloc_resize g idx :
  s_slots st !! c = Some (g, idx) ->
  UNIT * off + n <= get_stride (MR st g) - IB -> get_stride (MR st g) - IB - UNIT * off - n < 2 ^ 32 ->
  AREACH_from resv (inplace_full st c off n) (rLB' A).
Proof.
  intros SL Hfit Hres. destruct realloc_blk as (L & LS & BL & INV & RESV & SEC & CR & Hk).
  destruct (block_facts x0 st L BL LS INV c off old Hk) as (g' & bg & idx' & ai & a & ar & ka & BF).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) as SL'. rewrite SL in SL'. assert (g' = g /\ idx' = idx) as [-> ->] by (split; congruence).
  pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as Hoff.
  pose proof (inplace_INVL x0 st L BL LS c off old n INV Hk eq_refl ltac:(lia) g bg idx ai a ar ka BF Hfit Hres) as INV'.
  exists (set_live (map bslot (((c, off), n) :: bl_remove c BL)) L), LS, (((c, off), n) :: bl_remove c BL).
  split; [apply INVL_set_live; exact INV'|]. split; [reflexivity|]. split; [exact RESV|].
  split; [rewrite <- SEC; rewrite <- (s_secret_strip (inplace_full st c off n)), strip_inplace_full; reflexivity|].
  assert (CC : forall q, conc (inplace_full st c off n) q = conc st q).
  { intros q. unfold conc, get_region. rewrite <- (s_regions_strip (inplace_full st c off n)), strip_inplace_full. reflexivity. }
  apply CORR_resize; [exact CR| exact (is_nodup _ _ _ IS)| intros k _ _; apply CC| rewrite CC; exact HA].
Qed.

Lemma realloc_remap_facts rid g oldb oldl needed :
  realloc_case (strip st) c A n = RcRemap rid g oldb oldl needed ->
  rid = fst c /\ needed = remap_needed (UNIT * off) n /\ MMAP_THRESHOLD <= n
  /\ (exists i r0, s_slots st !! c = Some (g, i) /\ s_regions st !! rid = Some r0 /\ r_kind r0 = RKGroup
        /\ oldb = r_base r0 /\ oldl = round_up_pg (r_len r0) /\ conc st c = oldb + UNIT /\ m_sizeclass (MR st g) = 63
        /\ m_maplen (MR st g) * 4096 = oldl /\ 0 < r_len r0).
Proof.
  intros RC. destruct realloc_blk as (L & LS & BL & INV & RESV & SEC & CR & Hk).
  destruct (block_facts x0 st L BL LS INV c off old Hk) as (g' & bg & idx & ai & a & ar & ka & BF).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  unfold realloc_case, realloc_geom in RC. change (s_slots (strip st)) with (s_slots st) in RC. rewrite (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) in RC.
  change (get_meta_rec (strip st) g') with (MR st g') in RC. change (conc (strip st) c) with (conc st c) in RC.
  cbv beta iota zeta in RC. cbn [rg_g rg_start rg_end rg_idx rg_stride] in RC. change (get_meta_rec (strip st) g') with (MR st g') in RC.
  destruct (inplace_ok (strip st) (mkRG g' idx (get_stride (MR st g')) (conc st c) (conc st c + get_stride (MR st g') - IB)) A n) eqn:IP; [discriminate|].
  destruct ((MMAP_THRESHOLD <=? n) && (48 <=? m_sizeclass (MR st g'))) eqn:BIG; [| discriminate].
  apply andb_prop in BIG as [THR SCL]. apply Z.leb_le in THR. apply Z.leb_le in SCL.
  inversion RC. subst rid g oldb oldl needed. clear RC.
  pose proof (ig_ok _ _ _ IG _ _ _ (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) as GO.
  assert (SC63 : m_sizeclass (MR st g') = 63).
  { destruct (g_sc _ _ _ _ _ _ GO) as [[S _]|(S & _)]; [lia| exact S]. }
  destruct (g_sc _ _ _ _ _ _ GO) as [[S _]|(_ & L0 & ML & _)]; [rewrite SC63 in S; lia|].
  destruct (g_top _ _ _ _ _ _ GO ML) as (B0 & r0 & Hr0 & Kr0 & E0 & _).
  pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as Ec. pose proof (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF) as Hmem. pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi.
  assert (I0 : idx = 0) by lia.
  assert (Fc : fst c = fst bg) by (rewrite Ec; reflexivity).
  assert (Sc : snd c = 16). { rewrite Ec; cbn [snd]; unfold sstart; rewrite (gbase_bm _ _ _ _ _ _ _ _ _ _ _ BF), B0, I0. unfold UNIT. lia. }
  assert (Ebg : bg = (fst c, 0)) by (destruct bg as [br bo]; cbn in B0, Fc |- *; subst; reflexivity).
  assert (HA' : A - conc st c = UNIT * off) by (rewrite HA; lia).
  rewrite HA'. split; [reflexivity|]. split; [reflexivity|]. split; [exact THR|].
  exists idx, r0. split; [exact (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF)|]. rewrite <- Fc in Hr0. split; [exact Hr0|]. split; [exact Kr0|].
  rewrite Hmem. change (conc (strip st) bg) with (conc st bg). rewrite Ebg. rewrite (conc_region st (fst c) 0 r0 Hr0), (conc_region' st c r0 Hr0), Sc.
  split; [lia|]. split; [exact E0|]. split; [unfold UNIT; lia|]. split; [exact SC63|]. split; [reflexivity|].
  destruct (ir_shape _ _ _ IR _ _ Hr0) as (_ & _ & LEN & _). exact LEN.
Qed.

Theorem areach_realloc_inplace :
  realloc_case (strip st) c A n = RcInPlace ->
  AREACH_from resv (inplace_full st c off n) (rLB' A).
Proof.
  intros RC. destruct realloc_blk as (L & LS & BL & INV & RESV & SEC & CR & Hk).
  destruct (block_facts x0 st L BL LS INV c off old Hk) as (g & bg & idx & ai & a & ar & ka & BF).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).

  unfold realloc_case, realloc_geom in RC. change (s_slots (strip st)) with (s_slots st) in RC. rewrite (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) in RC.
  change (get_meta_rec (strip st) g) with (MR st g) in RC. change (conc (strip st) c) with (conc st c) in RC.
  cbv beta iota zeta in RC. cbn [rg_g rg_start rg_end rg_idx rg_stride] in RC. change (get_meta_rec (strip st) g) with (MR st g) in RC.
  destruct (inplace_ok (strip st) (mkRG g idx (get_stride (MR st g)) (conc st c) (conc st c + get_stride (MR st g) - IB)) A n) eqn:IP;
    [| destruct ((MMAP_THRESHOLD <=? n) && (48 <=? m_sizeclass (MR st g))); discriminate].
  unfold inplace_ok in IP. cbn [rg_end rg_g] in IP. change (get_meta_rec (strip st) g) with (MR st g) in IP.
  apply andb_prop in IP as [IP SCL]. apply andb_prop in IP as [FIT THR]. apply Z.leb_le in FIT. apply Z.ltb_lt in THR. apply Z.leb_le in SCL.
  pose proof (size_to_class_ok n ltac:(lia)) as [STC _].
  assert (SC48 : m_sizeclass (MR st g) < 48).
  { destruct (g_sc _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF))) as [[S _]|(S & _)]; [lia| rewrite S in SCL; lia]. }
  assert (Hfit : UNIT * off + n <= get_stride (MR st g) - IB) by (rewrite HA in FIT; lia).
  pose proof (small_stride x0 st L BL LS bg g INV ltac:(exists ai; exact (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) SC48) as SS.
  pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as Hoff.
  pose proof (inplace_INVL x0 st L BL LS c off old n INV Hk eq_refl ltac:(lia) g bg idx ai a ar ka BF Hfit ltac:(unfold UNIT, IB in *; lia)) as INV'.
  exists (set_live (map bslot (((c, off), n) :: bl_remove c BL)) L), LS, (((c, off), n) :: bl_remove c BL).
  split; [apply INVL_set_live; exact INV'|]. split; [reflexivity|]. split; [exact RESV|].
  split; [rewrite <- SEC; rewrite <- (s_secret_strip (inplace_full st c off n)), strip_inplace_full; reflexivity|].
  assert (CC : forall q, conc (inplace_full st c off n) q = conc st q).
  { intros q. unfold conc, get_region. rewrite <- (s_regions_strip (inplace_full st c off n)), strip_inplace_full. reflexivity. }
  apply CORR_resize; [exact CR| exact (is_nodup _ _ _ IS)| intros k _ _; apply CC| rewrite CC; exact HA].
Qed.

Theorem areach_realloc_remap rid g oldb oldl needed nb :
  realloc_case (strip st) c A n = RcRemap rid g oldb oldl needed ->
  0 < nb -> nb mod 4096 = 0 -> nb + needed <= alloc_ceiling ->
  (forall rid2 r2, s_regions st !! rid2 = Some r2 -> rid2 <> rid ->
     let '(b2, l2) := region_live_range r2 in nb + needed <= b2 \/ b2 + l2 <= nb) ->
  AREACH_from resv (remap_full st c off n nb needed) (rLB' (nb + UNIT + UNIT * off))
  /\ rid = fst c /\ needed = remap_needed (UNIT * off) n
  /\ (exists i r0, s_slots st !! c = Some (g, i) /\ s_regions st !! rid = Some r0 /\ r_kind r0 = RKGroup
        /\ oldb = r_base r0 /\ oldl = round_up_pg (r_len r0) /\ conc st c = oldb + UNIT /\ m_sizeclass (MR st g) = 63).
Proof.
  intros RC NB0 NBA NCEIL DISJ. destruct realloc_blk as (L & LS & BL & INV & RESV & SEC & CR & Hk).
  destruct (block_facts x0 st L BL LS INV c off old Hk) as (g' & bg & idx & ai & a & ar & ka & BF).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  unfold realloc_case, realloc_geom in RC. change (s_slots (strip st)) with (s_slots st) in RC. rewrite (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) in RC.
  change (get_meta_rec (strip st) g') with (MR st g') in RC. change (conc (strip st) c) with (conc st c) in RC.
  cbv beta iota zeta in RC. cbn [rg_g rg_start rg_end rg_idx rg_stride] in RC. change (get_meta_rec (strip st) g') with (MR st g') in RC.
  destruct (inplace_ok (strip st) (mkRG g' idx (get_stride (MR st g')) (conc st c) (conc st c + get_stride (MR st g') - IB)) A n) eqn:IP; [discriminate|].
  destruct ((MMAP_THRESHOLD <=? n) && (48 <=? m_sizeclass (MR st g'))) eqn:BIG; [| discriminate].
  apply andb_prop in BIG as [THR SCL]. apply Z.leb_le in THR. apply Z.leb_le in SCL.
  inversion RC. subst rid g oldb oldl needed. clear RC.
  pose proof (ig_ok _ _ _ IG _ _ _ (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) as GO.
  assert (SC63 : m_sizeclass (MR st g') = 63).
  { destruct (g_sc _ _ _ _ _ _ GO) as [[S _]|(S & _)]; [lia| exact S]. }
  destruct (g_sc _ _ _ _ _ _ GO) as [[S _]|(_ & L0 & ML & _)]; [rewrite SC63 in S; lia|].
  destruct (g_top _ _ _ _ _ _ GO ML) as (B0 & r0 & Hr0 & Kr0 & E0 & _).
  pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as Ec. pose proof (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF) as Hmem. pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi.
  assert (I0 : idx = 0) by lia.
  assert (Fc : fst c = fst bg) by (rewrite Ec; reflexivity).
  assert (Sc : snd c = 16). { rewrite Ec; cbn [snd]; unfold sstart; rewrite (gbase_bm _ _ _ _ _ _ _ _ _ _ _ BF), B0, I0. unfold UNIT. lia. }
  assert (Ebg : bg = (fst c, 0)) by (destruct bg as [br bo]; cbn in B0, Fc |- *; subst; reflexivity).
  assert (HA' : A - conc st c = UNIT * off) by (rewrite HA; lia).
  rewrite HA' in *.
  pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as Hoff.
  pose proof (remap_INVL x0 st L BL LS c off old n INV Hk eq_refl ltac:(lia) g' bg idx ai a ar ka BF SC63 nb NB0 NBA NCEIL DISJ) as INV'.
  assert (HgF : s_groups st !! (fst c, 0) = Some (mkGhdr (Some g') ai)) by (rewrite <- Ebg; exact (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)).
  assert (CCo : forall k, In k BL -> bslot k <> c -> conc (remap_full st c off n nb (remap_needed (UNIT * off) n)) (bslot k) = conc st (bslot k)).
  { intros k Hk' NE.
    unfold conc, get_region. rewrite <- (s_regions_strip (remap_full st c off n nb _)), strip_remap_full by (eexists; exact (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF)).
    rewrite (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF). rewrite s_regions_remap_update. change (s_regions (strip st)) with (s_regions st).
    rewrite lookup_insert_ne; [reflexivity|].
    intros E. destruct (is_blocks _ _ _ IS k Hk') as (m & i & Hs & _).
    destruct (rid_slots x0 st L BL LS g' (fst c) ai nb n INV HgF SC63 (bslot k) m i Hs (eq_sym E)) as (Es & _). apply NE. rewrite Es, <- Sc. symmetry. apply surjective_pairing. }
  assert (CCc : conc (remap_full st c off n nb (remap_needed (UNIT * off) n)) c = nb + UNIT).
  { unfold conc, get_region. rewrite <- (s_regions_strip (remap_full st c off n nb _)), strip_remap_full by (eexists; exact (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF)).
    rewrite (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF). rewrite s_regions_remap_update. rewrite lookup_insert_eq. cbn [r_base]. rewrite Sc. reflexivity. }
  split; [| split; [reflexivity| split; [reflexivity|]]].
  - exists (set_live (map bslot (((c, off), n) :: bl_remove c BL)) (LR st L c off n g' nb)), LS, (((c, off), n) :: bl_remove c BL).
    split; [apply INVL_set_live; exact INV'|]. split; [reflexivity|]. split; [exact RESV|].
    split; [rewrite <- SEC; rewrite <- (s_secret_strip (remap_full st c off n nb _)), strip_remap_full by (eexists; exact (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF)); reflexivity|].
    apply CORR_resize; [exact CR| exact (is_nodup _ _ _ IS)| exact CCo| rewrite CCc; lia].
  - exists idx, r0. split; [exact (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF)|]. rewrite <- Fc in Hr0. split; [exact Hr0|]. split; [exact Kr0|].
    rewrite Hmem. change (conc (strip st) bg) with (conc st bg). rewrite Ebg. rewrite (conc_region st (fst c) 0 r0 Hr0), (conc_region' st c r0 Hr0), Sc.
    split; [lia|]. split; [exact E0|]. split; [unfold UNIT; lia| exact SC63].
Qed.
End REALLOC.

End CEIL.
