(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc Mall7vg KInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_S421.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres4 MI_WFree MI_Ws22.

Module MI_WKill.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc Mall7vg KInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_S421.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres4 MI_WFree.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall7vg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List.MI_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Arith OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Geom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ext OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2.MI_Ext2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_S421 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.MI_Read OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2.MI_Pres1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres4.MI_Pres3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zsum_perm l l' : Permutation l l' -> zsum l = zsum l'.
Proof. induction 1; unfold zsum in *; cbn in *; lia. Qed.

Lemma round_up_ge_k x : x <= round_up_pg x.
Proof. unfold round_up_pg. pose proof (proj2 (Z.land_nonneg (-x) (PGSZ - 1)) ltac:(right; unfold PGSZ; lia)). lia. Qed.

Definition gterm (st : mstate) (sc : Z) (bh : aptr * ghdr) : Z :=
  match g_meta (snd bh) with
  | Some m => if m_sizeclass (MR st m) =? sc then cnt_of (MR st m) else 0
  | None => 0
  end.
Lemma gcnt_unfold st sc : gcnt st sc = zsum (map (gterm st sc) (map_to_list (s_groups st))).
Proof. reflexivity. Qed.

Lemma gcnt_delete st st' p h sc :
  s_groups st !! p = Some h -> s_groups st' = delete p (s_groups st) -> s_metas st' = s_metas st ->
  gcnt st sc = gterm st sc (p, h) + gcnt st' sc.
Proof.
  intros Hp HG HM. rewrite !gcnt_unfold, HG.
  rewrite <- (zsum_perm _ _ (Permutation_map (gterm st sc) (map_to_list_delete (s_groups st) p h Hp))). cbn. f_equal.
  f_equal. apply map_ext. intros [b hb]. unfold gterm. cbn. unfold MR, get_meta_rec. rewrite HM. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section KILL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
Variables (X : extras) (st st1 : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (g p : aptr) (ai i : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : s_groups st !! p = Some (mkGhdr (Some g) ai).
Hypothesis HF : x_fresh X = Some g.
Hypothesis NL : m_next (MR st g) = None.
Hypothesis HO : x_orph X = None.
Hypothesis Hi : 0 <= i <= m_last_idx (MR st g).
Hypothesis HP : x_pend X = Some (fst p, sstart (MR st g) i).
Hypothesis ALL : forall j, 0 <= j <= m_last_idx (MR st g) -> j <> i ->
  tbit (m_avail (MR st g)) j = true \/ tbit (m_freed (MR st g)) j = true.
Let sc := m_sizeclass (MR st g).
Let cnt := m_last_idx (MR st g) + 1.
(* [comment removed for export] *)
Hypothesis S1 : exists U, st1 = upd_ctx (fun c => set_usage_map U c) st.
Hypothesis U1 : forall sc', 0 <= sc' < 48 -> usage st1 sc' = if sc' =? sc then usage st sc - cnt else usage st sc'.
Hypothesis U2 : forall sc0 v, c_usage (s_ctx st1) !! sc0 = Some v -> 0 <= sc0 < 48.
Let st' := del_slots p (get_stride (MR st g)) cnt (del_group p st1).
Let nested := m_maplen (MR st g) =? 0.
Let X' := mkX (x_idle X) (g :: x_zomb X) (if nested then Some p else None) (if nested then None else Some (fst p)) None.

Let IR := proj1 INV. Let IA := proj1 (proj2 INV). Let IM := proj1 (proj2 (proj2 INV)). Let IL := proj1 (proj2 (proj2 (proj2 INV))).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))). Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Lemma g_hosts : hosts st p g. Proof. exists ai. exact Hg. Qed.
Lemma GO : group_ok X st LS g p ai. Proof. exact (ig_ok _ _ _ IG _ _ _ Hg). Qed.
Lemma stride_pos : 0 < get_stride (MR st g).
Proof. pose proof (stride_ge _ _ _ IG _ _ g_hosts) as [H _]. unfold UNIT in H. lia. Qed.
Lemma gbase_p : gbase (MR st g) = p. Proof. exact (hosts_gbase _ _ _ IM _ _ g_hosts). Qed.
Lemma slot_g j : slot_start' (MR st g) j = (fst p, snd p + UNIT + get_stride (MR st g) * j).
Proof. rewrite slot_start'_sstart. unfold sstart. rewrite gbase_p. reflexivity. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma K_metas : s_metas st' = s_metas st. Proof. destruct S1 as [U ->]. reflexivity. Qed.
Lemma K_MR x : MR st' x = MR st x. Proof. unfold MR, get_meta_rec. rewrite K_metas. reflexivity. Qed.
Lemma K_regions : s_regions st' = s_regions st. Proof. destruct S1 as [U ->]. reflexivity. Qed.
Lemma K_shadow : s_shadow st' = s_shadow st. Proof. destruct S1 as [U ->]. reflexivity. Qed.
Lemma K_areas : s_areas st' = s_areas st. Proof. destruct S1 as [U ->]. reflexivity. Qed.
Lemma K_tick : s_tick st' = s_tick st. Proof. destruct S1 as [U ->]. reflexivity. Qed.
Lemma K_next_rid : s_next_rid st' = s_next_rid st. Proof. destruct S1 as [U ->]. reflexivity. Qed.
Lemma K_secret : s_secret st' = s_secret st. Proof. destruct S1 as [U ->]. reflexivity. Qed.
Lemma K_reserved : s_reserved st' = s_reserved st. Proof. destruct S1 as [U ->]. reflexivity. Qed.
Lemma K_groups : s_groups st' = delete p (s_groups st). Proof. destruct S1 as [U ->]. reflexivity. Qed.
Lemma K_ctx : s_ctx st' = s_ctx st1. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma K_c (P : mctx -> Prop) : (forall c U, P c -> P (set_usage_map U c)) -> P (s_ctx st) -> P (s_ctx st').
Proof. intros HPU H0. rewrite K_ctx. destruct S1 as [U ->]. cbn. apply HPU. exact H0. Qed.
Lemma K_cf :
  c_secret (s_ctx st') = c_secret (s_ctx st) /\ c_init_done (s_ctx st') = c_init_done (s_ctx st)
  /\ c_mmap_counter (s_ctx st') = c_mmap_counter (s_ctx st) /\ c_free_meta_head (s_ctx st') = c_free_meta_head (s_ctx st)
  /\ c_avail_meta (s_ctx st') = c_avail_meta (s_ctx st) /\ c_avail_meta_count (s_ctx st') = c_avail_meta_count (s_ctx st)
  /\ c_avail_meta_area_count (s_ctx st') = c_avail_meta_area_count (s_ctx st) /\ c_meta_alloc_shift (s_ctx st') = c_meta_alloc_shift (s_ctx st)
  /\ c_meta_area_head (s_ctx st') = c_meta_area_head (s_ctx st) /\ c_meta_area_tail (s_ctx st') = c_meta_area_tail (s_ctx st)
  /\ c_avail_meta_areas (s_ctx st') = c_avail_meta_areas (s_ctx st) /\ c_active (s_ctx st') = c_active (s_ctx st)
  /\ c_unmap_seq (s_ctx st') = c_unmap_seq (s_ctx st) /\ c_bounces (s_ctx st') = c_bounces (s_ctx st)
  /\ c_seq (s_ctx st') = c_seq (s_ctx st) /\ c_brk (s_ctx st') = c_brk (s_ctx st) /\ c_usage (s_ctx st') = c_usage (s_ctx st1).
Proof. destruct S1 as [U E]. rewrite K_ctx, E. cbn. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity. Qed.
Lemma K_usage sc' : usage st' sc' = usage st1 sc'.
Proof. reflexivity. Qed.

Lemma K_get_head h : get_head st' h = get_head st h.
Proof. destruct S1 as [U ->]. destruct h; reflexivity. Qed.
Lemma K_frontier rid r : frontier st' rid r = frontier st rid r.
Proof. unfold frontier. rewrite K_ctx. destruct S1 as [U ->]. reflexivity. Qed.

(* [comment removed for export] *)
Definition gslot (s : aptr) : Prop := exists j, 0 <= j < cnt /\ s = slot_start' (MR st g) j.
Lemma K_slots s : s_slots st' !! s = s_slots st !! s /\ ~ gslot s \/ s_slots st' !! s = None /\ gslot s.
Proof.
  pose proof stride_pos as SP. pose proof (g_li _ _ _ _ _ _ GO) as LI.
  unfold st'. rewrite lookup_del_slots; [| unfold cnt; lia| exact SP].
  replace (s_slots (del_group p st1)) with (s_slots st) by (destruct S1 as [U ->]; reflexivity).
  set (d := snd s - snd p - UNIT).
  destruct ((fst s =? fst p)%N && (0 <=? d) && (d mod get_stride (MR st g) =? 0) && (d / get_stride (MR st g) <? cnt)) eqn:E.
  - right. split; [reflexivity|]. apply Bool.andb_true_iff in E as [E E4]. apply Bool.andb_true_iff in E as [E E3]. apply Bool.andb_true_iff in E as [E1 E2].
    apply N.eqb_eq in E1. apply Z.leb_le in E2. apply Z.eqb_eq in E3. apply Z.ltb_lt in E4.
    exists (d / get_stride (MR st g)). split; [split; [apply Z.div_pos; lia| exact E4]|].
    rewrite slot_g. pose proof (Z.div_mod d (get_stride (MR st g)) ltac:(lia)) as DM. rewrite E3, Z.add_0_r in DM.
    destruct s as [sr so]. cbn in E1, d |- *. subst sr. f_equal. unfold d in DM. lia.
  - left. split; [reflexivity|]. ((first [ intro dR_38; dex1 dR_38 as j; destruct dR_38 as [Hj Es] | intro dR_38; dand3 dR_38 as j Hj Es | intros (j & Hj & Es) ])). rewrite slot_g in Es. subst s. cbn in d.
    assert (Ed : d = get_stride (MR st g) * j) by (unfold d; lia).
    rewrite N.eqb_refl in E. cbn in E.
    assert (E2 : (0 <=? d) = true) by (apply Z.leb_le; rewrite Ed; nia). rewrite E2 in E. cbn in E.
    assert (E3 : (d mod get_stride (MR st g) =? 0) = true) by (apply Z.eqb_eq; rewrite Ed, Z.mul_comm; apply Z_mod_mult).
    rewrite E3 in E. cbn in E.
    assert (E4 : (d / get_stride (MR st g) <? cnt) = true) by (apply Z.ltb_lt; rewrite Ed, Z.mul_comm, Z_div_mult by lia; lia).
    rewrite E4 in E. discriminate.
Qed.
Lemma K_slots_other s : ~ gslot s -> s_slots st' !! s = s_slots st !! s.
Proof. intros NG. destruct (K_slots s) as [[E _]|[_ G]]; [exact E| tauto]. Qed.
(* [comment removed for export] *)
Lemma K_slots_some s v : s_slots st' !! s = Some v -> s_slots st !! s = Some v /\ ~ gslot s.
Proof. intros H. destruct (K_slots s) as [[E NG]|[E G]]; [rewrite <- E; auto| congruence]. Qed.

(* [comment removed for export] *)
Lemma none_of {A} (o : option A) : (o <> None -> False) -> o = None.
Proof. destruct o; [intros H; exfalso; apply H; discriminate| reflexivity]. Qed.

Lemma g_slot_free j : 0 <= j <= m_last_idx (MR st g) ->
  ~ In (fst p, sstart (MR st g) j) (map bslot BL) /\ s_groups st !! (fst p, sstart (MR st g) j) = None
  /\ (x_pend X = Some (fst p, sstart (MR st g) j) -> j = i).
Proof.
  intros Hj. pose proof (is_part _ _ _ IS _ _ _ j Hg Hj) as P. cbn zeta in P. rewrite (slot_start'_eq _ _ _ IM _ _ _ g_hosts) in P. unfold one5 in P.
  (first [ dand11 P as _ nAB nAC nAD nAE nBC nBD nBE nCD nCE nDE | destruct P as (_ & nAB & nAC & nAD & nAE & nBC & nBD & nBE & nCD & nCE & nDE) ]).
  assert (PJ : x_pend X = Some (fst p, sstart (MR st g) j) -> j = i).
  { intros HPj. rewrite HP in HPj. inversion HPj.
    destruct (Z.lt_total j i) as [LT|[E|LT]]; [| exact E|]; exfalso.
    - pose proof (sstart_lt _ _ _ IG _ _ j i g_hosts LT). pose proof stride_pos. lia.
    - pose proof (sstart_lt _ _ _ IG _ _ i j g_hosts LT). pose proof stride_pos. lia. }
  destruct (Z.eq_dec j i) as [->|NE].
  - rewrite HP in *. split; [intros C; apply nCE; auto|]. split; [| auto]. apply none_of. intros Hh. apply nDE. auto.
  - destruct (ALL j Hj NE) as [A|B].
    + split; [intros C; exact (nAC (conj A C))|]. split; [| exact PJ]. apply none_of. intros Hh. exact (nAD (conj A Hh)).
    + split; [intros C; exact (nBC (conj B C))|]. split; [| exact PJ]. apply none_of. intros Hh. exact (nBD (conj B Hh)).
Qed.
Lemma g_slot_free' j : 0 <= j <= m_last_idx (MR st g) ->
  ~ In (slot_start' (MR st g) j) (map bslot BL) /\ s_groups st !! (slot_start' (MR st g) j) = None.
Proof. intros Hj. rewrite (slot_start'_eq _ _ _ IM _ _ _ g_hosts). (first [ pose proof ((g_slot_free j Hj)) as dR_2; dand3 dR_2 as A B _ | destruct (g_slot_free j Hj) as (A & B & _) ]). auto. Qed.

Lemma gslot_range s : gslot s -> exists j, 0 <= j <= m_last_idx (MR st g) /\ s = slot_start' (MR st g) j.
Proof. ((first [ intro dR_39; dex1 dR_39 as j; destruct dR_39 as [Hj E] | intro dR_39; dand3 dR_39 as j Hj E | intros (j & Hj & E) ])). exists j. unfold cnt in Hj. split; [lia| exact E]. Qed.

(* [comment removed for export] *)
Lemma other_slot_not_g m b j : hosts st b m -> m <> g -> 0 <= j <= m_last_idx (MR st m) -> ~ gslot (slot_start' (MR st m) j).
Proof.
  intros Hm NE Hj G. (first [ pose proof ((gslot_range _ G)) as dR_3; dex1 dR_3 as j'; destruct dR_3 as [Hj' E] | pose proof ((gslot_range _ G)) as dR_3; dand3 dR_3 as j' Hj' E | destruct (gslot_range _ G) as (j' & Hj' & E) ]).
  destruct (slot_key_inj _ _ _ IS _ _ _ _ _ _ Hm g_hosts Hj Hj' E) as [Em _]. exact (NE Em).
Qed.
Lemma entry_not_g s m j : s_slots st !! s = Some (m, j) -> m <> g -> ~ gslot s.
Proof.
  intros Hs NE. (first [ pose proof ((is_valid _ _ _ IS _ _ _ Hs)) as dR_4; dand3 dR_4 as [b Hb] Hj -> | destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & Hj & ->) ]). exact (other_slot_not_g m b j Hb NE Hj).
Qed.
(* [comment removed for export] *)
Lemma entry_g_gslot s j : s_slots st !! s = Some (g, j) -> gslot s.
Proof.
  intros Hs. (first [ pose proof ((is_valid _ _ _ IS _ _ _ Hs)) as dR_5; dand3 dR_5 as _ Hj -> | destruct (is_valid _ _ _ IS _ _ _ Hs) as (_ & Hj & ->) ]). exists j. unfold cnt. split; [lia| reflexivity].
Qed.

Lemma hosts_K b m : hosts st' b m <-> hosts st b m /\ b <> p.
Proof.
  unfold hosts. rewrite K_groups. split.
  - intros [a H]. apply lookup_delete_Some in H as [NE H]. split; [exists a; exact H| congruence].
  - intros [[a H] NE]. exists a. rewrite lookup_delete_ne by congruence. exact H.
Qed.
(* [comment removed for export] *)
Lemma live_K m : live_group st m -> m <> g -> live_group st' m.
Proof.
  intros [b Hb] NE. exists b. apply hosts_K. split; [exact Hb|]. intros ->. exact (NE (hosts_fun _ _ _ _ Hb g_hosts)).
Qed.
Lemma g_unlisted_K h : ~ In g (LS h).
Proof. exact (lists_notin st LS (old_lists _ _ _ _ _ INV) g NL h). Qed.

(* [comment removed for export] *)
Lemma p_not_gslot : ~ gslot p.
Proof.
  ((first [ intro dR_40; dex1 dR_40 as j; destruct dR_40 as [Hj E] | intro dR_40; dand3 dR_40 as j Hj E | intros (j & Hj & E) ])). rewrite slot_g in E. pose proof stride_pos.
  assert (snd p = snd p + UNIT + get_stride (MR st g) * j) by (rewrite E at 1; reflexivity). unfold UNIT in *. nia.
Qed.
Lemma slots_pos s m j : s_slots st !! s = Some (m, j) -> 0 < snd s.
Proof.
  intros Hs. (first [ pose proof ((is_valid _ _ _ IS _ _ _ Hs)) as dR_6; dand3 dR_6 as [b Hb] Hj -> | destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & Hj & ->) ]). rewrite (slot_start'_eq _ _ _ IM _ _ _ Hb). cbn.
  pose proof (sstart0 _ _ _ IM _ _ Hb). pose proof (sstart_mono _ _ _ IG _ _ 0 j Hb ltac:(lia)).
  (first [ pose proof ((hosts_ok _ _ _ IG _ _ Hb)) as dR_7; dex1 dR_7 as a; destruct dR_7 as [_ GOm] | pose proof ((hosts_ok _ _ _ IG _ _ Hb)) as dR_7; dand3 dR_7 as a _ GOm | destruct (hosts_ok _ _ _ IG _ _ Hb) as (a & _ & GOm) ]). pose proof (g_align _ _ _ _ _ _ GOm) as [A _]. unfold UNIT in *. lia.
Qed.

(* [comment removed for export] *)
Lemma top_region_empty b h : m_maplen (MR st g) <> 0 -> s_groups st !! b = Some h -> fst b = fst p -> b = p.
Proof.
  intros Hml Hb Hf. (first [ pose proof ((im_hdr _ _ _ IM _ _ Hb)) as dR_8; dex1 dR_8 as m; dand3 dR_8 as Em Hmem _ | pose proof ((im_hdr _ _ _ IM _ _ Hb)) as dR_8; dand4 dR_8 as m Em Hmem _ | destruct (im_hdr _ _ _ IM _ _ Hb) as (m & Em & Hmem & _) ]).
  assert (Hm : hosts st b m) by (destruct h as [hm ha]; cbn in Em; subst hm; exists ha; exact Hb).
  destruct (aptr_eq_dec m g) as [->|NE]; [exact (hosts_inj _ _ _ IM _ _ _ Hm g_hosts)|]. exfalso.
  destruct (Z.eq_dec (m_maplen (MR st m)) 0) as [Hml'|Hml'].
  - (first [ pose proof ((@top_chain _ _ _ _ IM IG IS m b Hm Hml')) as dR_9; dex4 dR_9 as t j c bt; dand4 dR_9 as Ha Ht Htop Hft | pose proof ((@top_chain _ _ _ _ IM IG IS m b Hm Hml')) as dR_9; dand8 dR_9 as t j c bt Ha Ht Htop Hft | destruct (@top_chain _ _ _ _ IM IG IS m b Hm Hml') as (t & j & c & bt & Ha & Ht & Htop & Hft) ]).
    assert (t = g) by (apply (@top_unique _ _ _ IG t g bt p Ht g_hosts Htop Hml); congruence). subst t.
    (first [ pose proof ((@anc_hostslot _ _ _ _ IM IG IS m g j c Ha)) as dR_10; dex1 dR_10 as bp; destruct dR_10 as [Hp Hsl] | pose proof ((@anc_hostslot _ _ _ _ IM IG IS m g j c Ha)) as dR_10; dand3 dR_10 as bp Hp Hsl | destruct (@anc_hostslot _ _ _ _ IM IG IS m g j c Ha) as (bp & Hp & Hsl) ]).
    pose proof (hosts_inj _ _ _ IM _ _ _ Hp g_hosts). subst bp.
    (first [ pose proof ((@anc_facts _ _ _ _ IM IG IS m g j c Ha)) as dR_11; dex2 dR_11 as bm' bp'; dand5 dR_11 as _ _ _ Hj _ | pose proof ((@anc_facts _ _ _ _ IM IG IS m g j c Ha)) as dR_11; dand7 dR_11 as bm' bp' _ _ _ Hj _ | destruct (@anc_facts _ _ _ _ IM IG IS m g j c Ha) as (bm' & bp' & _ & _ & _ & Hj & _) ]).
    (first [ pose proof ((g_slot_free j Hj)) as dR_12; dand3 dR_12 as _ N _ | destruct (g_slot_free j Hj) as (_ & N & _) ]). exact (Hsl N).
  - apply NE. apply (@top_unique _ _ _ IG m g b p Hm g_hosts Hml' Hml Hf).
Qed.

Lemma gcnt_K sc' : gcnt st sc' = (if sc =? sc' then cnt else 0) + gcnt st' sc'.
Proof.
  rewrite (gcnt_delete st st' p _ sc' Hg K_groups K_metas). unfold gterm. cbn. fold sc. fold cnt. reflexivity.
Qed.

Theorem INVL_kill : INVL X' st' L BL LS.
Proof.
  pose proof GO as GOg. pose proof g_hosts as Hgh.
  assert (NGm : forall b m, hosts st b m -> m <> g -> b <> p).
  { intros b m Hm NE ->. exact (NE (hosts_fun _ _ _ _ Hm g_hosts)). }
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - (* [comment removed for export] *) destruct IR; constructor; rewrite ?K_regions, ?K_next_rid, ?K_reserved; try assumption.
    + eapply Permutation_trans; [exact ir_metas|]. erewrite map_ext; [apply Permutation_refl|]. intros [rid r]; cbn. rewrite K_frontier. reflexivity.
    + intros rid r H1 H2. rewrite K_frontier. exact (ir_metalen rid r H1 H2).
    + intros rid r H1 H2. rewrite K_frontier. exact (ir_brkfront rid r H1 H2).
    + apply (K_c (fun c => 0 <= c_meta_alloc_shift c /\ (c_meta_alloc_shift c = 0 \/ exists rid r, s_regions st !! rid = Some r /\ r_kind r = RKMeta /\ r_len r = 2 ^ c_meta_alloc_shift c * PGSZ))); [intros c U H; exact H| exact ir_shift].
    + apply (K_c (fun c => match c_brk c with
                           | BrkUntried => ld_brk L = BPUntried /\ forall rid r, s_regions st !! rid = Some r -> r_kind r <> RKBrk
                           | BrkDead => ld_brk L = BPDead
                           | BrkLive rid off => ld_brk L = BPLive /\ exists r, s_regions st !! rid = Some r /\ r_kind r = RKBrk /\ r_len r = off end));
        [intros c U H; exact H| exact ir_brk].
    + apply (K_c (fun c => 0 <= c_avail_meta_area_count c /\
        (0 < c_avail_meta_area_count c -> c_avail_meta_areas c <> None) /\
        (forall rid off, c_avail_meta_areas c = Some (rid, off) -> exists r, s_regions st !! rid = Some r /\ is_metakind r /\ PGSZ <= off /\ off mod PGSZ = 0
           /\ off + c_avail_meta_area_count c * PGSZ = r_len r /\ (0 < c_avail_meta_area_count c -> r_kind r = RKMeta))));
        [intros c U H; exact H| exact ir_cursor].
    + intros rid Ho. unfold X' in Ho. cbn in Ho. unfold nested in Ho. destruct (Z.eqb_spec (m_maplen (MR st g)) 0) as [E|NE]; [discriminate|].
      inversion Ho. subst rid. (first [ pose proof ((g_top _ _ _ _ _ _ GOg NE)) as dR_13; dand5 dR_13 as H0 r Hr Hk _ | destruct (g_top _ _ _ _ _ _ GOg NE) as (H0 & r & Hr & Hk & _) ]). exists r. split; [exact Hr|]. split; [exact Hk|].
      intros b Hb. rewrite K_groups. destruct (aptr_eq_dec b p) as [->|NEb]; [apply lookup_delete_eq|]. rewrite lookup_delete_ne by congruence.
      destruct (s_groups st !! b) eqn:Eb; [| reflexivity]. exfalso. exact (NEb (top_region_empty b _ NE Eb Hb)).
  - (* [comment removed for export] *) (first [ dex16 K_cf as cf1 cf2 cf3 cf4 cf5 cf6 cf7 cf8 cf9 cf10 cf11 cf12 cf13 cf14 cf15 cf16; rename K_cf into cf17 | dand17 K_cf as cf1 cf2 cf3 cf4 cf5 cf6 cf7 cf8 cf9 cf10 cf11 cf12 cf13 cf14 cf15 cf16 cf17 | destruct K_cf as (cf1 & cf2 & cf3 & cf4 & cf5 & cf6 & cf7 & cf8 & cf9 & cf10 & cf11 & cf12 & cf13 & cf14 & cf15 & cf16 & cf17) ]).
    destruct IA; constructor; rewrite ?K_regions, ?K_areas, ?K_secret, ?K_metas, ?cf1, ?cf2, ?cf3, ?cf4, ?cf5, ?cf6, ?cf7, ?cf8, ?cf9, ?cf10, ?cf11, ?cf12, ?cf13, ?cf14, ?cf15, ?cf16, ?cf17; try assumption.
    + intros a ar Ha. destruct (ia_areas a ar Ha) as ((r & ? & ? & ? & ? & ?) & ? & ? & ?). split; [| auto]. exists r. rewrite K_frontier. auto.
    + intros sc' Hsc'. rewrite K_usage, (U1 sc' Hsc').
      pose proof (gcnt_K sc') as GK. rewrite <- (ia_usage sc' Hsc') in GK. rewrite Z.eqb_sym in GK.
      destruct (Z.eqb_spec sc' sc) as [E|NE]; [rewrite <- E; lia| lia].
  - (* [comment removed for export] *) destruct IM as [M1 M2 M3 M4 M5] eqn:EIM; constructor; rewrite ?K_MR.
    + intros m Hm. rewrite !K_MR. apply M1. rewrite <- (K_MR m). exact Hm.
    + intros m b Hm. rewrite K_MR in Hm. destruct (aptr_eq_dec m g) as [->|NE]; [right; left; reflexivity|].
      destruct (M2 m b Hm) as [H|H]; [left| right; right; exact H]. apply hosts_K. split; [exact H|]. exact (NGm b m H NE).
    + intros b h Hb. rewrite K_groups in Hb. apply lookup_delete_Some in Hb as [NE Hb]. destruct (M3 b h Hb) as (m & ? & ? & ?). exists m. rewrite !K_MR. auto.
    + intros m Hm. rewrite K_metas. exact (M4 m Hm).
    + intros z Hz. rewrite !K_MR, K_groups. cbn in Hz. destruct Hz as [<-|Hz].
      * split; [intros [h Hh]; exact (g_unlisted_K h Hh)|]. split; [exact NL|].
        split; [exact (proj2 (il_link _ _ IL g) NL)|].
        exists p. split; [exact (hosts_mem _ _ _ IM _ _ g_hosts)| apply lookup_delete_eq].
      * (first [ pose proof ((M5 z Hz)) as dR_15; dand6 dR_15 as A1 A2 A3 b A4 A5 | destruct (M5 z Hz) as (A1 & A2 & A3 & b & A4 & A5) ]). split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
        exists b. split; [exact A4|]. destruct (aptr_eq_dec b p) as [->|NE]; [apply lookup_delete_eq| rewrite lookup_delete_ne by congruence; exact A5].
  - (* [comment removed for export] *) destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9] eqn:EIL; constructor; try assumption.
    + intros h. rewrite K_get_head. apply L1.
    + intros h. apply (dll_ext_metas st st' K_metas). apply L2.
    + intros m. rewrite !K_MR. apply L5.
    + intros m Hm. rewrite !K_MR. apply L6. exact Hm.
    + intros sc0 m Hm. (first [ pose proof ((L7 sc0 m Hm)) as dR_16; dand3 dR_16 as A1 A2 A3 | destruct (L7 sc0 m Hm) as (A1 & A2 & A3) ]). rewrite K_MR. split; [exact A1|]. split; [| exact A3].
      apply live_K; [exact A2|]. intros ->. exact (g_unlisted_K _ Hm).
  - (* [comment removed for export] *) destruct IG as [G1 G2 G3 G4 G5] eqn:EIG. constructor.
    + intros m b aim Hb. rewrite K_groups in Hb. apply lookup_delete_Some in Hb as [NEb Hb]. pose proof (G1 m b aim Hb) as GOm.
      assert (NEm : m <> g) by (intros ->; apply NEb; symmetry; exact (hosts_inj _ _ _ IM _ _ _ (ex_intro _ aim Hb) g_hosts)).
      assert (NF : x_fresh X <> Some m) by (rewrite HF; congruence).
      destruct GOm; constructor; rewrite ?K_MR, ?K_metas, ?K_regions; try assumption.
      * intros _. exact (g_partial NF).
      * intros _. exact (g_unlisted NF).
      * intros _. exact (g_rest NF).
      * intros _. exact (g_under NF).
      * intros Hml. (first [ pose proof ((g_nest Hml)) as dR_17; dex2 dR_17 as pm i'; destruct dR_17 as [Hs REST] | pose proof ((g_nest Hml)) as dR_17; dand4 dR_17 as pm i' Hs REST | destruct (g_nest Hml) as (pm & i' & Hs & REST) ]). exists pm, i'. rewrite !K_MR. split; [| exact REST].
        rewrite K_slots_other; [exact Hs|]. apply (entry_not_g _ _ _ Hs). intros ->.
        (first [ pose proof ((is_valid _ _ _ IS _ _ _ Hs)) as dR_18; dand3 dR_18 as _ Hi' Eb | destruct (is_valid _ _ _ IS _ _ _ Hs) as (_ & Hi' & Eb) ]).
        destruct (g_slot_free' i' Hi') as [_ N]. rewrite <- Eb, Hb in N. discriminate.
    + intros b aim Hb. rewrite K_groups in Hb. apply lookup_delete_Some in Hb as [_ Hb]. exact (G2 b aim Hb).
    + intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite K_groups in H1, H2. apply lookup_delete_Some in H1 as [_ H1]. apply lookup_delete_Some in H2 as [_ H2].
      rewrite !K_MR. eapply G3; eassumption.
    + intros rid r Hr Hk Ho. rewrite K_regions in Hr. (first [ pose proof ((G4 rid r Hr Hk ltac:(rewrite HO; discriminate))) as dR_19; dex1 dR_19 as m; destruct dR_19 as [Hm Hml] | pose proof ((G4 rid r Hr Hk ltac:(rewrite HO; discriminate))) as dR_19; dand3 dR_19 as m Hm Hml | destruct (G4 rid r Hr Hk ltac:(rewrite HO; discriminate)) as (m & Hm & Hml) ]). exists m. rewrite K_MR. split; [| exact Hml].
      apply hosts_K. split; [exact Hm|]. intros E.
      assert (Em : m = g) by (apply (hosts_fun st p); [rewrite <- E; exact Hm| exact g_hosts]). subst m.
      unfold X' in Ho. cbn in Ho. unfold nested in Ho. rewrite (proj2 (Z.eqb_neq _ _) Hml) in Ho. apply Ho. rewrite <- E. reflexivity.
    + intros b h Hb. rewrite K_groups in Hb. apply lookup_delete_Some in Hb as [_ Hb]. rewrite K_regions. exact (G5 b h Hb).
  - (* [comment removed for export] *) destruct IS as [S1' S2 S3 S4 S5 S6] eqn:EIS. constructor.
    + intros s m j Hs. destruct (K_slots_some _ _ Hs) as [Hs0 NG]. (first [ pose proof ((S1' s m j Hs0)) as dR_20; dand3 dR_20 as Hl Hj Es | destruct (S1' s m j Hs0) as (Hl & Hj & Es) ]). rewrite !K_MR.
      assert (NEm : m <> g) by (intros ->; exact (NG (entry_g_gslot _ _ Hs0))).
      split; [exact (live_K m Hl NEm)|]. auto.
    + intros b m j Hb Hj. rewrite K_MR in Hj |- *. apply hosts_K in Hb as [Hb NEb].
      assert (NEm : m <> g) by (intros ->; exact (NEb (hosts_inj _ _ _ IM _ _ _ Hb g_hosts))).
      rewrite K_slots_other; [exact (S2 b m j Hb Hj)|]. exact (other_slot_not_g m b j Hb NEm Hj).
    + intros b m aim j Hb Hj. rewrite K_groups in Hb. apply lookup_delete_Some in Hb as [NEb Hb]. rewrite K_MR in Hj. rewrite !K_MR, K_groups. unfold X'. cbn [x_pend].
      assert (Hbm : hosts st b m) by (exists aim; exact Hb).
      assert (NEm : m <> g) by (intros ->; apply NEb; symmetry; exact (hosts_inj _ _ _ IM _ _ _ Hbm g_hosts)).
      pose proof (S3 b m aim j Hb Hj) as P. cbn zeta in P |- *.
      set (s := slot_start' (MR st m) j) in *.
      assert (OP : ~ (x_pend X = Some s)).
      { rewrite HP. intros E. apply (other_slot_not_g m b j Hbm NEm Hj). exists i. split; [unfold cnt; lia|].
        rewrite (slot_start'_eq _ _ _ IM _ _ _ g_hosts). apply (inj Some) in E. rewrite E. reflexivity. }
      unfold one5 in P |- *.
      (first [ dand11 P as P0 nAB nAC nAD nAE nBC nBD nBE nCD nCE nDE | destruct P as (P0 & nAB & nAC & nAD & nAE & nBC & nBD & nBE & nCD & nCE & nDE) ]).
      destruct (aptr_eq_dec s p) as [Esp|NEsp].
      * assert (Hn : nested = true).
        { unfold nested. apply Z.eqb_eq. destruct (Z.eq_dec (m_maplen (MR st g)) 0) as [E|NE]; [exact E|]. exfalso.
          destruct (g_top _ _ _ _ _ _ GOg NE) as [H0 _]. pose proof (slots_pos s m j (S2 b m j Hbm Hj)) as SP. rewrite Esp in SP. lia. }
        rewrite Hn. rewrite Esp in *. rewrite lookup_delete_eq.
        assert (D : s_groups st !! p <> None) by (rewrite Hg; discriminate).
        assert (nA : ~ tbit (m_avail (MR st m)) j = true) by (intros A; exact (nAD (conj A D))).
        assert (nB : ~ tbit (m_freed (MR st m)) j = true) by (intros B; exact (nBD (conj B D))).
        assert (nC : ~ In p (map bslot BL)) by (intros C; exact (nCD (conj C D))).
        clear - nA nB nC. assert (NN : ~ (@None ghdr <> None)) by (intros H; apply H; reflexivity). tauto.
      * rewrite lookup_delete_ne by congruence.
        assert (NP' : ~ ((if nested then Some p else None) = Some s)) by (destruct nested; [intros E; inversion E; congruence| discriminate]).
        revert P0 nAB nAC nAD nAE nBC nBD nBE nCD nCE nDE OP NP'. clear.
        generalize (tbit (m_avail (MR st m)) j = true) (tbit (m_freed (MR st m)) j = true) (In s (map bslot BL)) (s_groups st !! s <> None).
        generalize ((if nested then Some p else None) = Some s) (x_pend X = Some s). intros. tauto.
    + intros s Hs. unfold X' in Hs. cbn [x_pend] in Hs. unfold nested in Hs. destruct (Z.eqb_spec (m_maplen (MR st g)) 0) as [Hml|Hml]; [| discriminate]. inversion Hs. subst s.
      (first [ pose proof ((g_nest _ _ _ _ _ _ GOg Hml)) as dR_22; dex2 dR_22 as pm ip; destruct dR_22 as [Hs0 _] | pose proof ((g_nest _ _ _ _ _ _ GOg Hml)) as dR_22; dand4 dR_22 as pm ip Hs0 _ | destruct (g_nest _ _ _ _ _ _ GOg Hml) as (pm & ip & Hs0 & _) ]). rewrite K_slots_other; [rewrite Hs0; discriminate| exact p_not_gslot].
    + exact S5.
    + intros k Hk. (first [ pose proof ((S6 k Hk)) as dR_23; dex2 dR_23 as m j; destruct dR_23 as [Hs REST] | pose proof ((S6 k Hk)) as dR_23; dand4 dR_23 as m j Hs REST | destruct (S6 k Hk) as (m & j & Hs & REST) ]). exists m, j. rewrite K_MR. split; [| exact REST].
      rewrite K_slots_other; [exact Hs|]. intros G. (first [ pose proof ((gslot_range _ G)) as dR_24; dex1 dR_24 as j'; destruct dR_24 as [Hj' E] | pose proof ((gslot_range _ G)) as dR_24; dand3 dR_24 as j' Hj' E | destruct (gslot_range _ G) as (j' & Hj' & E) ]).
      destruct (g_slot_free' j' Hj') as [NB _]. apply NB. rewrite <- E. apply in_map_iff. exists k. auto.
  - (* [comment removed for export] *) destruct ISH as [D1 D2 D3 D4 D5 D6] eqn:EISH.
    assert (KN : forall q v, known st q v -> known st' q v).
    { intros q v. unfold known, SHd, get_shadow. rewrite K_shadow. exact (fun H => H). }
    assert (UN : forall q, unknown st q -> unknown st' q).
    { intros q. unfold unknown, SHd, get_shadow. rewrite K_shadow. exact (fun H => H). }
    constructor.
    + intros rid sh Hsh. rewrite K_shadow in Hsh. rewrite K_regions. exact (D1 rid sh Hsh).
    + intros rid sh Hsh. rewrite K_shadow in Hsh. rewrite K_tick. exact (D2 rid sh Hsh).
    + intros b m j Hb Hj. apply hosts_K in Hb as [Hb _]. rewrite K_MR in Hj |- *. apply KN. exact (D3 b m j Hb Hj).
    + intros b m o Hb Ho. apply hosts_K in Hb as [Hb _]. apply UN. exact (D4 b m o Hb Ho).
    + intros b m pm j Hb Hml Hs. apply hosts_K in Hb as [Hb _]. rewrite K_MR in Hml. destruct (K_slots_some _ _ Hs) as [Hs0 _]. rewrite !K_MR.
      (first [ pose proof ((D5 b m pm j Hb Hml Hs0)) as dR_25; dand4 dR_25 as (v3 & K3 & E3 & R3) K2 K1 Q | destruct (D5 b m pm j Hb Hml Hs0) as ((v3 & K3 & E3 & R3) & K2 & K1 & Q) ]). cbn zeta.
      split; [exists v3; auto|]. auto.
    + intros k m j Hk Hs. destruct (K_slots_some _ _ Hs) as [Hs0 _]. rewrite !K_MR. pose proof (D6 k m j Hk Hs0) as B. cbn zeta in B |- *.
      (first [ dand8 B as A1 A2 A3 A4 A5 A6 A7 A8 | destruct B as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8) ]).
      split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [exact A5|]. split.
      * intros Hres. (first [ pose proof ((A6 Hres)) as dR_27; dand6 dR_27 as B1 B2 B3 B4 B5 B6 | destruct (A6 Hres) as (B1 & B2 & B3 & B4 & B5 & B6) ]). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto.
      * split; [intros Hres; apply KN; apply A7; exact Hres|]. intros a Ha. apply UN. apply A8. exact Ha.
Qed.

Lemma kill_top : m_maplen (MR st g) <> 0 ->
  exists r, snd p = 0 /\ s_regions st' !! (fst p) = Some r /\ r_kind r = RKGroup
    /\ m_maplen (MR st g) * 4096 = round_up_pg (r_len r) /\ 0 < m_maplen (MR st g) * 4096.
Proof.
  intros Hml. (first [ pose proof ((g_top _ _ _ _ _ _ GO Hml)) as dR_28; dand6 dR_28 as H0 r Hr Hk E _ | destruct (g_top _ _ _ _ _ _ GO Hml) as (H0 & r & Hr & Hk & E & _) ]). exists r. rewrite K_regions.
  (first [ pose proof ((ir_shape _ _ _ IR _ _ Hr)) as dR_29; dand4 dR_29 as _ _ L0 _ | pose proof (ir_shape _ _ _ IR _ _ Hr) as (_ & _ & L0 & _) ]). pose proof (round_up_ge_k (r_len r)). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto. lia.
Qed.

Lemma kill_nested : m_maplen (MR st g) = 0 ->
  exists pm ip bpm, s_slots st' !! p = Some (pm, ip) /\ hosts st' bpm pm /\ fst bpm = fst p
    /\ 0 <= ip <= m_last_idx (MR st pm) /\ p = (fst bpm, sstart (MR st pm) ip)
    /\ m_sizeclass (MR st g) < m_sizeclass (MR st pm) < 48
    /\ get_stride (MR st pm) = UNIT * size_class (m_sizeclass (MR st pm))
    /\ gend (MR st g) <= sstart (MR st pm) ip + get_stride (MR st pm).
Proof.
  intros Hml. (first [ pose proof ((g_nest _ _ _ _ _ _ GO Hml)) as dR_30; dex2 dR_30 as pm ip; dand5 dR_30 as Hs Hf He Hsc Hstr | pose proof ((g_nest _ _ _ _ _ _ GO Hml)) as dR_30; dand7 dR_30 as pm ip Hs Hf He Hsc Hstr | destruct (g_nest _ _ _ _ _ _ GO Hml) as (pm & ip & Hs & Hf & He & Hsc & Hstr) ]).
  (first [ pose proof ((is_valid _ _ _ IS _ _ _ Hs)) as dR_31; dand3 dR_31 as [bpm Hpm] Hip Ep | destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bpm Hpm] & Hip & Ep) ]).
  exists pm, ip, bpm.
  assert (NE : pm <> g) by (intros ->; lia).
  split; [rewrite K_slots_other; [exact Hs| exact p_not_gslot]|].
  split; [apply hosts_K; split; [exact Hpm|]; intros ->; exact (NE (hosts_fun _ _ _ _ Hpm g_hosts))|].
  rewrite (slot_start'_eq _ _ _ IM _ _ _ Hpm) in Ep.
  split; [rewrite Ep; reflexivity|]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto; lia.
Qed.

(* [comment removed for export] *)
Lemma dec_hdr_eq {T} (k : aptr -> Z -> M T) bail :
  m_maplen (MR st g) = 0 ->
  exists pm ip bpm, dec_hdr st' p k bail = k pm ip
    /\ s_slots st' !! p = Some (pm, ip) /\ hosts st' bpm pm /\ fst bpm = fst p
    /\ 0 <= ip <= m_last_idx (MR st pm) /\ p = (fst bpm, sstart (MR st pm) ip)
    /\ m_sizeclass (MR st g) < m_sizeclass (MR st pm) < 48.
Proof.
  intros Hml. (first [ pose proof ((kill_nested Hml)) as dR_32; dex3 dR_32 as pm ip bpm; dand8 dR_32 as Hs' Hpm' Hf Hip Ep Hsc Hstr Hend | pose proof ((kill_nested Hml)) as dR_32; dand11 dR_32 as pm ip bpm Hs' Hpm' Hf Hip Ep Hsc Hstr Hend | destruct (kill_nested Hml) as (pm & ip & bpm & Hs' & Hpm' & Hf & Hip & Ep & Hsc & Hstr & Hend) ]).
  exists pm, ip, bpm. split; [| OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto; lia].
  pose proof Hpm' as Hpm. apply hosts_K in Hpm as [Hpm NEb].
  (first [ pose proof ((hosts_ok _ _ _ IG _ _ Hpm)) as dR_33; dex1 dR_33 as aipm; destruct dR_33 as [Hgpm GOpm] | pose proof ((hosts_ok _ _ _ IG _ _ Hpm)) as dR_33; dand3 dR_33 as aipm Hgpm GOpm | destruct (hosts_ok _ _ _ IG _ _ Hpm) as (aipm & Hgpm & GOpm) ]).
  assert (Hs : s_slots st !! p = Some (pm, ip)) by (destruct (K_slots_some _ _ Hs') as [H _]; exact H).
  (* [comment removed for export] *)
  pose proof (ish_nest _ _ ISH p g pm ip g_hosts Hml Hs) as NS. cbn zeta in NS. rewrite (hosts_gbase _ _ _ IM _ _ Hpm) in NS.
  set (q := (snd p - snd bpm - UNIT) / UNIT) in NS.
  (first [ dand4 NS as (v3 & K3 & E3 & R3) K2 K1 Q | destruct NS as ((v3 & K3 & E3 & R3) & K2 & K1 & Q) ]).
  pose proof (ish_hdr0 _ _ ISH bpm pm ip Hpm ltac:(unfold cnt_of; lia)) as K4.
  assert (KN : forall a v, known st a v -> known st' a v).
  { intros a v. unfold known, SHd, get_shadow. rewrite K_shadow. exact (fun H => H). }
  assert (Hq : UNIT * q = get_stride (MR st pm) * ip).
  { subst q. rewrite Ep. cbn [snd]. unfold sstart. rewrite (hosts_gbase _ _ _ IM _ _ Hpm).
    replace (snd bpm + UNIT + get_stride (MR st pm) * ip - snd bpm - UNIT) with (size_class (m_sizeclass (MR st pm)) * ip * UNIT) by (rewrite Hstr; lia).
    rewrite Hstr. unfold UNIT. rewrite Z.div_mul by lia. lia. }
  clearbody q.
  pose proof (g_align _ _ _ _ _ _ GOpm) as [A0 A16].
  unfold dec_hdr, get_meta.
  rewrite (guard_true 10).
  2:{ apply Z.eqb_eq. rewrite Ep. cbn [snd]. unfold sstart. rewrite (hosts_gbase _ _ _ IM _ _ Hpm), Hstr. unfold UNIT in *.
      replace (snd bpm + 16 + 16 * size_class (m_sizeclass (MR st pm)) * ip) with (snd bpm + (1 + size_class (m_sizeclass (MR st pm)) * ip) * 16) by lia.
      rewrite Z_mod_plus_full. exact A16. }
  unfold rd16.
  rewrite (rd8_known st' (aadd p (-2)) (byte_of q 0)) by (eapply known_at; [apply KN; exact K2| cbn; lia| reflexivity]).
  rewrite (rd8_known st' (aadd (aadd p (-2)) 1) (byte_of q 1)) by (eapply known_at; [apply KN; exact K1| cbn; lia| reflexivity]).
  rewrite (rd8_known st' (aadd p (-3)) v3) by (eapply known_at; [apply KN; exact K3| cbn; lia| reflexivity]).
  rewrite (rd8_known st' (aadd p (-4)) 0).
  2:{ eapply known_at; [apply KN; exact K4| rewrite Ep; cbn; unfold IB; lia| rewrite Ep; reflexivity]. }
  cbn [Z.eqb negb].
  rewrite (u16_bytes q Q).
  assert (Ebase : aadd p (- (UNIT * q) - UNIT) = bpm).
  { rewrite Ep. unfold aadd, sstart. rewrite (hosts_gbase _ _ _ IM _ _ Hpm). destruct bpm as [br bo]. cbn [fst snd] in *. f_equal. lia. }
  rewrite Ebase. unfold get_group. destruct Hpm' as [ai' Hg']. rewrite Hg'. cbn [g_meta]. rewrite E3. fold (MR st' pm). rewrite !K_MR.
  rewrite (guard_true 11) by (rewrite (hosts_mem _ _ _ IM _ _ Hpm); apply optr_eqb_refl).
  rewrite (guard_true 12) by (apply Z.leb_le; lia).
  pose proof (is_part _ _ _ IS _ _ _ ip Hgpm Hip) as P. cbn zeta in P. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hpm), <- Ep in P. unfold one5 in P.
  assert (D : s_groups st !! p <> None) by (rewrite Hg; discriminate).
  rewrite (guard_true 13) by (unfold testbit; destruct (Z.testbit (m_avail (MR st pm)) ip) eqn:E; [exfalso; unfold tbit in P; tauto| reflexivity]).
  rewrite (guard_true 14) by (unfold testbit; destruct (Z.testbit (m_freed (MR st pm)) ip) eqn:E; [exfalso; unfold tbit in P; tauto| reflexivity]).
  pose proof (g_present _ _ _ _ _ _ GOpm) as Pr. destruct (s_metas st !! pm) as [mr|] eqn:Em; [| congruence].
  (first [ pose proof ((ia_metas _ IA _ _ Em)) as dR_35; dex3 dR_35 as a ar ka; dand3 dR_35 as Ha Hka Emk | pose proof ((ia_metas _ IA _ _ Em)) as dR_35; dand6 dR_35 as a ar ka Ha Hka Emk | destruct (ia_metas _ IA _ _ Em) as (a & ar & ka & Ha & Hka & Emk) ]).
  (first [ pose proof ((ia_areas _ IA _ _ Ha)) as dR_36; dand4 dR_36 as (r & Hr & Hmk & Hal & Hpg & Hfr) Hck Hns _ | destruct (ia_areas _ IA _ _ Ha) as ((r & Hr & Hmk & Hal & Hpg & Hfr) & Hck & Hns & _) ]).
  destruct K_cf as (cf1 & _).
  rewrite (guard_true 15) by (rewrite K_areas, Emk, (area_of_mslot a ka Hal Hka), Ha; apply Z.eqb_eq; unfold ctx; rewrite cf1; exact Hck).
  pose proof (size_class_bound (m_sizeclass (MR st pm))) as SB.
  rewrite (guard_true 16).
  2:{ clear KN K2 K1 K3 K4 P D Ebase. destruct (Z.ltb_spec (m_sizeclass (MR st pm)) 48); [| lia]. rewrite Hstr in Hq.
      assert (Eq : q = size_class (m_sizeclass (MR st pm)) * ip) by (unfold UNIT in Hq; lia).
      assert (G0 : 0 <= m_sizeclass (MR st g)) by (destruct (g_sc _ _ _ _ _ _ GO) as [[[G0 _] _]|(G63 & _)]; lia).
      rewrite Eq. specialize (SB ltac:(lia)). apply Bool.andb_true_iff. split; [apply Z.leb_le; lia| apply Z.ltb_lt]. rewrite Z.mul_add_distr_l. lia. }
  rewrite (guard_true 17).
  2:{ destruct (Z.eqb_spec (m_maplen (MR st pm)) 0) as [|NM]; cbn [negb]; [reflexivity|].
      (first [ pose proof ((g_top _ _ _ _ _ _ GOpm NM)) as dR_37; dand6 dR_37 as B0 _ _ _ _ GE | destruct (g_top _ _ _ _ _ _ GOpm NM) as (B0 & _ & _ & _ & _ & GE) ]). apply Z.leb_le.
      unfold gend, cnt_of, sstart in GE. rewrite (hosts_gbase _ _ _ IM _ _ Hpm), B0 in GE.
      pose proof (stride_ge _ _ _ IG _ _ Hpm) as [S16 _]. unfold UNIT in S16, Hq, GE.
      clear KN K2 K1 K3 K4 P D Ebase SB.
      eapply (guard17_arith (get_stride (MR st pm)) ip 0 0 q (m_last_idx (MR st pm)) (m_maplen (MR st pm))); try lia. }
  reflexivity.
Qed.
End KILL.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma fg_st1 X st L BL LS g p ai (INV : INVL X st L BL LS) (Hg : s_groups st !! p = Some (mkGhdr (Some g) ai)) :
  let sc := m_sizeclass (MR st g) in
  let cnt := m_last_idx (MR st g) + 1 in
  let st1 := if sc <? 48 then set_usage sc (usage st sc - cnt) st else st in
  (exists U, st1 = upd_ctx (fun c => set_usage_map U c) st)
  /\ (forall sc', 0 <= sc' < 48 -> usage st1 sc' = if sc' =? sc then usage st sc - cnt else usage st sc')
  /\ (forall sc0 v, c_usage (s_ctx st1) !! sc0 = Some v -> 0 <= sc0 < 48).
Proof.
  cbn zeta. pose proof (ia_usage_keys _ (proj1 (proj2 INV))) as UK.
  pose proof (g_sc _ _ _ _ _ _ (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hg)) as SC.
  destruct (Z.ltb_spec (m_sizeclass (MR st g)) 48) as [LT|GE].
  - split; [eexists; reflexivity|]. split.
    + intros sc' Hsc'. apply usage_set_usage.
    + intros sc0 v. cbn. destruct (Z.eq_dec sc0 (m_sizeclass (MR st g))) as [->|NE].
      * intros _. destruct SC as [[A _]|(A & _)]; lia.
      * rewrite lookup_insert_ne by congruence. apply UK.
  - split; [| split; [| exact UK]].
    + exists (c_usage (s_ctx st)). destruct st as [c ? ? ? ? ? ? ? ? ? ?]; destruct c; reflexivity.
    + intros sc' Hsc'. destruct (Z.eqb_spec sc' (m_sizeclass (MR st g))); [lia| reflexivity].
Qed.

End CEIL.
End MI_WKill.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall7vg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List.MI_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Arith OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Geom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ext OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2.MI_Ext2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_S421 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.MI_Read OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2.MI_Pres1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres4.MI_Pres3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ws22 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WNtf.MI_WKill.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma one5_iff (A B C D E A' B' C' D' E' : Prop) :
  (A <-> A') -> (B <-> B') -> (C <-> C') -> (D <-> D') -> (E <-> E') -> one5 A B C D E -> one5 A' B' C' D' E'.
Proof. unfold one5. tauto. Qed.
(* [comment removed for export] *)
Lemma one5_E_to_B (A B C D E B' E' : Prop) : E -> B' -> ~ E' -> one5 A B C D E -> one5 A B' C D E'.
Proof. unfold one5. tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AOR.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (g bg : aptr) (ai i : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : s_groups st !! bg = Some (mkGhdr (Some g) ai).
Hypothesis Hi : 0 <= i <= m_last_idx (MR st g).
Hypothesis HP : x_pend X = Some (fst bg, sstart (MR st g) i).
Hypothesis C1 : x_fresh X <> Some g -> forall sc, In g (LS (LActive sc)) -> Some g <> head_of (LS (LActive sc)) -> m_avail (MR st g) = 0.
Hypothesis C2 : x_fresh X <> Some g -> m_sizeclass (MR st g) < 48 -> in_list LS g.
Hypothesis C3 : m_sizeclass (MR st g) < 48 -> UNIT * size_class (m_sizeclass (MR st g)) <= get_stride (MR st g).
Let st' := upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) (bit i)) r) st.

Lemma aor_form : st' = upd_meta g (fun r => m_set_avail (m_avail (MR st g)) (m_set_freed (Z.lor (m_freed (MR st g)) (bit i)) r)) st.
Proof. unfold st', upd_meta, MR. destruct (get_meta_rec st g); reflexivity. Qed.

Theorem INVL_aor : INVL (xpend X None) st' L BL LS.
Proof.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (ig_ok _ _ _ IG _ _ _ Hg) as GO. pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6).
  pose proof (g_li _ _ _ _ _ _ GO) as LI. pose proof (g_ai _ _ _ _ _ _ GO) as AI.
  assert (Hgh : hosts st bg g) by (exists ai; exact Hg).
  pose proof (is_part _ _ _ IS _ _ _ i Hg Hi) as Pi. cbn zeta in Pi. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hgh) in Pi.
  assert (NA : tbit (m_avail (MR st g)) i = false).
  { destruct (tbit (m_avail (MR st g)) i) eqn:E; [| reflexivity]. exfalso. unfold one5 in Pi. tauto. }
  assert (TB : forall j, 0 <= j -> tbit (Z.lor (m_freed (MR st g)) (bit i)) j = tbit (m_freed (MR st g)) j || (i =? j)).
  { intros j Hj. unfold tbit. rewrite Z.lor_spec, testbit_bit by lia. reflexivity. }
  assert (NZ : Z.lor (m_freed (MR st g)) (bit i) <> 0).
  { intros E. pose proof (TB i ltac:(lia)) as T. rewrite E, Z.eqb_refl, Bool.orb_true_r in T. unfold tbit in T. rewrite Z.bits_0 in T. discriminate. }
  rewrite aor_form.
  apply (INVL_mask_change X st L BL LS g bg ai (m_avail (MR st g)) (Z.lor (m_freed (MR st g)) (bit i)) None INV Hg).
  - split; [exact M1|]. split; [apply Z.lor_nonneg; split; [exact M2| unfold bit; apply Z.pow_nonneg; lia]|]. split; [exact M3|].
    split; [| split].
    + intros j Hj. rewrite TB by exact Hj. rewrite Bool.orb_true_iff. intros [H|H]; [exact (M4 j Hj H)| apply Z.eqb_eq in H; lia].
    + intros j Hj Ha. rewrite TB by exact Hj. rewrite Bool.orb_true_iff. intros [H|H]; [exact (M5 j Hj Ha H)| apply Z.eqb_eq in H; subst j; rewrite NA in Ha; discriminate].
    + intros j Hj. rewrite TB by lia. rewrite (M6 j Hj). reflexivity.
  - intros j Hj. cbn zeta. rewrite TB by lia.
    pose proof (is_part _ _ _ IS _ _ _ j Hg Hj) as P. cbn zeta in P. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hgh) in P |- *.
    destruct (Z.eqb_spec i j) as [<-|NE].
    + rewrite Bool.orb_true_r. eapply one5_E_to_B; [exact HP| reflexivity| discriminate| exact P].
    + rewrite Bool.orb_false_r. eapply one5_iff; [reflexivity| reflexivity| reflexivity| reflexivity| | exact P].
      rewrite HP. split; [intros E; exfalso| discriminate]. inversion E.
      destruct (Z.lt_total i j) as [LT|[EQ|LT]]; [| lia|].
      * pose proof (sstart_lt _ _ _ IG _ _ i j Hgh LT). pose proof (stride_ge _ _ _ IG _ _ Hgh) as [SG _]. unfold UNIT in *. lia.
      * pose proof (sstart_lt _ _ _ IG _ _ j i Hgh LT). pose proof (stride_ge _ _ _ IG _ _ Hgh) as [SG _]. unfold UNIT in *. lia.
  - right. split.
    + intros s Hs. rewrite HP in Hs. inversion Hs. subst s. exists i. split; [exact Hi|]. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hgh). reflexivity.
    + intros s Hs. discriminate.
  - intros NF sc Hin Hnh. split; [exact (C1 NF sc Hin Hnh)| exact NZ].
  - intros NF Hsc NI. exfalso. exact (NI (C2 NF Hsc)).
  - intros _ Hsc Hlt. exfalso. pose proof (C3 Hsc). lia.
Qed.
End AOR.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ACT.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (a ba : aptr) (aia : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Ha : s_groups st !! ba = Some (mkGhdr (Some a) aia).
Hypothesis AV0 : m_avail (MR st a) = 0.
Hypothesis HEAD : head_of (LS (LActive (m_sizeclass (MR st a)))) = Some a.
Let act := mask_upto aia.
Let A' := Z.land (m_freed (MR st a)) act.
Let F' := Z.ldiff (m_freed (MR st a)) act.
Let st' := upd_meta a (fun r => m_set_avail A' (m_set_freed F' r)) st.

Lemma act_eq : match m_mem (MR st a) with
               | Some _ => mask_upto (group_active_idx st (default (0%N, -1) (m_mem (MR st a))))
               | None => 0 end = act.
Proof.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  rewrite (hosts_mem _ _ _ IM _ _ (ex_intro _ aia Ha)). cbn. unfold group_active_idx, get_group. rewrite Ha.
  pose proof (g_ai _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Ha)) as AI. pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Ha)) as LI.
  unfold act. f_equal. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 5) with 32. lia.
Qed.

Lemma activate_group_eq {T} (k : mstate -> Z -> M T) bail : activate_group a st k bail = k st' A'.
Proof.
  unfold activate_group. fold (MR st a). rewrite AV0. cbn [guard Z.eqb]. rewrite act_eq. reflexivity.
Qed.

Lemma a_listed : In a (LS (LActive (m_sizeclass (MR st a)))).
Proof. destruct (LS (LActive (m_sizeclass (MR st a)))); cbn in HEAD; [discriminate|]. inversion HEAD. left. reflexivity. Qed.

Theorem INVL_activate : INVL X st' L BL LS.
Proof.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (ig_ok _ _ _ IG _ _ _ Ha) as GO. pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6).
  pose proof (g_li _ _ _ _ _ _ GO) as LI. pose proof (g_ai _ _ _ _ _ _ GO) as AI.
  assert (Hah : hosts st ba a) by (exists aia; exact Ha).
  assert (TA : forall j, 0 <= j -> tbit A' j = tbit (m_freed (MR st a)) j && (j <=? aia)).
  { intros j Hj. unfold A', act, tbit. rewrite Z.land_spec, testbit_mask_upto by lia. reflexivity. }
  assert (TF : forall j, 0 <= j -> tbit F' j = tbit (m_freed (MR st a)) j && negb (j <=? aia)).
  { intros j Hj. unfold F', act, tbit. rewrite Z.ldiff_spec, testbit_mask_upto by lia. reflexivity. }
  assert (X_eta : X = mkX (x_idle X) (x_zomb X) (x_pend X) (x_orph X) (x_fresh X)) by (destruct X; reflexivity).
  rewrite X_eta at 1.
  apply (INVL_mask_change X st L BL LS a ba aia A' F' (x_pend X) INV Ha).
  - split; [apply Z.land_nonneg; left; exact M2|]. split; [apply Z.ldiff_nonneg; left; exact M2|].
    split; [| split; [| split]].
    + intros j Hj. rewrite TA by exact Hj. rewrite Bool.andb_true_iff. intros [_ H]. apply Z.leb_le in H. exact H.
    + intros j Hj. rewrite TF by exact Hj. rewrite Bool.andb_true_iff. intros [H _]. exact (M4 j Hj H).
    + intros j Hj. rewrite TA, TF by exact Hj. rewrite !Bool.andb_true_iff. intros [_ H1] [_ H2]. rewrite H1 in H2. discriminate.
    + intros j Hj. rewrite TF by lia. rewrite (M6 j Hj). cbn. destruct (Z.leb_spec j aia); [lia| reflexivity].
  - intros j Hj. cbn zeta. rewrite TA, TF by lia.
    pose proof (is_part _ _ _ IS _ _ _ j Ha Hj) as P. cbn zeta in P.
    assert (NAj : tbit (m_avail (MR st a)) j = false) by (unfold tbit; rewrite AV0; apply Z.bits_0).
    rewrite NAj in P.
    destruct (tbit (m_freed (MR st a)) j); destruct (j <=? aia); cbn [andb negb]; revert P; unfold one5; clear; tauto.
  - left. reflexivity.
  - intros NF sc Hin Hnh. exfalso. destruct (il_active _ _ IL sc a Hin) as (_ & _ & E). subst sc. exact (Hnh (eq_sym HEAD)).
  - intros NF Hsc NI. exfalso. apply NI. exists (LActive (m_sizeclass (MR st a))). exact a_listed.
  - intros NF Hsc Hlt. destruct (g_under _ _ _ _ _ _ GO NF Hsc Hlt) as [_ F0]. unfold A', F'. rewrite F0. split; [apply Z.land_0_l| apply Z.ldiff_0_l].
Qed.
End ACT.
