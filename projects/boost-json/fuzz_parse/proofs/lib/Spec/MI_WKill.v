(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Read MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4 MI_WFree.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_Inv~~~~~~jb4zsum37Corelib4Init5Logico02eq36Stdlib7SortingbPermutationp9bPermutation79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~s3bround_up_pg46Stdlib6ZArith6BinInt1Zhgf2lehc4prods34aptrs34ghdrs36mstatehc4boolhc6optionjb2MRhc3sndjb6cnt_ofs36g_metas3bm_sizeclasshgf3eqb01N35stdpp7numbers1Nhp06eq_dec35stdpp7numbers1Zhqb6eq_dec25stdpp9countablehs6bN_countablehs6bZ_countablehs6eprod_countable25stdpp9decidableig7bprod_eq_dec37Corelib5Lists7ListDefii73mapjb4gcnt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec8MI_WKill~~~~~~ikc5gterms38s_groups25stdpp8fin_mapsiq0bmap_to_list25stdpp4gmapirf4gmapirf9gmap_folds37s_metashc4Somehc4pairs34metahgf3add25stdpp4basejg66deletejg66lookupiq0amap_deleteirfbgmap_lookupirfh2gmap_partial_alterjb8group_oks3aget_stridehgf2ltjb5gbasehc3fsts34UNITs3bslot_start'hgf3mulo03ando02exjb6sstarthc4Noneo03notjb3blkjb5bslotjb6x_pends34cptrs3am_last_idx36Stdlib5Lists4Listjue2In89OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec8MI_WKill4KILL~~~~~~kg75gslotjb5hostss37s_slotss35lheads38m_maplens35usagehgf3sub79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4KInv~~~~~~ko94mledjb4INVLjb6extrass37c_usages34mctxs36mkGhdrs35s_ctxs39set_usages3dset_usage_maps37upd_ctxhgf3ltbjb7x_freshs36m_nexts34optrjb6x_orphhc4truejb4tbito02ors37m_avails37m_freed" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zsum_perm : ltac2:(zQ "50!h9!j4!n9!p4!r5>1l@1$1$0>2l'@1$1$0>0@3$4$0^2^1@3$3$0@1$2^3@1$2^2").
Proof. intros l l'. induction 1; unfold zsum in *; cbn in *; lia. Qed.

Lemma round_up_ge_k : ltac2:(zQ "30!h9!hg1!hi7>1x$0@2$2^1@1$1^1").
Proof. intros x. unfold round_up_pg. pose proof (proj2 (Z.land_nonneg (-x) (PGSZ - 1)) ltac:(right; unfold PGSZ; lia)). lia. Qed.

Definition gterm : ltac2:(zQ "50!h9!hid!hj4!hjb!hk2>2st$4>2sc$0>2bh@2$1$2$3$0") := ltac2:(zQ "d0!hj4!h9!hkb!hl2!hlb!hjb!hid!hm0!hm6!hmf!hn8!hk2!ho6\2st$b\2sc$1\2bh@2$6$0$5M3\1x@1$3$0$1@1$9@3$7$0$5^1\1m$0M2\0$2$1@2$c@1$a@2$4^4^1^3@1$8@2$4^4^1ZZ").
Lemma gcnt_unfold : ltac2:(zQ "h50!h9!hod!hj4!hjb!hq1!hrc!ht7!hu6!hv5!ih8!hid!p4!ije!ik5!n9!ioc!hk2!ip5!ir0!isb!it3>2st$h0>2sc$0@3$b$0@2$d^2^1@1$e@4$c@2$a$2$3$0@2$f^2^1@5$h2$2$3@4$h3$2@4$9$1$4$0$5@6$8$1$4$6$0$5$7$3@4$h4$2@4$9$1$4$0$5@6$8$1$4$6$0$5$7$3@1$h1^2").
Proof. intros st sc. reflexivity. Qed.

Lemma gcnt_delete : ltac2:(zQ "hb1!h9!hod!hq1!hrc!hj4!hjb!ht7!hu6!hv5!ih8!isb!p4!ip5!ik5!hk2!iu0!iua!hl2!iv1!ioc!iv8!ivf!jh2!jhc!ji6!jj4!jk3&@4$a$4@4$9$1$2$0$3@6$8$1$2$6$0$3$7$5>2st$e>3st'$e>1p$4>1h$5>2sc$0>0@3$b@1$h1$5@6$h7$4$5~0@4$h9$4@4$9$1$2$0$3@6$8$1$2$6$0$3$7$5^3@1$c^5@2$h0$5^2>0@3$b~0@1$c^5@5$h6$4~0@4$h8$4$5~0@4$ha$4@4$9$1$2$0$3@6$8$1$2$6$0$3$7$5^4@1$c^6>0@3$b@4$a$4@4$9$1$2$0$3@6$8$1$2$6$0$3$7$h4@1$f^6@1$f^7@3$b$0@2$d^8^4@2$h5@3$h3^8^4@4$h2$4$5^6^5@2$d^7^4").
Proof. intros st st' p h sc.
  intros Hp HG HM. rewrite !gcnt_unfold, HG.
  rewrite <- (zsum_perm _ _ (Permutation_map (gterm st sc) (map_to_list_delete (s_groups st) p h Hp))). cbn. f_equal.
  f_equal. apply map_ext. intros [b hb]. unfold gterm. cbn. unfold MR, get_meta_rec. rewrite HM. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section KILL.
Variables (X : extras) (st st1 : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (g p : aptr) (ai i : Z).
Hypothesis INV : ltac2:(zQ "10!ksd@5$0?1X?2st?1L?2BL?2LS").
Hypothesis Hg : ltac2:(zQ "h20!hjb!hod!h9!hj4!hq1!hrc!iua!ht7!hu6!hv5!ih8!hl2!p4!kue!ip5!jhc!isb!jj4@3$c@1$b$0@6$f$3$0@4$h0$3@4$a$1$4$2$5@6$9$1$4$7$2$5$8$0@4$h1$3@4$a$1$4$2$5@6$9$1$4$7$2$5$8$0?1p@1$e?2st@2$6$0@2$d@2$6$3?1g?2ai").
Hypothesis HF : ltac2:(zQ "50!hj4!iua!hl2!p4!lic@3$3@1$2$0@1$4?1X@2$1$0?1g").
Hypothesis NL : ltac2:(zQ "60!jr6!p4!hlb!hj4!lj6!ljf@3$1$5@1$4@2$2?2st?1g@1$0$3").
Hypothesis HO : ltac2:(zQ "50!hod!jr6!hl2!p4!lk6@3$3@1$2$0@1$4?1X@1$1$0").
Hypothesis Hi : ltac2:(zQ "40!hi7!jq2!hlb!ju1@2$1@2$0Z?1i@2$0?1i@1$3@2$2?2st?1g").
Hypothesis HP : ltac2:(zQ "c0!hod!h9!iua!jo0!hl2!iv1!hid!p4!hlb!jqd!jt1!hj4@3$7@1$4$b@1$a?1X@2$2@2$6$0$1@4$5$0$1@3$3$0$1?1p@2$9@2$8?2st?1g?1i").
Hypothesis ALL : ltac2:(zQ "d0!p4!hlb!hkb!lkf!h9!ll6!hi7!jq2!jrd!lld!lm2!lmc!ju1>1j$4>0@2$7@2$6Z^1@2$6^1@1$c@2$1?2st?1g>0@1$8@3$0$4^2?1i@2$9@3$0$2@2$5@1$a@2$1?2st?1g^3$3@3$0$2@2$5@1$b@2$1?2st?1g^3$3").
Let sc := m_sizeclass (MR st g).
Let cnt : ltac2:(zQ "10!h9$0") := ltac2:(zQ "30!hlb!ju1!ivf@2$2@1$1@2$0?2st?1g+1").
(* [comment removed for export] *)
Hypothesis S1 : ltac2:(zQ "a0!h9!hu6!isb!hrc!p4!jq8!ku7!hk2!lgb!lhb@2$5@4$2$0$3$1$0\1U@4$2$0$3$1$0@3$4$7?3st1@2$9\1c$6@2$8^2^1?2st").
Hypothesis U1 : forall sc', 0 <= sc' < 48 -> usage st1 sc' = if sc' =? sc then usage st sc - cnt else usage st sc'.
Hypothesis U2 : ltac2:(zQ "e0!h9!hu6!hrc!iua!hl2!jq2!p4!ktd!kv7!hi7!jn2!jhc!isb!jj4>3sc0$0>1v$0>0@3$6@1$4$0@6$b$0$0@4$c$0$2$1$0@4$d$0$2$1$0^2@1$7@1$8?3st1@2$3$0^1@2$5@2$9Z^3@2$a^3+j0").
Let st' := del_slots p (get_stride (MR st g)) cnt (del_group p st1).
Let nested := m_maplen (MR st g) =? 0.
Let X' := mkX (x_idle X) (g :: x_zomb X) (if nested then Some p else None) (if nested then None else Some (fst p)) None.

Let IR := proj1 INV. Let IA := proj1 (proj2 INV). Let IM := proj1 (proj2 (proj2 INV)). Let IL := proj1 (proj2 (proj2 (proj2 INV))).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))). Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Lemma g_hosts : hosts st p g. Proof. exists ai. exact Hg. Qed.
Lemma GO : ltac2:(zQ "10!jla@6$0?1X?2st?2LS?1g?1p?2ai"). Proof. exact (ig_ok _ _ _ IG _ _ _ Hg). Qed.
Lemma stride_pos : ltac2:(zQ "30!hlb!jm5!jn2@2$2Z@1$1@2$0?2st?1g").
Proof. pose proof (stride_ge _ _ _ IG _ _ g_hosts) as [H _]. unfold UNIT in H. lia. Qed.
Lemma gbase_p : ltac2:(zQ "40!p4!hlb!jn8!hj4@3$0$3@1$2@2$1?2st?1g?1p"). Proof. exact (hosts_gbase _ _ _ IM _ _ g_hosts). Qed.
Lemma slot_g : ltac2:(zQ "d0!h9!hod!hlb!ivf!jo0!iv1!hm0!p4!jo6!hj4!jm5!jod!jpb>1j$0@3$7$9@2$b@2$2?2st?1g^1@4$5$1$0@3$4$1$0?1p@2$3@2$3@3$6$1$0?1p$8@2$c@1$a@2$2?2st?1g^1").
Proof. intros j. rewrite slot_start'_sstart. unfold sstart. rewrite gbase_p. reflexivity. Qed.

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
Proof. destruct S1 as [U E]. rewrite K_ctx, E. cbn. repeat split; reflexivity. Qed.
Lemma K_usage sc' : usage st' sc' = usage st1 sc'.
Proof. reflexivity. Qed.

Lemma K_get_head h : get_head st' h = get_head st h.
Proof. destruct S1 as [U ->]. destruct h; reflexivity. Qed.
Lemma K_frontier rid r : frontier st' rid r = frontier st rid r.
Proof. unfold frontier. rewrite K_ctx. destruct S1 as [U ->]. reflexivity. Qed.

(* [comment removed for export] *)
Definition gslot : ltac2:(zQ "10!hj4>1s$0P") := ltac2:(zQ "90!jq2!h9!hj4!p4!jq8!hlb!jod!hi7!jn2\1s$2@2$4$1\1j$1@2$0@2$0@2$7Z^1@2$8^1?3cnt@3$3$2^2@2$6@2$5?2st?1g^1").
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
  - left. split; [reflexivity|]. intros (j & Hj & Es). rewrite slot_g in Es. subst s. cbn in d.
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
Lemma K_slots_some s v : s_slots st' !! s = Some v -> s_slots st !! s = Some v /\ ~ gslot s.
Proof. intros H. destruct (K_slots s) as [[E NG]|[E G]]; [rewrite <- E; auto| congruence]. Qed.

(* [comment removed for export] *)
Lemma none_of {A} (o : option A) : (o <> None -> False) -> o = None.
Proof. destruct o; [intros H; exfalso; apply H; discriminate| reflexivity]. Qed.

Lemma g_slot_free : ltac2:(zQ "i11!h9!hod!hjb!hlb!hq1!hrc!jo0!iv1!hid!jq2!p4!jqd!hj4!hl2!hi7!ht7!hu6!hv5!ih8!jr6!iua!jrd!ije!js3!js9!jt1!jta!ju1!ip5!kg1!jhc!isb!jj4&@4$7$1$0@3$6$1$0?1p@2$b@2$3?2st?1g^2>1j$0>0@2$9@2$eZ^1@2$e^1@1$hb@2$3?2st?1g@2$9@1$h5@3$hd@2$8$1$0~0@4$h6$h7$ha$h8?2BL@2$9@3$a@1$d$2@6$he@2$8$1$0$2@4$hf$c@4$h2$1$4$0$5@6$h1$1$4$f$0$5$h0$2@4$i0$c@4$h2$1$4$0$5@6$h1$1$4$f$0$5$h0$2~0@1$hc?2st@1$h3$2>0@3$a@1$d$c@1$h9?1X@2$h4@2$8$1$0~0@3$a$0^3?1i").
Proof. intros j.
  intros Hj. pose proof (is_part _ _ _ IS _ _ _ j Hg Hj) as P. cbn zeta in P. rewrite (slot_start'_eq _ _ _ IM _ _ _ g_hosts) in P. unfold one5 in P.
  destruct P as (_ & nAB & nAC & nAD & nAE & nBC & nBD & nBE & nCD & nCE & nDE).
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
Lemma g_slot_free' : ltac2:(zQ "hc0!h9!hjb!hod!hj4!hq1!hrc!hlb!jq2!jod!hi7!ht7!hu6!hv5!ih8!jr6!hl2!p4!jrd!ije!js3!js9!jta!ju1!ip5!kg1!jhc!isb!jj4>1j$0>0@2$7@2$9Z^1@2$9^1@1$h6@2$6?2st?1g@2$7@1$h1@3$h8$3@2$8@2$6?2st?1g^2@4$h2$h3$h5$h4?2BL@3$h0@1$f$1@6$h9$3$1@4$ha$3@4$d$2$4$0$5@6$c$2$4$a$0$5$b$1@4$hb$3@4$d$2$4$0$5@6$c$2$4$a$0$5$b$1@2$8@2$6?2st?1g^2@1$h7?2st@1$e$1").
Proof. intros j. intros Hj. rewrite (slot_start'_eq _ _ _ IM _ _ _ g_hosts). destruct (g_slot_free j Hj) as (A & B & _). auto. Qed.

Lemma gslot_range : ltac2:(zQ "a0!jq2!h9!hlb!hj4!hi7!p4!jq8!kkc!ju1!jod>1s$3>0@1$7^1@2$6$1\1j$1@2$0@2$0@2$4Z^1@2$4^1@1$8@2$2?2st?1g@3$5$3^3@2$9@2$2?2st?1g^1").
Proof. intros s. intros (j & Hj & E). exists j. unfold cnt in Hj. split; [lia| exact E]. Qed.

(* [comment removed for export] *)
Lemma other_slot_not_g : ltac2:(zQ "b0!hj4!jrd!hlb!hi7!jq2!p4!h9!kl5!kkc!ju1!jod>1m$0>1b$0>1j$6>0@3$7?2st^2^3>0@1$1@3$5$0^4?1g>0@2$4@2$3Z^3@2$3^3@1$9@2$2?2st^5@1$1@1$8@2$a@2$2?2st^6^4").
Proof. intros m b j.
  intros Hm NE Hj G. destruct (gslot_range _ G) as (j' & Hj' & E).
  destruct (slot_key_inj _ _ _ IS _ _ _ _ _ _ Hm g_hosts Hj Hj' E) as [Em _]. exact (NE Em).
Qed.
Lemma entry_not_g : ltac2:(zQ "h40!hj4!h9!hid!hod!hq1!hrc!p4!jrd!ht7!hu6!hv5!ih8!iua!hl2!iv1!kkc!kld!jhc!isb!jj4>1s$0>1m$0>1j$1>0@3$6@1$d@2$2$0$1@6$h1$0@2$2$0$1@4$h2$0@4$b$3$4$1$5@6$a$3$4$8$1$5$9@2$2$0$1@4$h3$0@4$b$3$4$1$5@6$a$3$4$8$1$5$9@2$2$0$1^3@1$h0?2st@2$c@2$2$0$1@4$e$0$1^2^1>0@1$7@3$6$0^3?1g@1$7@1$f^5").
Proof. intros s m j.
  intros Hs NE. destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & Hj & ->). exact (other_slot_not_g m b j Hb NE Hj).
Qed.
(* [comment removed for export] *)
Lemma entry_g_gslot : ltac2:(zQ "h30!h9!hj4!hid!hod!hq1!hrc!ht7!hu6!hv5!ih8!iua!hl2!iv1!p4!kkc!kld!jhc!isb!jj4>1s$1>1j$0>0@3$d@1$b@2$2$1$0@6$h0$1@2$2$1$0@4$h1$1@4$9$3$4$0$5@6$8$3$4$6$0$5$7@2$2$1$0@4$h2$1@4$9$3$4$0$5@6$8$3$4$6$0$5$7@2$2$1$0^2@1$f?2st@2$a@2$2$1$0@4$c$1$0?1g^1@1$e^3").
Proof. intros s j.
  intros Hs. destruct (is_valid _ _ _ IS _ _ _ Hs) as (_ & Hj & ->). exists j. unfold cnt. split; [lia| reflexivity].
Qed.

Lemma hosts_K b m : hosts st' b m <-> hosts st b m /\ b <> p.
Proof.
  unfold hosts. rewrite K_groups. split.
  - intros [a H]. apply lookup_delete_Some in H as [NE H]. split; [exists a; exact H| congruence].
  - intros [[a H] NE]. exists a. rewrite lookup_delete_ne by congruence. exact H.
Qed.
Lemma live_K m : live_group st m -> m <> g -> live_group st' m.
Proof.
  intros [b Hb] NE. exists b. apply hosts_K. split; [exact Hb|]. intros ->. exact (NE (hosts_fun _ _ _ _ Hb g_hosts)).
Qed.
Lemma g_unlisted_K : ltac2:(zQ "40!jrd!hj4!km7!kg1>1h$2@1$0@3$3$1?1g@1?2LS^1").
Proof. intros h. exact (lists_notin st LS (old_lists _ _ _ _ _ INV) g NL h). Qed.

(* [comment removed for export] *)
Lemma p_not_gslot : ltac2:(zQ "20!jrd!kkc@1$0@1$1?1p").
Proof.
  intros (j & Hj & E). rewrite slot_g in E. pose proof stride_pos.
  assert (snd p = snd p + UNIT + get_stride (MR st g) * j) by (rewrite E at 1; reflexivity). unfold UNIT in *. nia.
Qed.
Lemma slots_pos : ltac2:(zQ "h40!h9!hj4!hid!hod!hq1!hrc!ht7!hu6!hv5!ih8!iua!hl2!iv1!hm0!p4!kld!jn2!jhc!isb!jj4>1s@2$2$3$0>1m$1>1j$0>0@3$e@1$b@2$2$1$0@6$h1@2$2$3$0@2$2$1$0@4$h2$1@4$9$3$4$0$5@6$8$3$4$6$0$5$7@2$2$1$0@4$h3$1@4$9$3$4$0$5@6$8$3$4$6$0$5$7@2$2$1$0^3@1$f?2st@2$a@2$2$1$0@4$c$1$0^2^1@2$h0Z@3$d$3$0^4").
Proof. intros s m j.
  intros Hs. destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & Hj & ->). rewrite (slot_start'_eq _ _ _ IM _ _ _ Hb). cbn.
  pose proof (sstart0 _ _ _ IM _ _ Hb). pose proof (sstart_mono _ _ _ IG _ _ 0 j Hb ltac:(lia)).
  destruct (hosts_ok _ _ _ IG _ _ Hb) as (a & _ & GOm). pose proof (g_align _ _ _ _ _ _ GOm) as [A _]. unfold UNIT in *. lia.
Qed.

(* [comment removed for export] *)
Lemma top_region_empty : ltac2:(zQ "h60!hod!h9!hjb!p4!hq1!hrc!hid!jo0!hj4!ht7!hu6!hv5!ih8!iua!hl2!jrd!hlb!kmf!ip5!jhc!isb!jj4>1b@2$6$0$1>1h$2>0@1$f@3$3$1@1$h1@2$h0?2st?1gZ>0@3$3@1$e$2@6$h3@2$6$0$1$2@4$h4$8@4$c$0$4$1$5@6$b$0$4$9$1$5$a$2@4$h5$8@4$c$0$4$1$5@6$b$0$4$9$1$5$a$2^3@1$h2?2st@2$d$2^2>0@3$3$0@3$7$0$1^4@3$7$0$1?1p@3$3@2$6$0$1^5?1p").
Proof. intros b h.
  intros Hml Hb Hf. destruct (im_hdr _ _ _ IM _ _ Hb) as (m & Em & Hmem & _).
  assert (Hm : hosts st b m) by (destruct h as [hm ha]; cbn in Em; subst hm; exists ha; exact Hb).
  destruct (aptr_eq_dec m g) as [->|NE]; [exact (hosts_inj _ _ _ IM _ _ _ Hm g_hosts)|]. exfalso.
  destruct (Z.eq_dec (m_maplen (MR st m)) 0) as [Hml'|Hml'].
  - destruct (@top_chain _ _ _ _ IM IG IS m b Hm Hml') as (t & j & c & bt & Ha & Ht & Htop & Hft).
    assert (t = g) by (apply (@top_unique _ _ _ IG t g bt p Ht g_hosts Htop Hml); congruence). subst t.
    destruct (@anc_hostslot _ _ _ _ IM IG IS m g j c Ha) as (bp & Hp & Hsl).
    pose proof (hosts_inj _ _ _ IM _ _ _ Hp g_hosts). subst bp.
    destruct (@anc_facts _ _ _ _ IM IG IS m g j c Ha) as (bm' & bp' & _ & _ & _ & Hj & _).
    destruct (g_slot_free j Hj) as (_ & N & _). exact (Hsl N).
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
      inversion Ho. subst rid. destruct (g_top _ _ _ _ _ _ GOg NE) as (H0 & r & Hr & Hk & _). exists r. split; [exact Hr|]. split; [exact Hk|].
      intros b Hb. rewrite K_groups. destruct (aptr_eq_dec b p) as [->|NEb]; [apply lookup_delete_eq|]. rewrite lookup_delete_ne by congruence.
      destruct (s_groups st !! b) eqn:Eb; [| reflexivity]. exfalso. exact (NEb (top_region_empty b _ NE Eb Hb)).
    + intros rid r q H1 H2 H3 H4 H5. rewrite K_areas. rewrite K_frontier in H4. apply (ir_pages rid r q H1 H2 H3 H4).
      rewrite HF. intros E. injection E as Eg. exact (meta_not_page X st L BL LS g rid q INV (g_present _ _ _ _ _ _ GO) H3 Eg).
    + assert (ES : c_meta_alloc_shift (s_ctx st') = c_meta_alloc_shift (s_ctx st)) by (destruct S1 as [U ->]; reflexivity). rewrite ES. exact ir_mshift.
  - (* [comment removed for export] *) destruct K_cf as (cf1 & cf2 & cf3 & cf4 & cf5 & cf6 & cf7 & cf8 & cf9 & cf10 & cf11 & cf12 & cf13 & cf14 & cf15 & cf16 & cf17).
    destruct IA; constructor; rewrite ?K_regions, ?K_areas, ?K_secret, ?K_metas, ?cf1, ?cf2, ?cf3, ?cf4, ?cf5, ?cf6, ?cf7, ?cf8, ?cf9, ?cf10, ?cf11, ?cf12, ?cf13, ?cf14, ?cf15, ?cf16, ?cf17; try assumption.
    + intros a ar Ha. destruct (ia_areas a ar Ha) as ((r & ? & ? & ? & ? & ?) & ? & ? & ?). split; [| auto]. exists r. rewrite K_frontier. auto.
    + intros sc' Hsc'. rewrite K_usage, (U1 sc' Hsc').
      pose proof (gcnt_K sc') as GK. rewrite <- (ia_usage sc' Hsc') in GK. rewrite Z.eqb_sym in GK.
      destruct (Z.eqb_spec sc' sc) as [E|NE]; [rewrite <- E; lia| lia].
  - (* [comment removed for export] *) destruct IM as [M1 M2 M3 M4 M5 MAL] eqn:EIM; constructor; rewrite ?K_MR.
    + intros m Hm. rewrite !K_MR. apply M1. rewrite <- (K_MR m). exact Hm.
    + intros m b Hm. rewrite K_MR in Hm. destruct (aptr_eq_dec m g) as [->|NE]; [right; left; reflexivity|].
      destruct (M2 m b Hm) as [H|H]; [left| right; right; exact H]. apply hosts_K. split; [exact H|]. exact (NGm b m H NE).
    + intros b h Hb. rewrite K_groups in Hb. apply lookup_delete_Some in Hb as [NE Hb]. destruct (M3 b h Hb) as (m & ? & ? & ?). exists m. rewrite !K_MR. auto.
    + intros m Hm. rewrite K_metas. exact (M4 m Hm).
    + intros z Hz. rewrite !K_MR, K_groups. cbn in Hz. destruct Hz as [<-|Hz].
      * split; [intros [h Hh]; exact (g_unlisted_K h Hh)|]. split; [exact NL|].
        split; [exact (proj2 (il_link _ _ IL g) NL)|].
        exists p. split; [exact (hosts_mem _ _ _ IM _ _ g_hosts)| apply lookup_delete_eq].
      * destruct (M5 z Hz) as (A1 & A2 & A3 & b & A4 & A5). split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
        exists b. split; [exact A4|]. destruct (aptr_eq_dec b p) as [->|NE]; [apply lookup_delete_eq| rewrite lookup_delete_ne by congruence; exact A5].
    + intros m Hm. rewrite K_metas in Hm. destruct (aptr_eq_dec m g) as [->|NE]; [right; right; right; left; reflexivity|].
      destruct (MAL m Hm) as [A|[A|[A|A]]]; [left; exact (live_K m A NE)| right; left; exact A| right; right; left; exact A| right; right; right; right; exact A].
  - (* [comment removed for export] *) destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9] eqn:EIL; constructor; try assumption.
    + intros h. rewrite K_get_head. apply L1.
    + intros h. apply (dll_ext_metas st st' K_metas). apply L2.
    + intros m. rewrite !K_MR. apply L5.
    + intros m Hm. rewrite !K_MR. apply L6. exact Hm.
    + intros sc0 m Hm. destruct (L7 sc0 m Hm) as (A1 & A2 & A3). rewrite K_MR. split; [exact A1|]. split; [| exact A3].
      apply live_K; [exact A2|]. intros ->. exact (g_unlisted_K _ Hm).
  - (* [comment removed for export] *) destruct IG as [G1 G2 G3 G4 G5 GOE] eqn:EIG. constructor.
    + intros m b aim Hb. rewrite K_groups in Hb. apply lookup_delete_Some in Hb as [NEb Hb]. pose proof (G1 m b aim Hb) as GOm.
      assert (NEm : m <> g) by (intros ->; apply NEb; symmetry; exact (hosts_inj _ _ _ IM _ _ _ (ex_intro _ aim Hb) g_hosts)).
      assert (NF : x_fresh X <> Some m) by (rewrite HF; congruence).
      destruct GOm; constructor; rewrite ?K_MR, ?K_metas, ?K_regions; try assumption.
      * intros _. exact (g_partial NF).
      * intros _. exact (g_unlisted NF).
      * intros _. exact (g_rest NF).
      * intros _. exact (g_under NF).
      * intros Hml. destruct (g_nest Hml) as (pm & i' & Hs & REST). exists pm, i'. rewrite !K_MR. split; [| exact REST].
        rewrite K_slots_other; [exact Hs|]. apply (entry_not_g _ _ _ Hs). intros ->.
        destruct (is_valid _ _ _ IS _ _ _ Hs) as (_ & Hi' & Eb).
        destruct (g_slot_free' i' Hi') as [_ N]. rewrite <- Eb, Hb in N. discriminate.
    + intros b aim Hb. rewrite K_groups in Hb. apply lookup_delete_Some in Hb as [_ Hb]. exact (G2 b aim Hb).
    + intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite K_groups in H1, H2. apply lookup_delete_Some in H1 as [_ H1]. apply lookup_delete_Some in H2 as [_ H2].
      rewrite !K_MR. eapply G3; eassumption.
    + intros rid r Hr Hk Ho. rewrite K_regions in Hr. destruct (G4 rid r Hr Hk ltac:(rewrite HO; discriminate)) as (m & Hm & Hml). exists m. rewrite K_MR. split; [| exact Hml].
      apply hosts_K. split; [exact Hm|]. intros E.
      assert (Em : m = g) by (apply (hosts_fun st p); [rewrite <- E; exact Hm| exact g_hosts]). subst m.
      unfold X' in Ho. cbn in Ho. unfold nested in Ho. rewrite (proj2 (Z.eqb_neq _ _) Hml) in Ho. apply Ho. rewrite <- E. reflexivity.
    + intros b h Hb. rewrite K_groups in Hb. apply lookup_delete_Some in Hb as [_ Hb]. rewrite K_regions. exact (G5 b h Hb).
    + intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite K_groups in H1, H2. apply lookup_delete_Some in H1 as [_ H1]. apply lookup_delete_Some in H2 as [_ H2].
      rewrite !K_MR. eapply GOE; eassumption.
  - (* [comment removed for export] *) destruct IS as [S1' S2 S3 S4 S5 S6 SBG] eqn:EIS. constructor.
    + intros s m j Hs. destruct (K_slots_some _ _ Hs) as [Hs0 NG]. destruct (S1' s m j Hs0) as (Hl & Hj & Es). rewrite !K_MR.
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
      destruct P as (P0 & nAB & nAC & nAD & nAE & nBC & nBD & nBE & nCD & nCE & nDE).
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
      destruct (g_nest _ _ _ _ _ _ GOg Hml) as (pm & ip & Hs0 & _). rewrite K_slots_other; [rewrite Hs0; discriminate| exact p_not_gslot].
    + exact S5.
    + intros k Hk. destruct (S6 k Hk) as (m & j & Hs & REST). exists m, j. rewrite K_MR. split; [| exact REST].
      rewrite K_slots_other; [exact Hs|]. intros G. destruct (gslot_range _ G) as (j' & Hj' & E).
      destruct (g_slot_free' j' Hj') as [NB _]. apply NB. rewrite <- E. apply in_map_iff. exists k. auto.
    + intros k m j Hk Hs Hsc. destruct (K_slots_some _ _ Hs) as [Hs0 _]. rewrite K_MR in Hsc. rewrite K_regions. exact (SBG k m j Hk Hs0 Hsc).
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
      destruct (D5 b m pm j Hb Hml Hs0) as ((v3 & K3 & E3 & R3) & K2 & K1 & Q). cbn zeta.
      split; [exists v3; auto|]. auto.
    + intros k m j Hk Hs. destruct (K_slots_some _ _ Hs) as [Hs0 _]. rewrite !K_MR. pose proof (D6 k m j Hk Hs0) as B. cbn zeta in B |- *.
      destruct B as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
      split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [exact A5|]. split.
      * intros Hres. destruct (A6 Hres) as (B1 & B2 & B3 & B4 & B5 & B6). repeat split; auto.
      * split; [intros Hres; apply KN; apply A7; exact Hres|]. intros a Ha. apply UN. apply A8. exact Ha.
Qed.

Lemma kill_top : m_maplen (MR st g) <> 0 ->
  exists r, snd p = 0 /\ s_regions st' !! (fst p) = Some r /\ r_kind r = RKGroup
    /\ m_maplen (MR st g) * 4096 = round_up_pg (r_len r) /\ 0 < m_maplen (MR st g) * 4096.
Proof.
  intros Hml. destruct (g_top _ _ _ _ _ _ GO Hml) as (H0 & r & Hr & Hk & E & _). exists r. rewrite K_regions.
  pose proof (ir_shape _ _ _ IR _ _ Hr) as (_ & _ & L0 & _). pose proof (round_up_ge_k (r_len r)). repeat split; auto. lia.
Qed.

Lemma kill_nested : m_maplen (MR st g) = 0 ->
  exists pm ip bpm, s_slots st' !! p = Some (pm, ip) /\ hosts st' bpm pm /\ fst bpm = fst p
    /\ 0 <= ip <= m_last_idx (MR st pm) /\ p = (fst bpm, sstart (MR st pm) ip)
    /\ m_sizeclass (MR st g) < m_sizeclass (MR st pm) < 48
    /\ get_stride (MR st pm) = UNIT * size_class (m_sizeclass (MR st pm))
    /\ gend (MR st g) <= sstart (MR st pm) ip + get_stride (MR st pm).
Proof.
  intros Hml. destruct (g_nest _ _ _ _ _ _ GO Hml) as (pm & ip & Hs & Hf & He & Hsc & Hstr).
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bpm Hpm] & Hip & Ep).
  exists pm, ip, bpm.
  assert (NE : pm <> g) by (intros ->; lia).
  split; [rewrite K_slots_other; [exact Hs| exact p_not_gslot]|].
  split; [apply hosts_K; split; [exact Hpm|]; intros ->; exact (NE (hosts_fun _ _ _ _ Hpm g_hosts))|].
  rewrite (slot_start'_eq _ _ _ IM _ _ _ Hpm) in Ep.
  split; [rewrite Ep; reflexivity|]. repeat split; auto; lia.
Qed.

(* [comment removed for export] *)
Lemma dec_hdr_eq {T} (k : aptr -> Z -> M T) bail :
  m_maplen (MR st g) = 0 ->
  exists pm ip bpm, dec_hdr st' p k bail = k pm ip
    /\ s_slots st' !! p = Some (pm, ip) /\ hosts st' bpm pm /\ fst bpm = fst p
    /\ 0 <= ip <= m_last_idx (MR st pm) /\ p = (fst bpm, sstart (MR st pm) ip)
    /\ m_sizeclass (MR st g) < m_sizeclass (MR st pm) < 48.
Proof.
  intros Hml. destruct (kill_nested Hml) as (pm & ip & bpm & Hs' & Hpm' & Hf & Hip & Ep & Hsc & Hstr & Hend).
  exists pm, ip, bpm. split; [| repeat split; auto; lia].
  pose proof Hpm' as Hpm. apply hosts_K in Hpm as [Hpm NEb].
  destruct (hosts_ok _ _ _ IG _ _ Hpm) as (aipm & Hgpm & GOpm).
  assert (Hs : s_slots st !! p = Some (pm, ip)) by (destruct (K_slots_some _ _ Hs') as [H _]; exact H).
  (* [comment removed for export] *)
  pose proof (ish_nest _ _ ISH p g pm ip g_hosts Hml Hs) as NS. cbn zeta in NS. rewrite (hosts_gbase _ _ _ IM _ _ Hpm) in NS.
  set (q := (snd p - snd bpm - UNIT) / UNIT) in NS.
  destruct NS as ((v3 & K3 & E3 & R3) & K2 & K1 & Q).
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
  destruct (ia_metas _ IA _ _ Em) as (a & ar & ka & Ha & Hka & Emk).
  destruct (ia_areas _ IA _ _ Ha) as ((r & Hr & Hmk & Hal & Hpg & Hfr) & Hck & Hns & _).
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
      destruct (g_top _ _ _ _ _ _ GOpm NM) as (B0 & _ & _ & _ & _ & GE). apply Z.leb_le.
      unfold gend, cnt_of, sstart in GE. rewrite (hosts_gbase _ _ _ IM _ _ Hpm), B0 in GE.
      pose proof (stride_ge _ _ _ IG _ _ Hpm) as [S16 _]. unfold UNIT in S16, Hq, GE.
      clear KN K2 K1 K3 K4 P D Ebase SB.
      eapply (guard17_arith (get_stride (MR st pm)) ip 0 0 q (m_last_idx (MR st pm)) (m_maplen (MR st pm))); try lia. }
  reflexivity.
Qed.
End KILL.

(* [comment removed for export] *)
Lemma fg_st1 : ltac2:(zQ "ic0!h9!hrc!hj4!hu6!hjb!hkb!jq2!p4!hod!hk2!kna!isb!hq1!iua!j4!hl2!hlb!hi7!jn2!ko2!jhc!ht7!hv5!ih8!jj4!jq8!ks5!ksd!js3!kt4!ktd!km7!ju1!hn8!ku7!kue!kv7!ip5!kvf!lgb!lhb!ivf!ho6!li5>1X$hd>2st$9>1L$ha>2BL@1$e$hc>2LS>0$hf@1$e$2>1g$2>1p$2>2ai$0>3INV@5$hb^8^7^6^5^4>2Hg@3$7@1$f$4@6$h4$2$4@4$b$2@4$h7$8$c$0$1@6$h6$8$c$h5$0$1$3$4@4$h8$2@4$h7$8$c$0$1@6$h6$8$c$h5$0$1$3$4^3@1$i5^8@2$d$4@2$i3@2$d$2^4^2=2sc$0@1$i1@2$h0^9^5=3cnt$0@2$i9@1$i0@2$h0^a^6+1=3st1$9M5\0$5$9@2$ib^2+j0@3$i6^2@2$h3@2$a^b^2^1^b^b@2$6@2$h9@4$b$0$1$3$0\1U@4$b$0$1$3$0@3$7$9^2@2$i8\1c$i2@2$i7^2^1^d@2$6>3sc'$0>0@2$6@2$h1Z^1@2$h2^1+j0@3$7$0@2$a^3^2M5\0$5$0@2$ia^2^5@2$h3@2$a^e^5^4@2$a^e^2>3sc0$0>1v$0>0@3$7@1$f$0@6$h4$0$0@4$b$0$1$3$0@4$h8$0$1$3$0^2@1$he@1$i4^3@2$d$0^1@2$6@2$h1Z^3@2$h2^3+j0").
Proof. intros X st L BL LS g p ai INV Hg.
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
(* [comment removed for export] *)
