(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Bool.
From Stdlib Require Lia.
From stdpp Require gmap.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM09.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Spec Require Malloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module MallocCtrl.

From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Bool. From Stdlib Require Import Lia.
From stdpp Require Import gmap.
Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Malloc.
Unset Lia Cache.

Local Open Scope Z_scope.
Local Open Scope stree_scope.

Section ORACLE.
Context {O : Type}.
Variable pans : O -> aptr -> Z -> Z -> Z.
Variable pupd : O -> ev -> Z -> O.

Definition psel (o : O) (e : ev) : option Z :=
  match e with EPeek p c h => Some (pans o p c h) | _ => None end.
Definition prun {R} (o : O) (t : M R) : M (O * R) := eruns psel pupd o t.

Definition KREL {X R1 R2} (RR : O * R1 -> R2 -> Prop)
  (k1 : mstate -> X -> M R1) (k2 : mstate -> X -> M R2) : Prop :=
  forall o st cst x, cst = strip st -> strel RR (prun o (k1 st x)) (k2 cst x).
Definition KREL0 {R1 R2} (RR : O * R1 -> R2 -> Prop)
  (k1 : mstate -> M R1) (k2 : mstate -> M R2) : Prop :=
  forall o st cst, cst = strip st -> strel RR (prun o (k1 st)) (k2 cst).
Definition BREL {R1 R2} (RR : O * R1 -> R2 -> Prop) (b1 : M R1) (b2 : M R2) : Prop :=
  forall o, strel RR (prun o b1) b2.
End ORACLE.
Arguments psel {O} pans o e.
Arguments prun {O} pans pupd {R} o t.
Arguments KREL {O} pans pupd {X R1 R2} RR k1 k2.
Arguments KREL0 {O} pans pupd {R1 R2} RR k1 k2.
Arguments BREL {O} pans pupd {R1 R2} RR b1 b2.


Lemma strip_strip st : strip (strip st) = strip st.
Proof. reflexivity. Qed.

Lemma strip_wr8 p v st : strip (wr8 p v st) = strip st.
Proof. reflexivity. Qed.
Lemma strip_wr16 p v st : strip (wr16 p v st) = strip st.
Proof. reflexivity. Qed.
Lemma strip_wr32 p v st : strip (wr32 p v st) = strip st.
Proof. reflexivity. Qed.
Lemma strip_havoc p n st : strip (havoc p n st) = strip st.
Proof. unfold havoc. destruct (n <=? 0); reflexivity. Qed.
Lemma strip_set_tick t st : strip (set_tick t st) = strip st.
Proof. reflexivity. Qed.
Lemma strip_zero_hdrs p size i cnt st : strip (zero_hdrs p size i cnt st) = strip st.
Proof. revert i st; induction cnt; intros; simpl; auto. rewrite IHcnt. reflexivity. Qed.
Lemma strip_set_size p e n b st : strip (set_size p e n b st) = strip st.
Proof. unfold set_size. destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma strip_enframe_at st g idx n off :
  strip (fst (enframe_at st g idx n off)) = strip st.
Proof.
  unfold enframe_at. destruct (negb (off =? 0)); cbn -[set_size wr8 wr16 strip]; rewrite strip_set_size; reflexivity.
Qed.
Lemma strip_hdr_havoc b st : strip (hdr_havoc b st) = strip st.
Proof. reflexivity. Qed.
Lemma strip_nest_layout st g idx j size cnt : strip (nest_layout st g idx j size cnt) = strip st.
Proof.
  unfold nest_layout. destruct (enframe_at st g idx _ 0) as [st1 p] eqn:E.
  rewrite strip_zero_hdrs, strip_wr8. pose proof (strip_enframe_at st g idx (UNIT * size_class j - IB) 0) as H.
  rewrite E in H. exact H.
Qed.


Lemma ctx_strip st : ctx (strip st) = ctx st. Proof. reflexivity. Qed.
Lemma s_ctx_strip st : s_ctx (strip st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_regions_strip st : s_regions (strip st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_metas_strip st : s_metas (strip st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_strip st : s_areas (strip st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_strip st : s_groups (strip st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_slots_strip st : s_slots (strip st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_next_rid_strip st : s_next_rid (strip st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_secret_strip st : s_secret (strip st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_strip st : s_reserved (strip st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_atop_strip st : s_atop (strip st) = s_atop st. Proof. reflexivity. Qed.
Lemma active_strip st sc : active (strip st) sc = active st sc. Proof. reflexivity. Qed.
Lemma usage_strip st sc : usage (strip st) sc = usage st sc. Proof. reflexivity. Qed.
Lemma unmap_seq_strip st i : unmap_seq (strip st) i = unmap_seq st i. Proof. reflexivity. Qed.
Lemma bounces_strip st i : bounces (strip st) i = bounces st i. Proof. reflexivity. Qed.
Lemma get_meta_rec_strip st m : get_meta_rec (strip st) m = get_meta_rec st m. Proof. reflexivity. Qed.
Lemma get_group_strip st g : get_group (strip st) g = get_group st g. Proof. reflexivity. Qed.
Lemma group_active_idx_strip st g : group_active_idx (strip st) g = group_active_idx st g. Proof. reflexivity. Qed.
Lemma get_region_strip st r : get_region (strip st) r = get_region st r. Proof. reflexivity. Qed.
Lemma conc_strip st p : conc (strip st) p = conc st p. Proof. reflexivity. Qed.
Lemma live_ranges_strip st : live_ranges (strip st) = live_ranges st. Proof. reflexivity. Qed.
Lemma brk_pages_ok_strip st lo len : brk_pages_ok (strip st) lo len = brk_pages_ok st lo len. Proof. reflexivity. Qed.
Lemma get_head_strip st h : get_head (strip st) h = get_head st h. Proof. destruct h; reflexivity. Qed.
Lemma is_bouncing_strip sc st : is_bouncing sc (strip st) = is_bouncing sc st. Proof. reflexivity. Qed.
Lemma okay_to_free_strip st g : okay_to_free (strip st) g = okay_to_free st g. Proof. reflexivity. Qed.
Lemma slot_of_strip st g i : slot_of (strip st) g i = slot_of st g i. Proof. reflexivity. Qed.

Lemma strip_upd_ctx f st : upd_ctx f (strip st) = strip (upd_ctx f st). Proof. reflexivity. Qed.
Lemma strip_upd_meta m f st : upd_meta m f (strip st) = strip (upd_meta m f st). Proof. reflexivity. Qed.
Lemma strip_put_meta m r st : put_meta m r (strip st) = strip (put_meta m r st). Proof. reflexivity. Qed.
Lemma strip_set_active sc v st : set_active sc v (strip st) = strip (set_active sc v st). Proof. reflexivity. Qed.
Lemma strip_set_head h v st : set_head h v (strip st) = strip (set_head h v st). Proof. destruct h; reflexivity. Qed.
Lemma strip_set_usage sc v st : set_usage sc v (strip st) = strip (set_usage sc v st). Proof. reflexivity. Qed.
Lemma strip_set_bounce i v st : set_bounce i v (strip st) = strip (set_bounce i v st). Proof. reflexivity. Qed.
Lemma strip_set_areas a st : set_areas a (strip st) = strip (set_areas a st). Proof. reflexivity. Qed.
Lemma strip_put_group g m ai st : put_group g m ai (strip st) = strip (put_group g m ai st). Proof. reflexivity. Qed.
Lemma strip_set_group_active_idx g ai st : set_group_active_idx g ai (strip st) = strip (set_group_active_idx g ai st).
Proof. unfold set_group_active_idx. rewrite get_group_strip. destruct (get_group st g); reflexivity. Qed.
Lemma strip_del_group g st : del_group g (strip st) = strip (del_group g st). Proof. reflexivity. Qed.
Lemma strip_add_slots m p s c st : add_slots m p s c (strip st) = strip (add_slots m p s c st). Proof. reflexivity. Qed.
Lemma strip_del_slots p s c st : del_slots p s c (strip st) = strip (del_slots p s c st). Proof. reflexivity. Qed.
Lemma strip_drop_region rid st : drop_region rid (strip st) = strip (drop_region rid st).
Proof. unfold drop_region, strip; cbn. rewrite delete_empty. reflexivity. Qed.
Lemma strip_new_region k b l st :
  new_region k b l (strip st) = (strip (fst (new_region k b l st)), snd (new_region k b l st)).
Proof. reflexivity. Qed.
Lemma strip_upd_region rid f st : upd_region rid f (strip st) = strip (upd_region rid f st).
Proof. unfold upd_region. rewrite get_region_strip. destruct (get_region st rid); reflexivity. Qed.
Lemma strip_step_seq st : step_seq (strip st) = strip (step_seq st).
Proof. unfold step_seq. rewrite ctx_strip. destruct (c_seq (ctx st) =? 255); reflexivity. Qed.
Lemma strip_record_seq sc st : record_seq sc (strip st) = strip (record_seq sc st).
Proof. unfold record_seq. destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma strip_account_bounce sc st : account_bounce sc (strip st) = strip (account_bounce sc st).
Proof. unfold account_bounce. rewrite !unmap_seq_strip, !bounces_strip, !ctx_strip.
  destruct (sc_in_seq_range sc); [|reflexivity]. destruct (negb _ && _); [|reflexivity]. destruct (_ <? 100); reflexivity. Qed.
Lemma strip_decay_bounces sc st : decay_bounces sc (strip st) = strip (decay_bounces sc st).
Proof. unfold decay_bounces. rewrite !bounces_strip. destruct (_ && _); reflexivity. Qed.
Lemma strip_dequeue h m st : dequeue h m (strip st) = strip (dequeue h m st).
Proof.
  unfold dequeue. rewrite !get_meta_rec_strip.
  destruct (negb _); [|rewrite strip_set_head; reflexivity].
  destruct (m_prev _); destruct (m_next _); rewrite ?strip_upd_meta, ?get_head_strip;
  destruct (optr_eqb _ _); rewrite ?strip_set_head, ?strip_upd_meta; reflexivity.
Qed.

Hint Rewrite ctx_strip s_ctx_strip s_regions_strip s_metas_strip s_areas_strip s_groups_strip s_slots_strip
  s_next_rid_strip s_secret_strip s_reserved_strip s_atop_strip active_strip usage_strip unmap_seq_strip bounces_strip
  get_meta_rec_strip get_group_strip group_active_idx_strip get_region_strip conc_strip live_ranges_strip brk_pages_ok_strip
  get_head_strip is_bouncing_strip okay_to_free_strip slot_of_strip
  strip_upd_ctx strip_upd_meta strip_put_meta strip_set_active strip_set_head strip_set_usage strip_set_bounce
  strip_set_areas strip_put_group strip_set_group_active_idx strip_del_group strip_add_slots strip_del_slots
  strip_drop_region strip_new_region strip_upd_region strip_step_seq strip_record_seq strip_account_bounce
  strip_decay_bounces strip_dequeue
  strip_strip strip_wr8 strip_wr16 strip_wr32 strip_havoc strip_set_tick strip_zero_hdrs strip_set_size strip_nest_layout strip_hdr_havoc
  : strip_rw.
Hint Rewrite <- strip_upd_ctx strip_upd_meta strip_put_meta strip_set_active strip_set_head strip_set_usage strip_set_bounce
  strip_set_areas strip_put_group strip_set_group_active_idx strip_del_group strip_add_slots strip_del_slots
  strip_drop_region strip_upd_region strip_step_seq strip_record_seq strip_account_bounce
  strip_decay_bounces strip_dequeue : strip_in.
Hint Rewrite strip_strip strip_wr8 strip_wr16 strip_wr32 strip_havoc strip_set_tick strip_zero_hdrs strip_set_size
  strip_nest_layout strip_enframe_at strip_hdr_havoc : strip_in.


Ltac csimp := cbn -[strip
   ctx active usage unmap_seq bounces get_meta_rec get_group group_active_idx get_region conc oconc
                   live_ranges brk_pages_ok get_head is_bouncing okay_to_free slot_of get_shadow
                   s_ctx s_regions s_shadow s_metas s_areas s_groups s_slots s_next_rid s_tick s_secret s_reserved s_atop
   upd_ctx set_active set_head set_usage set_bounce put_meta upd_meta put_group set_group_active_idx
                   set_areas set_metas set_groups set_slots set_regions set_shadow set_next_rid set_tick
                   new_region drop_region del_group add_slots del_slots upd_region upd_shadow wr8 wr16 wr32 havoc hdr_havoc
                   step_seq record_seq account_bounce decay_bounces dequeue nest_layout enframe_at set_size zero_hdrs
   am_take am_carve am_finish am_after_brk alloc_meta ta_fin try_avail ag_tail alloc_group alloc_slot
                   malloc_small_ctrl malloc_core
                   nontrivial_free free_group free_tail free_hdr queue free_meta activate_group
                   enframe_read_off enframe_full get_meta get_nominal_size rd8 rd16 rd32
                   size_to_class size_class small_cnt_pick small_cnt halve_even halve_big med_cnt span_loop
                   mask_upto lowbit ctz32 bit u32 round_up_pg fold_off get_stride area_of
                   mmap_answer_ok brk0_answer_ok brk_answer_ok mmap_fixed_answer_ok munmap_answer_ok
                   mprotect_answer_ok peek_answer_ok is_err size_overflows
                   Z.add Z.sub Z.mul Z.div Z.modulo Z.eqb Z.leb Z.ltb Z.land Z.lor Z.ldiff Z.lxor Z.shiftl Z.shiftr
                   Z.pow Z.even Z.testbit Z.to_nat Z.iter N.succ N.eqb lookup insert delete empty map_to_list fmap].

Global Set Keyed Unification.
Ltac srw := autorewrite with strip_rw.

Ltac strip_in1 :=
  first
  [ rewrite strip_nest_layout | rewrite strip_hdr_havoc | rewrite strip_enframe_at | rewrite strip_zero_hdrs | rewrite strip_set_size
  | rewrite strip_havoc | rewrite strip_wr32 | rewrite strip_wr16 | rewrite strip_wr8 | rewrite strip_set_tick
  | rewrite strip_strip
  | rewrite <- strip_dequeue | rewrite <- strip_step_seq | rewrite <- strip_record_seq
  | rewrite <- strip_account_bounce | rewrite <- strip_decay_bounces | rewrite <- strip_drop_region
  | rewrite <- strip_del_slots | rewrite <- strip_add_slots | rewrite <- strip_del_group
  | rewrite <- strip_set_group_active_idx | rewrite <- strip_put_group | rewrite <- strip_upd_region
  | rewrite <- strip_set_head | rewrite <- strip_set_active | rewrite <- strip_set_usage | rewrite <- strip_set_bounce
  | rewrite <- strip_upd_meta | rewrite <- strip_put_meta | rewrite <- strip_set_areas | rewrite <- strip_upd_ctx ].
Ltac solve_eq := repeat strip_in1; reflexivity.
Ltac use_hyp :=
  match goal with
  | H : _ |- strel _ _ _ =>
      with_strategy opaque [am_take am_carve am_finish am_after_brk alloc_meta ta_fin try_avail ag_tail
                            alloc_group alloc_slot malloc_small_ctrl malloc_core
                            nontrivial_free free_group free_tail free_hdr queue free_meta activate_group
                            enframe_read_off enframe_full]
        (eapply H); (try assumption); (try solve_eq)
  end.
Ltac not_numeric T :=
  lazymatch T with Z => fail | bool => fail | N => fail | nat => fail | (Z * Z)%type => fail | _ => idtac end.
Ltac scrut x :=
  match x with
  | context [if ?c then ?a else _] => let T := type of a in not_numeric T; scrut c
  | context [match ?y with _ => _ end] => let T := type of y in (lazymatch T with bool => fail | _ => idtac end); scrut y
  | _ => destruct x eqn:?
  end.
Ltac sync1 :=
  first
  [ lazymatch goal with
    | |- strel _ _ _ => fail
    | |- _ = _ => solve_eq
    | |- _ => progress (hnf; intros);
              try match goal with H : ?c = strip _ |- _ => is_var c; subst c end
    end
  | lazymatch goal with
    | |- strel _ (SRet _) (SRet _) => constructor
    | |- strel _ (SVis _ _) (SVis _ _) => constructor; intros ?
    | |- strel _ (eruns _ _ _ (if ?c then _ else _)) _ => scrut c
    | |- strel _ (eruns _ _ _ (match ?x with _ => _ end)) _ => scrut x
    | |- strel _ (prun _ _ _ (if ?c then _ else _)) _ => scrut c
    | |- strel _ (prun _ _ _ (match ?x with _ => _ end)) _ => scrut x
    | |- strel _ _ _ => use_hyp
    end
  | match goal with |- ?g => scrut g end ].
Ltac sync := csimp; srw; repeat (sync1; csimp; srw).


Section CPS.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Context {R1 R2 : Type} (RR : O * R1 -> R2 -> Prop).
Local Notation KREL := (KREL pans pupd).
Local Notation KREL0 := (KREL0 pans pupd).
Local Notation BREL := (BREL pans pupd).
Local Notation prun := (prun pans pupd).

Lemma queue_ctrl h m k1 k2 b1 b2 :
  KREL0 RR k1 k2 -> BREL RR b1 b2 ->
  forall o st cst, cst = strip st -> strel RR (prun o (queue h m st k1 b1)) (queue h m cst k2 b2).
Proof. intros HK HB o st cst ->. unfold queue, guard. sync. Qed.

Lemma free_meta_ctrl m k1 k2 b1 b2 :
  KREL0 RR k1 k2 -> BREL RR b1 b2 ->
  forall o st cst, cst = strip st -> strel RR (prun o (free_meta m st k1 b1)) (free_meta m cst k2 b2).
Proof. intros HK HB o st cst ->. unfold free_meta. eapply queue_ctrl; eauto. Qed.

Lemma activate_group_ctrl m k1 k2 b1 b2 :
  KREL RR k1 k2 -> BREL RR b1 b2 ->
  forall o st cst, cst = strip st -> strel RR (prun o (activate_group m st k1 b1)) (activate_group m cst k2 b2).
Proof. intros HK HB o st cst ->. unfold activate_group, guard. sync. Qed.

Lemma am_take_ctrl k1 k2 b1 b2 :
  KREL RR k1 k2 -> BREL RR b1 b2 ->
  forall o st cst, cst = strip st -> strel RR (prun o (am_take st k1 b1)) (am_take cst k2 b2).
Proof. intros HK HB o st cst ->. unfold am_take. sync. Qed.

Lemma am_carve_ctrl p k1 k2 b1 b2 :
  KREL RR k1 k2 -> BREL RR b1 b2 ->
  forall o st cst, cst = strip st -> strel RR (prun o (am_carve st p k1 b1)) (am_carve cst p k2 b2).
Proof. intros HK HB o st cst ->. pose proof (am_take_ctrl k1 k2 b1 b2 HK HB) as HT. unfold am_carve. sync. Qed.

Lemma am_finish_ctrl nu k1 k2 b1 b2 :
  KREL RR k1 k2 -> BREL RR b1 b2 ->
  forall o st cst, cst = strip st -> strel RR (prun o (am_finish st nu k1 b1)) (am_finish cst nu k2 b2).
Proof. intros HK HB o st cst ->. pose proof (am_carve_ctrl) as HC. unfold am_finish, bad_answer. sync. Qed.

Lemma am_after_brk_ctrl nu k1 k2 b1 b2 :
  KREL RR k1 k2 -> BREL RR b1 b2 ->
  forall o st cst, cst = strip st -> strel RR (prun o (am_after_brk st nu k1 b1)) (am_after_brk cst nu k2 b2).
Proof. intros HK HB o st cst ->. pose proof (am_finish_ctrl) as HF. unfold am_after_brk, bad_answer. sync. Qed.

Lemma alloc_meta_ctrl k1 k2 b1 b2 :
  KREL RR k1 k2 -> BREL RR b1 b2 ->
  forall o st cst, cst = strip st -> strel RR (prun o (alloc_meta st k1 b1)) (alloc_meta cst k2 b2).
Proof.
  intros HK HB o st cst ->. pose proof (am_after_brk_ctrl) as HA. pose proof (am_take_ctrl k1 k2 b1 b2 HK HB) as HT.
  unfold alloc_meta, bad_answer. sync.
Qed.

Lemma ta_fin_ctrl m mask k1 k2 :
  KREL RR k1 k2 ->
  forall o st cst, cst = strip st -> strel RR (prun o (ta_fin st m mask k1)) (ta_fin cst m mask k2).
Proof. intros HK o st cst ->. unfold ta_fin. sync. Qed.

Lemma try_avail_ctrl sc k1 k2 b1 b2 :
  KREL RR k1 k2 -> BREL RR b1 b2 ->
  forall o st cst, cst = strip st -> strel RR (prun o (try_avail sc st k1 b1)) (try_avail sc cst k2 b2).
Proof.
  intros HK HB o st cst ->. pose proof (ta_fin_ctrl) as HF. pose proof (activate_group_ctrl) as HA.
  unfold try_avail, guard. sync.
Qed.

Lemma ag_tail_ctrl sc m p cnt ai k1 k2 :
  KREL RR k1 k2 ->
  forall o st cst, cst = strip st -> strel RR (prun o (ag_tail full_lay st sc m p cnt ai k1)) (ag_tail lay_none cst sc m p cnt ai k2).
Proof. intros HK o st cst ->. unfold ag_tail. cbn [lh_hdr full_lay lay_none]. rewrite <- (strip_hdr_havoc p st). sync.
Qed.

Lemma alloc_group_ctrl rec1 rec2 sc req k1 k2 b1 b2 :
  (forall sc' req' k1' k2' b1' b2', KREL RR k1' k2' -> BREL RR b1' b2' ->
     forall o st cst, cst = strip st -> strel RR (prun o (rec1 st sc' req' k1' b1')) (rec2 cst sc' req' k2' b2')) ->
  KREL RR k1 k2 -> BREL RR b1 b2 ->
  forall o st cst, cst = strip st ->
  strel RR (prun o (alloc_group R1 full_lay rec1 st sc req k1 b1)) (alloc_group R2 lay_none rec2 cst sc req k2 b2).
Proof.
  intros HR HK HB o st cst ->. pose proof (ag_tail_ctrl) as HT. pose proof (free_meta_ctrl) as HF. pose proof (alloc_meta_ctrl) as HA.
  unfold alloc_group, bad_answer. cbn [lh_nest full_lay lay_none]. sync.
Qed.

Lemma alloc_slot_ctrl fuel : forall sc req k1 k2 b1 b2,
  KREL RR k1 k2 -> BREL RR b1 b2 ->
  forall o st cst, cst = strip st ->
  strel RR (prun o (alloc_slot full_lay fuel st sc req k1 b1)) (alloc_slot lay_none fuel cst sc req k2 b2).
Proof.
  induction fuel as [|f IH]; intros sc req k1 k2 b1 b2 HK HB o st cst ->.
  { cbn [alloc_slot]. sync. }
  pose proof (try_avail_ctrl) as HTA. pose proof (queue_ctrl) as HQ.
  pose proof (alloc_group_ctrl (alloc_slot full_lay f) (alloc_slot lay_none f)) as HG.
  cbn [alloc_slot]. sync.
Qed.


Definition DREL {X1 X2} (XX : O * X1 -> X2 -> Prop) (dec1 : decoder X1) (dec2 : decoder X2) : Prop :=
  forall p k1 k2 b1 b2,
    (forall o m idx, strel XX (prun o (k1 m idx)) (k2 m idx)) ->
    BREL XX b1 b2 ->
    forall o st cst, cst = strip st -> strel XX (prun o (dec1 st p k1 b1)) (dec2 cst p k2 b2).

Lemma dec_slots_drel : DREL RR (@dec_slots R1) (@dec_slots R2).
Proof.
  intros p k1 k2 b1 b2 HK HB o st cst ->. unfold dec_slots. srw.
  destruct (s_slots st !! p) as [[m idx]|]; [apply HK | sync].
Qed.

Lemma free_group_ctrl (dec1 : decoder R1) (dec2 : decoder R2) rec1 rec2 g k1 k2 b1 b2 :
  DREL RR dec1 dec2 ->
  (forall g' i' k1' k2' b1' b2', KREL RR k1' k2' -> BREL RR b1' b2' ->
     forall o st cst, cst = strip st -> strel RR (prun o (rec1 st g' i' k1' b1')) (rec2 cst g' i' k2' b2')) ->
  KREL RR k1 k2 -> BREL RR b1 b2 ->
  forall o st cst, cst = strip st ->
  strel RR (prun o (free_group R1 dec1 rec1 st g k1 b1)) (free_group R2 dec2 rec2 cst g k2 b2).
Proof.
  intros HD HR HK HB o st cst ->. pose proof (free_meta_ctrl) as HF.
  unfold free_group. sync.
  all: try (eapply HD; [ intros ? ? ? | assumption | solve_eq ]; sync).
Qed.

Lemma nontrivial_free_ctrl (dec1 : decoder R1) (dec2 : decoder R2) (HD : DREL RR dec1 dec2) fuel :
  forall g i k1 k2 b1 b2,
  KREL RR k1 k2 -> BREL RR b1 b2 ->
  forall o st cst, cst = strip st ->
  strel RR (prun o (nontrivial_free dec1 fuel st g i k1 b1)) (nontrivial_free dec2 fuel cst g i k2 b2).
Proof.
  induction fuel as [|f IH]; intros g i k1 k2 b1 b2 HK HB o st cst ->.
  { cbn [nontrivial_free]. sync. }
  pose proof (free_group_ctrl dec1 dec2 (nontrivial_free dec1 f) (nontrivial_free dec2 f) g) as HG.
  pose proof (activate_group_ctrl) as HA. pose proof (queue_ctrl) as HQ.
  cbn [nontrivial_free]. unfold guard. sync.
Qed.

End CPS.

Section TOP.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Local Notation KREL := (KREL pans pupd).
Local Notation BREL := (BREL pans pupd).

Definition CREL (x : O * (mstate * option (aptr * Z))) (y : mstate * option (aptr * Z)) : Prop :=
  strip (fst (snd x)) = fst y /\ snd (snd x) = snd y.

Lemma malloc_small_ctrl_ctrl {R1 R2} (RR : O * R1 -> R2 -> Prop) n k1 k2 b1 b2 :
  KREL RR k1 k2 -> BREL RR b1 b2 ->
  forall o st cst, cst = strip st ->
  strel RR ((prun pans pupd) o (malloc_small_ctrl full_lay st n k1 b1)) (malloc_small_ctrl lay_none cst n k2 b2).
Proof.
  intros HK HB o st cst ->. pose proof (alloc_slot_ctrl pans pupd RR FUEL) as HS.
  unfold malloc_small_ctrl. sync.
Qed.

Lemma malloc_core_ctrl n : forall o st cst, cst = strip st ->
  strel CREL ((prun pans pupd) o (malloc_core full_lay st n)) (malloc_core lay_none cst n).
Proof.
  intros o st cst ->.
  pose proof (@malloc_small_ctrl_ctrl _ _ CREL) as HS. pose proof (@alloc_meta_ctrl O pans pupd _ _ CREL) as HA.
  unfold malloc_core, bad_answer, ret. sync.
  all: try (split; [ solve_eq | reflexivity ]).
Qed.


Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.

Lemma rd8_prun {R} st p (k : Z -> M R) o :
  exists o' v, (prun pans pupd) o (rd8 st p k) = (prun pans pupd) o' (k v).
Proof.
  unfold rd8. destruct (cell_read _ _) as [v|hint].
  - exists o, v; reflexivity.
  - unfold prun. cbn [eruns psel].
    destruct (peek_answer_ok (pans o p (conc st p) hint)) eqn:E.
    + eexists _, _; reflexivity.
    + exfalso. unfold peek_answer_ok in E. pose proof (Hpans o p (conc st p) hint).
      apply Bool.andb_false_iff in E. destruct E as [E|E]; [apply Z.leb_gt in E|apply Z.ltb_ge in E]; lia.
Qed.

Lemma rd16_prun {R} st p (k : Z -> M R) o :
  exists o' v, (prun pans pupd) o (rd16 st p k) = (prun pans pupd) o' (k v).
Proof.
  unfold rd16. destruct (rd8_prun st p (fun b0 => rd8 st (aadd p 1) (fun b1 => k (b0 + 256 * b1))) o) as (o1 & v1 & ->).
  destruct (rd8_prun st (aadd p 1) (fun b1 => k (v1 + 256 * b1)) o1) as (o2 & v2 & ->). eauto.
Qed.

Lemma enframe_read_off_prun {R} st g idx n ctr (k : Z -> M R) o :
  exists o' off, (prun pans pupd) o (enframe_read_off st g idx n ctr k) = (prun pans pupd) o' (k off).
Proof.
  unfold enframe_read_off.
  match goal with |- exists o' off, (prun pans pupd) o (rd8 ?s ?q ?kk) = _ => destruct (rd8_prun s q kk o) as (o1 & b3 & ->) end.
  destruct (negb (b3 =? 0)).
  - match goal with |- exists o' off, (prun pans pupd) o1 (rd16 ?s ?q ?kk) = _ => destruct (rd16_prun s q kk o1) as (o2 & v & ->) end. eauto.
  - eauto.
Qed.

Lemma enframe_at_ptr st g idx n off :
  snd (enframe_at st g idx n off) = slot_of st g idx \/ snd (enframe_at st g idx n off) = aadd (slot_of st g idx) (UNIT * off).
Proof.
  unfold enframe_at, slot_of, slot_start'. destruct (negb (off =? 0)); cbn -[Z.add Z.mul Z.sub get_stride]; auto.
Qed.

Definition MREL (x : O * (mstate * optr)) (y : mstate * option cptr) : Prop :=
  strip (fst (snd x)) = fst y /\
  match snd (snd x), snd y with
  | None, None => True
  | Some p, Some c => fst p = fst c /\ exists off, snd p = snd c + UNIT * off
  | _, _ => False
  end.

Lemma strel_smap_r {E A R1 R2 R3} (RR : R1 -> R2 -> Prop) (SS : R1 -> R3 -> Prop) (f : R2 -> R3)
  (t1 : stree E A R1) (t2 : stree E A R2) :
  strel RR t1 t2 -> (forall a b, RR a b -> SS a (f b)) -> strel SS t1 (smap f t2).
Proof. induction 1; intros; cbn; constructor; auto. Qed.

Lemma strel_steq_l {E A R1 R2} (RR : R1 -> R2 -> Prop) (t1 t1' : stree E A R1) (t2 : stree E A R2) :
  steq t1 t1' -> strel RR t1' t2 -> strel RR t1 t2.
Proof.
  intros H; revert t2; induction H; intros t2 Ht; inversion Ht; subst; constructor; eauto.
Qed.

Theorem malloc_control st n o :
  strel MREL ((prun pans pupd) o (malloc st n)) (cmalloc (strip st) n).
Proof.
  unfold malloc, cmalloc.
  eapply strel_steq_l. { unfold prun. apply eruns_sbind. }
  eapply strel_sbind.
  { apply (malloc_core_ctrl n o (set_tick (N.succ (s_tick st)) st)). reflexivity. }
  intros [o1 [S r]] [S' r'] [HS Hr]; cbn in HS, Hr; subst r' S'.
  destruct r as [[g idx]|].
  - destruct (enframe_read_off_prun S g idx n (c_mmap_counter (ctx S))
               (fun off => let '(st1, p) := enframe_at S g idx n off in ret (havoc p n st1, Some p)) o1) as (o2 & off & E).
    unfold enframe_full. cbn [fst snd]. unfold prun in E |- *. rewrite E.
    destruct (enframe_at S g idx n off) as [st1 p] eqn:Ea. unfold prun, ret; cbn [eruns psel]. constructor.
    split; cbn.
    + rewrite strip_havoc, strip_strip. pose proof (strip_enframe_at S g idx n off) as H1. rewrite Ea in H1. exact H1.
    + rewrite ?get_meta_rec_strip. pose proof (enframe_at_ptr S g idx n off) as Hp. rewrite Ea in Hp.
      unfold slot_of, slot_start', aadd in Hp. cbn [fst snd] in Hp.
      destruct Hp as [-> | ->]; cbn [fst snd]; [split; [reflexivity| exists 0; lia] | split; [reflexivity | exists off; lia]].
  - unfold prun, ret; cbn [eruns psel]. constructor. split; cbn; [rewrite strip_strip; reflexivity | exact I].
Qed.


Definition FREL (x : O * mstate) (y : mstate) : Prop := strip (snd x) = y.

Theorem free_tail_control (dec1 dec2 : decoder mstate) :
  DREL pans pupd (fun x y => strip (snd x) = strip y) dec1 dec2 ->
  forall st g idx o cst, cst = strip st ->
  strel (fun x y => strip (snd x) = strip y) ((prun pans pupd) o (free_tail dec1 st g idx)) (free_tail dec2 cst g idx).
Proof.
  intros HD st g idx o cst ->.
  pose proof (nontrivial_free_ctrl pans pupd (fun x y => strip (snd x) = strip y) dec1 dec2 HD FUEL) as HN.
  unfold free_tail, guard, bad_answer, ret. sync.
  all: cbn; rewrite ?strip_strip; try reflexivity; try solve_eq.
Qed.

Definition hdr_ok (st : mstate) (p : aptr) (c : cptr) : Prop :=
  exists st1 g idx,
    (forall o, (prun pans pupd) o (free_hdr st p) = SRet (o, Some (st1, g, idx)))
    /\ strip st1 = strip st
    /\ (s_slots st) !! c = Some (g, idx)
    /\ (forall o, strel (fun x y => strip (snd x) = strip y)
                        ((prun pans pupd) o (free_tail dec_hdr st1 g idx))
                        (free_tail dec_slots (strip st) g idx)).

Theorem free_control st p c o :
  hdr_ok st p c ->
  strel FREL ((prun pans pupd) o (free st (Some p))) (cfree (strip st) (Some c)).
Proof.
  intros (st1 & g & idx & Hh & Hs & Hc & Ht).
  unfold free, cfree. rewrite s_slots_strip, Hc.
  eapply strel_steq_l. { unfold prun. apply eruns_sbind. }
  unfold prun in Hh, Ht |- *. rewrite Hh. cbn [sbind fst snd].
  change (x__ <-- free_tail dec_slots (strip st) g idx;; ret (strip x__))
    with (smap strip (free_tail dec_slots (strip st) g idx)).
  apply (strel_smap_r _ _ _ _ _ (Ht o)). intros [o1 S] S' HS. exact HS.
Qed.

Lemma free_tail_slots_control st g idx o :
  strel (fun x y => strip (snd x) = strip y)
        ((prun pans pupd) o (free_tail dec_slots st g idx)) (free_tail dec_slots (strip st) g idx).
Proof. apply free_tail_control; [apply dec_slots_drel | reflexivity]. Qed.


Fixpoint follow {R} (t : M R) (ans : list Z) : option R :=
  match t, ans with
  | SRet r, _ => Some r
  | SVis (EUndef _) _, _ => None
  | SVis _ k, a :: ans' => follow (k a) ans'
  | SVis _ _, [] => None
  end.

Inductive reach : mstate -> list aptr -> list cptr -> Prop :=
| reach_init secret res atop : reach (minit secret res atop) [] []
| reach_malloc st L C n o ans o' st' p cst c :
    reach st L C ->
    follow ((prun pans pupd) o (malloc st n)) ans = Some (o', (st', Some p)) ->
    follow (cmalloc (strip st) n) ans = Some (cst, Some c) ->
    reach st' (p :: L) (c :: C)
| reach_malloc_null st L C n o ans o' st' cst :
    reach st L C ->
    follow ((prun pans pupd) o (malloc st n)) ans = Some (o', (st', None)) ->
    follow (cmalloc (strip st) n) ans = Some (cst, None) ->
    reach st' L C
| reach_free st L C i p c o ans o' st' :
    reach st L C ->
    nth_error L i = Some p -> nth_error C i = Some c ->
    follow ((prun pans pupd) o (free st (Some p))) ans = Some (o', st') ->
    reach st' (delete i L) (delete i C)
| reach_free_null st L C o ans o' st' :
    reach st L C ->
    follow ((prun pans pupd) o (free st None)) ans = Some (o', st') ->
    reach st' L C.


End TOP.
End MallocCtrl.

Module MI_Kit.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Bool. From Stdlib Require Import Lia.
From stdpp Require Import gmap.
Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Malloc. Import MallocCtrl.
Unset Lia Cache.
Unset Nia Cache.
Import ListNotations.
Local Open Scope Z_scope.


Lemma aptr_eqb_refl (a : aptr) : aptr_eqb a a = true.
Proof. unfold aptr_eqb. rewrite N.eqb_refl, Z.eqb_refl. reflexivity. Qed.

Lemma aptr_eqb_eq (a b : aptr) : aptr_eqb a b = true <-> a = b.
Proof.
  unfold aptr_eqb. destruct a as [r o], b as [r' o']; cbn. rewrite Bool.andb_true_iff, N.eqb_eq, Z.eqb_eq.
  split; [intros [-> ->]; reflexivity| intros H; inversion H; auto].
Qed.

Lemma aptr_eqb_spec (a b : aptr) : reflect (a = b) (aptr_eqb a b).
Proof.
  destruct (aptr_eqb a b) eqn:E; constructor.
  - apply aptr_eqb_eq. exact E.
  - intros ->. rewrite aptr_eqb_refl in E. discriminate.
Qed.

Lemma aptr_eqb_neq (a b : aptr) : a <> b -> aptr_eqb a b = false.
Proof. intros H. destruct (aptr_eqb_spec a b); [contradiction| reflexivity]. Qed.

Lemma optr_eqb_spec (a b : optr) : reflect (a = b) (optr_eqb a b).
Proof.
  destruct a as [a|], b as [b|]; cbn; try (constructor; congruence).
  destruct (aptr_eqb_spec a b); constructor; congruence.
Qed.

Lemma optr_eqb_refl (a : optr) : optr_eqb a a = true.
Proof. destruct (optr_eqb_spec a a); [reflexivity| contradiction]. Qed.

Ltac case_ptr x y := destruct (aptr_eqb_spec x y) as [?EQp|?NEp]; [first [subst x | subst y | idtac]|].

#[export] Instance aptr_eq_dec : EqDecision aptr := _.


Lemma get_meta_rec_put st m r x :
  get_meta_rec (put_meta m r st) x = if aptr_eqb x m then r else get_meta_rec st x.
Proof.
  unfold get_meta_rec, put_meta; cbn. destruct (aptr_eqb_spec x m) as [->|NE].
  - rewrite lookup_insert_eq. reflexivity.
  - rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma get_meta_rec_upd st m f x :
  get_meta_rec (upd_meta m f st) x = if aptr_eqb x m then f (get_meta_rec st m) else get_meta_rec st x.
Proof. unfold upd_meta. apply get_meta_rec_put. Qed.

Lemma get_meta_rec_put_same st m r : get_meta_rec (put_meta m r st) m = r.
Proof. rewrite get_meta_rec_put, aptr_eqb_refl. reflexivity. Qed.
Lemma get_meta_rec_put_other st m r x : x <> m -> get_meta_rec (put_meta m r st) x = get_meta_rec st x.
Proof. intros H. rewrite get_meta_rec_put, aptr_eqb_neq by exact H. reflexivity. Qed.
Lemma get_meta_rec_upd_same st m f : get_meta_rec (upd_meta m f st) m = f (get_meta_rec st m).
Proof. rewrite get_meta_rec_upd, aptr_eqb_refl. reflexivity. Qed.
Lemma get_meta_rec_upd_other st m f x : x <> m -> get_meta_rec (upd_meta m f st) x = get_meta_rec st x.
Proof. intros H. rewrite get_meta_rec_upd, aptr_eqb_neq by exact H. reflexivity. Qed.

Lemma s_metas_put_meta m r st : s_metas (put_meta m r st) = <[m := r]> (s_metas st).
Proof. reflexivity. Qed.
Lemma s_metas_upd_meta m f st : s_metas (upd_meta m f st) = <[m := f (get_meta_rec st m)]> (s_metas st).
Proof. reflexivity. Qed.

Lemma lookup_metas_put st m r x :
  s_metas (put_meta m r st) !! x = if aptr_eqb x m then Some r else s_metas st !! x.
Proof.
  cbn. destruct (aptr_eqb_spec x m) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.
Lemma lookup_metas_upd st m f x :
  s_metas (upd_meta m f st) !! x = if aptr_eqb x m then Some (f (get_meta_rec st m)) else s_metas st !! x.
Proof. unfold upd_meta. apply lookup_metas_put. Qed.

Lemma get_meta_rec_ext st st' x : s_metas st' = s_metas st -> get_meta_rec st' x = get_meta_rec st x.
Proof. intros H. unfold get_meta_rec. rewrite H. reflexivity. Qed.

Ltac msimp := cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen
                   m_set_prev m_set_next m_set_mem m_set_avail m_set_freed m_set_last_idx m_set_freeable m_set_sizeclass m_set_maplen
                   meta0] in *.

Lemma s_ctx_upd_ctx f st : s_ctx (upd_ctx f st) = f (s_ctx st). Proof. reflexivity. Qed.
Lemma s_regions_upd_ctx f st : s_regions (upd_ctx f st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_shadow_upd_ctx f st : s_shadow (upd_ctx f st) = s_shadow st. Proof. reflexivity. Qed.
Lemma s_next_rid_upd_ctx f st : s_next_rid (upd_ctx f st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_metas_upd_ctx f st : s_metas (upd_ctx f st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_upd_ctx f st : s_areas (upd_ctx f st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_upd_ctx f st : s_groups (upd_ctx f st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_slots_upd_ctx f st : s_slots (upd_ctx f st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_tick_upd_ctx f st : s_tick (upd_ctx f st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_upd_ctx f st : s_secret (upd_ctx f st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_upd_ctx f st : s_reserved (upd_ctx f st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_atop_upd_ctx f st : s_atop (upd_ctx f st) = s_atop st. Proof. reflexivity. Qed.
Lemma s_ctx_set_regions v st : s_ctx (set_regions v st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_regions_set_regions v st : s_regions (set_regions v st) = v. Proof. reflexivity. Qed.
Lemma s_shadow_set_regions v st : s_shadow (set_regions v st) = s_shadow st. Proof. reflexivity. Qed.
Lemma s_next_rid_set_regions v st : s_next_rid (set_regions v st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_metas_set_regions v st : s_metas (set_regions v st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_set_regions v st : s_areas (set_regions v st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_set_regions v st : s_groups (set_regions v st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_slots_set_regions v st : s_slots (set_regions v st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_tick_set_regions v st : s_tick (set_regions v st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_set_regions v st : s_secret (set_regions v st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_set_regions v st : s_reserved (set_regions v st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_atop_set_regions v st : s_atop (set_regions v st) = s_atop st. Proof. reflexivity. Qed.
Lemma s_ctx_set_shadow v st : s_ctx (set_shadow v st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_regions_set_shadow v st : s_regions (set_shadow v st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_shadow_set_shadow v st : s_shadow (set_shadow v st) = v. Proof. reflexivity. Qed.
Lemma s_next_rid_set_shadow v st : s_next_rid (set_shadow v st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_metas_set_shadow v st : s_metas (set_shadow v st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_set_shadow v st : s_areas (set_shadow v st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_set_shadow v st : s_groups (set_shadow v st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_slots_set_shadow v st : s_slots (set_shadow v st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_tick_set_shadow v st : s_tick (set_shadow v st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_set_shadow v st : s_secret (set_shadow v st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_set_shadow v st : s_reserved (set_shadow v st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_atop_set_shadow v st : s_atop (set_shadow v st) = s_atop st. Proof. reflexivity. Qed.
Lemma s_ctx_set_next_rid v st : s_ctx (set_next_rid v st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_regions_set_next_rid v st : s_regions (set_next_rid v st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_shadow_set_next_rid v st : s_shadow (set_next_rid v st) = s_shadow st. Proof. reflexivity. Qed.
Lemma s_next_rid_set_next_rid v st : s_next_rid (set_next_rid v st) = v. Proof. reflexivity. Qed.
Lemma s_metas_set_next_rid v st : s_metas (set_next_rid v st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_set_next_rid v st : s_areas (set_next_rid v st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_set_next_rid v st : s_groups (set_next_rid v st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_slots_set_next_rid v st : s_slots (set_next_rid v st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_tick_set_next_rid v st : s_tick (set_next_rid v st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_set_next_rid v st : s_secret (set_next_rid v st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_set_next_rid v st : s_reserved (set_next_rid v st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_atop_set_next_rid v st : s_atop (set_next_rid v st) = s_atop st. Proof. reflexivity. Qed.
Lemma s_ctx_set_metas v st : s_ctx (set_metas v st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_regions_set_metas v st : s_regions (set_metas v st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_shadow_set_metas v st : s_shadow (set_metas v st) = s_shadow st. Proof. reflexivity. Qed.
Lemma s_next_rid_set_metas v st : s_next_rid (set_metas v st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_metas_set_metas v st : s_metas (set_metas v st) = v. Proof. reflexivity. Qed.
Lemma s_areas_set_metas v st : s_areas (set_metas v st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_set_metas v st : s_groups (set_metas v st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_slots_set_metas v st : s_slots (set_metas v st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_tick_set_metas v st : s_tick (set_metas v st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_set_metas v st : s_secret (set_metas v st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_set_metas v st : s_reserved (set_metas v st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_atop_set_metas v st : s_atop (set_metas v st) = s_atop st. Proof. reflexivity. Qed.
Lemma s_ctx_set_areas v st : s_ctx (set_areas v st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_regions_set_areas v st : s_regions (set_areas v st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_shadow_set_areas v st : s_shadow (set_areas v st) = s_shadow st. Proof. reflexivity. Qed.
Lemma s_next_rid_set_areas v st : s_next_rid (set_areas v st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_metas_set_areas v st : s_metas (set_areas v st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_set_areas v st : s_areas (set_areas v st) = v. Proof. reflexivity. Qed.
Lemma s_groups_set_areas v st : s_groups (set_areas v st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_slots_set_areas v st : s_slots (set_areas v st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_tick_set_areas v st : s_tick (set_areas v st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_set_areas v st : s_secret (set_areas v st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_set_areas v st : s_reserved (set_areas v st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_atop_set_areas v st : s_atop (set_areas v st) = s_atop st. Proof. reflexivity. Qed.
Lemma s_ctx_set_groups v st : s_ctx (set_groups v st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_regions_set_groups v st : s_regions (set_groups v st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_shadow_set_groups v st : s_shadow (set_groups v st) = s_shadow st. Proof. reflexivity. Qed.
Lemma s_next_rid_set_groups v st : s_next_rid (set_groups v st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_metas_set_groups v st : s_metas (set_groups v st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_set_groups v st : s_areas (set_groups v st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_set_groups v st : s_groups (set_groups v st) = v. Proof. reflexivity. Qed.
Lemma s_slots_set_groups v st : s_slots (set_groups v st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_tick_set_groups v st : s_tick (set_groups v st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_set_groups v st : s_secret (set_groups v st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_set_groups v st : s_reserved (set_groups v st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_atop_set_groups v st : s_atop (set_groups v st) = s_atop st. Proof. reflexivity. Qed.
Lemma s_ctx_set_slots v st : s_ctx (set_slots v st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_regions_set_slots v st : s_regions (set_slots v st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_shadow_set_slots v st : s_shadow (set_slots v st) = s_shadow st. Proof. reflexivity. Qed.
Lemma s_next_rid_set_slots v st : s_next_rid (set_slots v st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_metas_set_slots v st : s_metas (set_slots v st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_set_slots v st : s_areas (set_slots v st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_set_slots v st : s_groups (set_slots v st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_slots_set_slots v st : s_slots (set_slots v st) = v. Proof. reflexivity. Qed.
Lemma s_tick_set_slots v st : s_tick (set_slots v st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_set_slots v st : s_secret (set_slots v st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_set_slots v st : s_reserved (set_slots v st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_atop_set_slots v st : s_atop (set_slots v st) = s_atop st. Proof. reflexivity. Qed.
Lemma s_ctx_set_tick v st : s_ctx (set_tick v st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_regions_set_tick v st : s_regions (set_tick v st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_shadow_set_tick v st : s_shadow (set_tick v st) = s_shadow st. Proof. reflexivity. Qed.
Lemma s_next_rid_set_tick v st : s_next_rid (set_tick v st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_metas_set_tick v st : s_metas (set_tick v st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_set_tick v st : s_areas (set_tick v st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_set_tick v st : s_groups (set_tick v st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_slots_set_tick v st : s_slots (set_tick v st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_tick_set_tick v st : s_tick (set_tick v st) = v. Proof. reflexivity. Qed.
Lemma s_secret_set_tick v st : s_secret (set_tick v st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_set_tick v st : s_reserved (set_tick v st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_atop_set_tick v st : s_atop (set_tick v st) = s_atop st. Proof. reflexivity. Qed.
Lemma c_secret_set_secret v c : c_secret (set_secret v c) = v. Proof. reflexivity. Qed.
Lemma c_init_done_set_secret v c : c_init_done (set_secret v c) = c_init_done c. Proof. reflexivity. Qed.
Lemma c_mmap_counter_set_secret v c : c_mmap_counter (set_secret v c) = c_mmap_counter c. Proof. reflexivity. Qed.
Lemma c_free_meta_head_set_secret v c : c_free_meta_head (set_secret v c) = c_free_meta_head c. Proof. reflexivity. Qed.
Lemma c_avail_meta_set_secret v c : c_avail_meta (set_secret v c) = c_avail_meta c. Proof. reflexivity. Qed.
Lemma c_avail_meta_count_set_secret v c : c_avail_meta_count (set_secret v c) = c_avail_meta_count c. Proof. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_secret v c : c_avail_meta_area_count (set_secret v c) = c_avail_meta_area_count c. Proof. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_secret v c : c_meta_alloc_shift (set_secret v c) = c_meta_alloc_shift c. Proof. reflexivity. Qed.
Lemma c_meta_area_head_set_secret v c : c_meta_area_head (set_secret v c) = c_meta_area_head c. Proof. reflexivity. Qed.
Lemma c_meta_area_tail_set_secret v c : c_meta_area_tail (set_secret v c) = c_meta_area_tail c. Proof. reflexivity. Qed.
Lemma c_avail_meta_areas_set_secret v c : c_avail_meta_areas (set_secret v c) = c_avail_meta_areas c. Proof. reflexivity. Qed.
Lemma c_active_set_secret v c : c_active (set_secret v c) = c_active c. Proof. reflexivity. Qed.
Lemma c_usage_set_secret v c : c_usage (set_secret v c) = c_usage c. Proof. reflexivity. Qed.
Lemma c_unmap_seq_set_secret v c : c_unmap_seq (set_secret v c) = c_unmap_seq c. Proof. reflexivity. Qed.
Lemma c_bounces_set_secret v c : c_bounces (set_secret v c) = c_bounces c. Proof. reflexivity. Qed.
Lemma c_seq_set_secret v c : c_seq (set_secret v c) = c_seq c. Proof. reflexivity. Qed.
Lemma c_brk_set_secret v c : c_brk (set_secret v c) = c_brk c. Proof. reflexivity. Qed.
Lemma c_secret_set_init_done v c : c_secret (set_init_done v c) = c_secret c. Proof. reflexivity. Qed.
Lemma c_init_done_set_init_done v c : c_init_done (set_init_done v c) = v. Proof. reflexivity. Qed.
Lemma c_mmap_counter_set_init_done v c : c_mmap_counter (set_init_done v c) = c_mmap_counter c. Proof. reflexivity. Qed.
Lemma c_free_meta_head_set_init_done v c : c_free_meta_head (set_init_done v c) = c_free_meta_head c. Proof. reflexivity. Qed.
Lemma c_avail_meta_set_init_done v c : c_avail_meta (set_init_done v c) = c_avail_meta c. Proof. reflexivity. Qed.
Lemma c_avail_meta_count_set_init_done v c : c_avail_meta_count (set_init_done v c) = c_avail_meta_count c. Proof. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_init_done v c : c_avail_meta_area_count (set_init_done v c) = c_avail_meta_area_count c. Proof. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_init_done v c : c_meta_alloc_shift (set_init_done v c) = c_meta_alloc_shift c. Proof. reflexivity. Qed.
Lemma c_meta_area_head_set_init_done v c : c_meta_area_head (set_init_done v c) = c_meta_area_head c. Proof. reflexivity. Qed.
Lemma c_meta_area_tail_set_init_done v c : c_meta_area_tail (set_init_done v c) = c_meta_area_tail c. Proof. reflexivity. Qed.
Lemma c_avail_meta_areas_set_init_done v c : c_avail_meta_areas (set_init_done v c) = c_avail_meta_areas c. Proof. reflexivity. Qed.
Lemma c_active_set_init_done v c : c_active (set_init_done v c) = c_active c. Proof. reflexivity. Qed.
Lemma c_usage_set_init_done v c : c_usage (set_init_done v c) = c_usage c. Proof. reflexivity. Qed.
Lemma c_unmap_seq_set_init_done v c : c_unmap_seq (set_init_done v c) = c_unmap_seq c. Proof. reflexivity. Qed.
Lemma c_bounces_set_init_done v c : c_bounces (set_init_done v c) = c_bounces c. Proof. reflexivity. Qed.
Lemma c_seq_set_init_done v c : c_seq (set_init_done v c) = c_seq c. Proof. reflexivity. Qed.
Lemma c_brk_set_init_done v c : c_brk (set_init_done v c) = c_brk c. Proof. reflexivity. Qed.
Lemma c_secret_set_mmap_counter v c : c_secret (set_mmap_counter v c) = c_secret c. Proof. reflexivity. Qed.
Lemma c_init_done_set_mmap_counter v c : c_init_done (set_mmap_counter v c) = c_init_done c. Proof. reflexivity. Qed.
Lemma c_mmap_counter_set_mmap_counter v c : c_mmap_counter (set_mmap_counter v c) = v. Proof. reflexivity. Qed.
Lemma c_free_meta_head_set_mmap_counter v c : c_free_meta_head (set_mmap_counter v c) = c_free_meta_head c. Proof. reflexivity. Qed.
Lemma c_avail_meta_set_mmap_counter v c : c_avail_meta (set_mmap_counter v c) = c_avail_meta c. Proof. reflexivity. Qed.
Lemma c_avail_meta_count_set_mmap_counter v c : c_avail_meta_count (set_mmap_counter v c) = c_avail_meta_count c. Proof. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_mmap_counter v c : c_avail_meta_area_count (set_mmap_counter v c) = c_avail_meta_area_count c. Proof. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_mmap_counter v c : c_meta_alloc_shift (set_mmap_counter v c) = c_meta_alloc_shift c. Proof. reflexivity. Qed.
Lemma c_meta_area_head_set_mmap_counter v c : c_meta_area_head (set_mmap_counter v c) = c_meta_area_head c. Proof. reflexivity. Qed.
Lemma c_meta_area_tail_set_mmap_counter v c : c_meta_area_tail (set_mmap_counter v c) = c_meta_area_tail c. Proof. reflexivity. Qed.
Lemma c_avail_meta_areas_set_mmap_counter v c : c_avail_meta_areas (set_mmap_counter v c) = c_avail_meta_areas c. Proof. reflexivity. Qed.
Lemma c_active_set_mmap_counter v c : c_active (set_mmap_counter v c) = c_active c. Proof. reflexivity. Qed.
Lemma c_usage_set_mmap_counter v c : c_usage (set_mmap_counter v c) = c_usage c. Proof. reflexivity. Qed.
Lemma c_unmap_seq_set_mmap_counter v c : c_unmap_seq (set_mmap_counter v c) = c_unmap_seq c. Proof. reflexivity. Qed.
Lemma c_bounces_set_mmap_counter v c : c_bounces (set_mmap_counter v c) = c_bounces c. Proof. reflexivity. Qed.
Lemma c_seq_set_mmap_counter v c : c_seq (set_mmap_counter v c) = c_seq c. Proof. reflexivity. Qed.
Lemma c_brk_set_mmap_counter v c : c_brk (set_mmap_counter v c) = c_brk c. Proof. reflexivity. Qed.
Lemma c_secret_set_free_meta_head v c : c_secret (set_free_meta_head v c) = c_secret c. Proof. reflexivity. Qed.
Lemma c_init_done_set_free_meta_head v c : c_init_done (set_free_meta_head v c) = c_init_done c. Proof. reflexivity. Qed.
Lemma c_mmap_counter_set_free_meta_head v c : c_mmap_counter (set_free_meta_head v c) = c_mmap_counter c. Proof. reflexivity. Qed.
Lemma c_free_meta_head_set_free_meta_head v c : c_free_meta_head (set_free_meta_head v c) = v. Proof. reflexivity. Qed.
Lemma c_avail_meta_set_free_meta_head v c : c_avail_meta (set_free_meta_head v c) = c_avail_meta c. Proof. reflexivity. Qed.
Lemma c_avail_meta_count_set_free_meta_head v c : c_avail_meta_count (set_free_meta_head v c) = c_avail_meta_count c. Proof. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_free_meta_head v c : c_avail_meta_area_count (set_free_meta_head v c) = c_avail_meta_area_count c. Proof. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_free_meta_head v c : c_meta_alloc_shift (set_free_meta_head v c) = c_meta_alloc_shift c. Proof. reflexivity. Qed.
Lemma c_meta_area_head_set_free_meta_head v c : c_meta_area_head (set_free_meta_head v c) = c_meta_area_head c. Proof. reflexivity. Qed.
Lemma c_meta_area_tail_set_free_meta_head v c : c_meta_area_tail (set_free_meta_head v c) = c_meta_area_tail c. Proof. reflexivity. Qed.
Lemma c_avail_meta_areas_set_free_meta_head v c : c_avail_meta_areas (set_free_meta_head v c) = c_avail_meta_areas c. Proof. reflexivity. Qed.
Lemma c_active_set_free_meta_head v c : c_active (set_free_meta_head v c) = c_active c. Proof. reflexivity. Qed.
Lemma c_usage_set_free_meta_head v c : c_usage (set_free_meta_head v c) = c_usage c. Proof. reflexivity. Qed.
Lemma c_unmap_seq_set_free_meta_head v c : c_unmap_seq (set_free_meta_head v c) = c_unmap_seq c. Proof. reflexivity. Qed.
Lemma c_bounces_set_free_meta_head v c : c_bounces (set_free_meta_head v c) = c_bounces c. Proof. reflexivity. Qed.
Lemma c_seq_set_free_meta_head v c : c_seq (set_free_meta_head v c) = c_seq c. Proof. reflexivity. Qed.
Lemma c_brk_set_free_meta_head v c : c_brk (set_free_meta_head v c) = c_brk c. Proof. reflexivity. Qed.
Lemma c_secret_set_avail_meta v c : c_secret (set_avail_meta v c) = c_secret c. Proof. reflexivity. Qed.
Lemma c_init_done_set_avail_meta v c : c_init_done (set_avail_meta v c) = c_init_done c. Proof. reflexivity. Qed.
Lemma c_mmap_counter_set_avail_meta v c : c_mmap_counter (set_avail_meta v c) = c_mmap_counter c. Proof. reflexivity. Qed.
Lemma c_free_meta_head_set_avail_meta v c : c_free_meta_head (set_avail_meta v c) = c_free_meta_head c. Proof. reflexivity. Qed.
Lemma c_avail_meta_set_avail_meta v c : c_avail_meta (set_avail_meta v c) = v. Proof. reflexivity. Qed.
Lemma c_avail_meta_count_set_avail_meta v c : c_avail_meta_count (set_avail_meta v c) = c_avail_meta_count c. Proof. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_avail_meta v c : c_avail_meta_area_count (set_avail_meta v c) = c_avail_meta_area_count c. Proof. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_avail_meta v c : c_meta_alloc_shift (set_avail_meta v c) = c_meta_alloc_shift c. Proof. reflexivity. Qed.
Lemma c_meta_area_head_set_avail_meta v c : c_meta_area_head (set_avail_meta v c) = c_meta_area_head c. Proof. reflexivity. Qed.
Lemma c_meta_area_tail_set_avail_meta v c : c_meta_area_tail (set_avail_meta v c) = c_meta_area_tail c. Proof. reflexivity. Qed.
Lemma c_avail_meta_areas_set_avail_meta v c : c_avail_meta_areas (set_avail_meta v c) = c_avail_meta_areas c. Proof. reflexivity. Qed.
Lemma c_active_set_avail_meta v c : c_active (set_avail_meta v c) = c_active c. Proof. reflexivity. Qed.
Lemma c_usage_set_avail_meta v c : c_usage (set_avail_meta v c) = c_usage c. Proof. reflexivity. Qed.
Lemma c_unmap_seq_set_avail_meta v c : c_unmap_seq (set_avail_meta v c) = c_unmap_seq c. Proof. reflexivity. Qed.
Lemma c_bounces_set_avail_meta v c : c_bounces (set_avail_meta v c) = c_bounces c. Proof. reflexivity. Qed.
Lemma c_seq_set_avail_meta v c : c_seq (set_avail_meta v c) = c_seq c. Proof. reflexivity. Qed.
Lemma c_brk_set_avail_meta v c : c_brk (set_avail_meta v c) = c_brk c. Proof. reflexivity. Qed.
Lemma c_secret_set_avail_meta_count v c : c_secret (set_avail_meta_count v c) = c_secret c. Proof. reflexivity. Qed.
Lemma c_init_done_set_avail_meta_count v c : c_init_done (set_avail_meta_count v c) = c_init_done c. Proof. reflexivity. Qed.
Lemma c_mmap_counter_set_avail_meta_count v c : c_mmap_counter (set_avail_meta_count v c) = c_mmap_counter c. Proof. reflexivity. Qed.
Lemma c_free_meta_head_set_avail_meta_count v c : c_free_meta_head (set_avail_meta_count v c) = c_free_meta_head c. Proof. reflexivity. Qed.
Lemma c_avail_meta_set_avail_meta_count v c : c_avail_meta (set_avail_meta_count v c) = c_avail_meta c. Proof. reflexivity. Qed.
Lemma c_avail_meta_count_set_avail_meta_count v c : c_avail_meta_count (set_avail_meta_count v c) = v. Proof. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_avail_meta_count v c : c_avail_meta_area_count (set_avail_meta_count v c) = c_avail_meta_area_count c. Proof. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_avail_meta_count v c : c_meta_alloc_shift (set_avail_meta_count v c) = c_meta_alloc_shift c. Proof. reflexivity. Qed.
Lemma c_meta_area_head_set_avail_meta_count v c : c_meta_area_head (set_avail_meta_count v c) = c_meta_area_head c. Proof. reflexivity. Qed.
Lemma c_meta_area_tail_set_avail_meta_count v c : c_meta_area_tail (set_avail_meta_count v c) = c_meta_area_tail c. Proof. reflexivity. Qed.
Lemma c_avail_meta_areas_set_avail_meta_count v c : c_avail_meta_areas (set_avail_meta_count v c) = c_avail_meta_areas c. Proof. reflexivity. Qed.
Lemma c_active_set_avail_meta_count v c : c_active (set_avail_meta_count v c) = c_active c. Proof. reflexivity. Qed.
Lemma c_usage_set_avail_meta_count v c : c_usage (set_avail_meta_count v c) = c_usage c. Proof. reflexivity. Qed.
Lemma c_unmap_seq_set_avail_meta_count v c : c_unmap_seq (set_avail_meta_count v c) = c_unmap_seq c. Proof. reflexivity. Qed.
Lemma c_bounces_set_avail_meta_count v c : c_bounces (set_avail_meta_count v c) = c_bounces c. Proof. reflexivity. Qed.
Lemma c_seq_set_avail_meta_count v c : c_seq (set_avail_meta_count v c) = c_seq c. Proof. reflexivity. Qed.
Lemma c_brk_set_avail_meta_count v c : c_brk (set_avail_meta_count v c) = c_brk c. Proof. reflexivity. Qed.
Lemma c_secret_set_avail_meta_area_count v c : c_secret (set_avail_meta_area_count v c) = c_secret c. Proof. reflexivity. Qed.
Lemma c_init_done_set_avail_meta_area_count v c : c_init_done (set_avail_meta_area_count v c) = c_init_done c. Proof. reflexivity. Qed.
Lemma c_mmap_counter_set_avail_meta_area_count v c : c_mmap_counter (set_avail_meta_area_count v c) = c_mmap_counter c. Proof. reflexivity. Qed.
Lemma c_free_meta_head_set_avail_meta_area_count v c : c_free_meta_head (set_avail_meta_area_count v c) = c_free_meta_head c. Proof. reflexivity. Qed.
Lemma c_avail_meta_set_avail_meta_area_count v c : c_avail_meta (set_avail_meta_area_count v c) = c_avail_meta c. Proof. reflexivity. Qed.
Lemma c_avail_meta_count_set_avail_meta_area_count v c : c_avail_meta_count (set_avail_meta_area_count v c) = c_avail_meta_count c. Proof. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_avail_meta_area_count v c : c_avail_meta_area_count (set_avail_meta_area_count v c) = v. Proof. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_avail_meta_area_count v c : c_meta_alloc_shift (set_avail_meta_area_count v c) = c_meta_alloc_shift c. Proof. reflexivity. Qed.
Lemma c_meta_area_head_set_avail_meta_area_count v c : c_meta_area_head (set_avail_meta_area_count v c) = c_meta_area_head c. Proof. reflexivity. Qed.
Lemma c_meta_area_tail_set_avail_meta_area_count v c : c_meta_area_tail (set_avail_meta_area_count v c) = c_meta_area_tail c. Proof. reflexivity. Qed.
Lemma c_avail_meta_areas_set_avail_meta_area_count v c : c_avail_meta_areas (set_avail_meta_area_count v c) = c_avail_meta_areas c. Proof. reflexivity. Qed.
Lemma c_active_set_avail_meta_area_count v c : c_active (set_avail_meta_area_count v c) = c_active c. Proof. reflexivity. Qed.
Lemma c_usage_set_avail_meta_area_count v c : c_usage (set_avail_meta_area_count v c) = c_usage c. Proof. reflexivity. Qed.
Lemma c_unmap_seq_set_avail_meta_area_count v c : c_unmap_seq (set_avail_meta_area_count v c) = c_unmap_seq c. Proof. reflexivity. Qed.
Lemma c_bounces_set_avail_meta_area_count v c : c_bounces (set_avail_meta_area_count v c) = c_bounces c. Proof. reflexivity. Qed.
Lemma c_seq_set_avail_meta_area_count v c : c_seq (set_avail_meta_area_count v c) = c_seq c. Proof. reflexivity. Qed.
Lemma c_brk_set_avail_meta_area_count v c : c_brk (set_avail_meta_area_count v c) = c_brk c. Proof. reflexivity. Qed.
Lemma c_secret_set_meta_alloc_shift v c : c_secret (set_meta_alloc_shift v c) = c_secret c. Proof. reflexivity. Qed.
Lemma c_init_done_set_meta_alloc_shift v c : c_init_done (set_meta_alloc_shift v c) = c_init_done c. Proof. reflexivity. Qed.
Lemma c_mmap_counter_set_meta_alloc_shift v c : c_mmap_counter (set_meta_alloc_shift v c) = c_mmap_counter c. Proof. reflexivity. Qed.
Lemma c_free_meta_head_set_meta_alloc_shift v c : c_free_meta_head (set_meta_alloc_shift v c) = c_free_meta_head c. Proof. reflexivity. Qed.
Lemma c_avail_meta_set_meta_alloc_shift v c : c_avail_meta (set_meta_alloc_shift v c) = c_avail_meta c. Proof. reflexivity. Qed.
Lemma c_avail_meta_count_set_meta_alloc_shift v c : c_avail_meta_count (set_meta_alloc_shift v c) = c_avail_meta_count c. Proof. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_meta_alloc_shift v c : c_avail_meta_area_count (set_meta_alloc_shift v c) = c_avail_meta_area_count c. Proof. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_meta_alloc_shift v c : c_meta_alloc_shift (set_meta_alloc_shift v c) = v. Proof. reflexivity. Qed.
Lemma c_meta_area_head_set_meta_alloc_shift v c : c_meta_area_head (set_meta_alloc_shift v c) = c_meta_area_head c. Proof. reflexivity. Qed.
Lemma c_meta_area_tail_set_meta_alloc_shift v c : c_meta_area_tail (set_meta_alloc_shift v c) = c_meta_area_tail c. Proof. reflexivity. Qed.
Lemma c_avail_meta_areas_set_meta_alloc_shift v c : c_avail_meta_areas (set_meta_alloc_shift v c) = c_avail_meta_areas c. Proof. reflexivity. Qed.
Lemma c_active_set_meta_alloc_shift v c : c_active (set_meta_alloc_shift v c) = c_active c. Proof. reflexivity. Qed.
Lemma c_usage_set_meta_alloc_shift v c : c_usage (set_meta_alloc_shift v c) = c_usage c. Proof. reflexivity. Qed.
Lemma c_unmap_seq_set_meta_alloc_shift v c : c_unmap_seq (set_meta_alloc_shift v c) = c_unmap_seq c. Proof. reflexivity. Qed.
Lemma c_bounces_set_meta_alloc_shift v c : c_bounces (set_meta_alloc_shift v c) = c_bounces c. Proof. reflexivity. Qed.
Lemma c_seq_set_meta_alloc_shift v c : c_seq (set_meta_alloc_shift v c) = c_seq c. Proof. reflexivity. Qed.
Lemma c_brk_set_meta_alloc_shift v c : c_brk (set_meta_alloc_shift v c) = c_brk c. Proof. reflexivity. Qed.
Lemma c_secret_set_meta_area_head v c : c_secret (set_meta_area_head v c) = c_secret c. Proof. reflexivity. Qed.
Lemma c_init_done_set_meta_area_head v c : c_init_done (set_meta_area_head v c) = c_init_done c. Proof. reflexivity. Qed.
Lemma c_mmap_counter_set_meta_area_head v c : c_mmap_counter (set_meta_area_head v c) = c_mmap_counter c. Proof. reflexivity. Qed.
Lemma c_free_meta_head_set_meta_area_head v c : c_free_meta_head (set_meta_area_head v c) = c_free_meta_head c. Proof. reflexivity. Qed.
Lemma c_avail_meta_set_meta_area_head v c : c_avail_meta (set_meta_area_head v c) = c_avail_meta c. Proof. reflexivity. Qed.
Lemma c_avail_meta_count_set_meta_area_head v c : c_avail_meta_count (set_meta_area_head v c) = c_avail_meta_count c. Proof. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_meta_area_head v c : c_avail_meta_area_count (set_meta_area_head v c) = c_avail_meta_area_count c. Proof. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_meta_area_head v c : c_meta_alloc_shift (set_meta_area_head v c) = c_meta_alloc_shift c. Proof. reflexivity. Qed.
Lemma c_meta_area_head_set_meta_area_head v c : c_meta_area_head (set_meta_area_head v c) = v. Proof. reflexivity. Qed.
Lemma c_meta_area_tail_set_meta_area_head v c : c_meta_area_tail (set_meta_area_head v c) = c_meta_area_tail c. Proof. reflexivity. Qed.
Lemma c_avail_meta_areas_set_meta_area_head v c : c_avail_meta_areas (set_meta_area_head v c) = c_avail_meta_areas c. Proof. reflexivity. Qed.
Lemma c_active_set_meta_area_head v c : c_active (set_meta_area_head v c) = c_active c. Proof. reflexivity. Qed.
Lemma c_usage_set_meta_area_head v c : c_usage (set_meta_area_head v c) = c_usage c. Proof. reflexivity. Qed.
Lemma c_unmap_seq_set_meta_area_head v c : c_unmap_seq (set_meta_area_head v c) = c_unmap_seq c. Proof. reflexivity. Qed.
Lemma c_bounces_set_meta_area_head v c : c_bounces (set_meta_area_head v c) = c_bounces c. Proof. reflexivity. Qed.
Lemma c_seq_set_meta_area_head v c : c_seq (set_meta_area_head v c) = c_seq c. Proof. reflexivity. Qed.
Lemma c_brk_set_meta_area_head v c : c_brk (set_meta_area_head v c) = c_brk c. Proof. reflexivity. Qed.
Lemma c_secret_set_meta_area_tail v c : c_secret (set_meta_area_tail v c) = c_secret c. Proof. reflexivity. Qed.
Lemma c_init_done_set_meta_area_tail v c : c_init_done (set_meta_area_tail v c) = c_init_done c. Proof. reflexivity. Qed.
Lemma c_mmap_counter_set_meta_area_tail v c : c_mmap_counter (set_meta_area_tail v c) = c_mmap_counter c. Proof. reflexivity. Qed.
Lemma c_free_meta_head_set_meta_area_tail v c : c_free_meta_head (set_meta_area_tail v c) = c_free_meta_head c. Proof. reflexivity. Qed.
Lemma c_avail_meta_set_meta_area_tail v c : c_avail_meta (set_meta_area_tail v c) = c_avail_meta c. Proof. reflexivity. Qed.
Lemma c_avail_meta_count_set_meta_area_tail v c : c_avail_meta_count (set_meta_area_tail v c) = c_avail_meta_count c. Proof. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_meta_area_tail v c : c_avail_meta_area_count (set_meta_area_tail v c) = c_avail_meta_area_count c. Proof. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_meta_area_tail v c : c_meta_alloc_shift (set_meta_area_tail v c) = c_meta_alloc_shift c. Proof. reflexivity. Qed.
Lemma c_meta_area_head_set_meta_area_tail v c : c_meta_area_head (set_meta_area_tail v c) = c_meta_area_head c. Proof. reflexivity. Qed.
Lemma c_meta_area_tail_set_meta_area_tail v c : c_meta_area_tail (set_meta_area_tail v c) = v. Proof. reflexivity. Qed.
Lemma c_avail_meta_areas_set_meta_area_tail v c : c_avail_meta_areas (set_meta_area_tail v c) = c_avail_meta_areas c. Proof. reflexivity. Qed.
Lemma c_active_set_meta_area_tail v c : c_active (set_meta_area_tail v c) = c_active c. Proof. reflexivity. Qed.
Lemma c_usage_set_meta_area_tail v c : c_usage (set_meta_area_tail v c) = c_usage c. Proof. reflexivity. Qed.
Lemma c_unmap_seq_set_meta_area_tail v c : c_unmap_seq (set_meta_area_tail v c) = c_unmap_seq c. Proof. reflexivity. Qed.
Lemma c_bounces_set_meta_area_tail v c : c_bounces (set_meta_area_tail v c) = c_bounces c. Proof. reflexivity. Qed.
Lemma c_seq_set_meta_area_tail v c : c_seq (set_meta_area_tail v c) = c_seq c. Proof. reflexivity. Qed.
Lemma c_brk_set_meta_area_tail v c : c_brk (set_meta_area_tail v c) = c_brk c. Proof. reflexivity. Qed.
Lemma c_secret_set_avail_meta_areas v c : c_secret (set_avail_meta_areas v c) = c_secret c. Proof. reflexivity. Qed.
Lemma c_init_done_set_avail_meta_areas v c : c_init_done (set_avail_meta_areas v c) = c_init_done c. Proof. reflexivity. Qed.
Lemma c_mmap_counter_set_avail_meta_areas v c : c_mmap_counter (set_avail_meta_areas v c) = c_mmap_counter c. Proof. reflexivity. Qed.
Lemma c_free_meta_head_set_avail_meta_areas v c : c_free_meta_head (set_avail_meta_areas v c) = c_free_meta_head c. Proof. reflexivity. Qed.
Lemma c_avail_meta_set_avail_meta_areas v c : c_avail_meta (set_avail_meta_areas v c) = c_avail_meta c. Proof. reflexivity. Qed.
Lemma c_avail_meta_count_set_avail_meta_areas v c : c_avail_meta_count (set_avail_meta_areas v c) = c_avail_meta_count c. Proof. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_avail_meta_areas v c : c_avail_meta_area_count (set_avail_meta_areas v c) = c_avail_meta_area_count c. Proof. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_avail_meta_areas v c : c_meta_alloc_shift (set_avail_meta_areas v c) = c_meta_alloc_shift c. Proof. reflexivity. Qed.
Lemma c_meta_area_head_set_avail_meta_areas v c : c_meta_area_head (set_avail_meta_areas v c) = c_meta_area_head c. Proof. reflexivity. Qed.
Lemma c_meta_area_tail_set_avail_meta_areas v c : c_meta_area_tail (set_avail_meta_areas v c) = c_meta_area_tail c. Proof. reflexivity. Qed.
Lemma c_avail_meta_areas_set_avail_meta_areas v c : c_avail_meta_areas (set_avail_meta_areas v c) = v. Proof. reflexivity. Qed.
Lemma c_active_set_avail_meta_areas v c : c_active (set_avail_meta_areas v c) = c_active c. Proof. reflexivity. Qed.
Lemma c_usage_set_avail_meta_areas v c : c_usage (set_avail_meta_areas v c) = c_usage c. Proof. reflexivity. Qed.
Lemma c_unmap_seq_set_avail_meta_areas v c : c_unmap_seq (set_avail_meta_areas v c) = c_unmap_seq c. Proof. reflexivity. Qed.
Lemma c_bounces_set_avail_meta_areas v c : c_bounces (set_avail_meta_areas v c) = c_bounces c. Proof. reflexivity. Qed.
Lemma c_seq_set_avail_meta_areas v c : c_seq (set_avail_meta_areas v c) = c_seq c. Proof. reflexivity. Qed.
Lemma c_brk_set_avail_meta_areas v c : c_brk (set_avail_meta_areas v c) = c_brk c. Proof. reflexivity. Qed.
Lemma c_secret_set_active_map v c : c_secret (set_active_map v c) = c_secret c. Proof. reflexivity. Qed.
Lemma c_init_done_set_active_map v c : c_init_done (set_active_map v c) = c_init_done c. Proof. reflexivity. Qed.
Lemma c_mmap_counter_set_active_map v c : c_mmap_counter (set_active_map v c) = c_mmap_counter c. Proof. reflexivity. Qed.
Lemma c_free_meta_head_set_active_map v c : c_free_meta_head (set_active_map v c) = c_free_meta_head c. Proof. reflexivity. Qed.
Lemma c_avail_meta_set_active_map v c : c_avail_meta (set_active_map v c) = c_avail_meta c. Proof. reflexivity. Qed.
Lemma c_avail_meta_count_set_active_map v c : c_avail_meta_count (set_active_map v c) = c_avail_meta_count c. Proof. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_active_map v c : c_avail_meta_area_count (set_active_map v c) = c_avail_meta_area_count c. Proof. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_active_map v c : c_meta_alloc_shift (set_active_map v c) = c_meta_alloc_shift c. Proof. reflexivity. Qed.
Lemma c_meta_area_head_set_active_map v c : c_meta_area_head (set_active_map v c) = c_meta_area_head c. Proof. reflexivity. Qed.
Lemma c_meta_area_tail_set_active_map v c : c_meta_area_tail (set_active_map v c) = c_meta_area_tail c. Proof. reflexivity. Qed.
Lemma c_avail_meta_areas_set_active_map v c : c_avail_meta_areas (set_active_map v c) = c_avail_meta_areas c. Proof. reflexivity. Qed.
Lemma c_active_set_active_map v c : c_active (set_active_map v c) = v. Proof. reflexivity. Qed.
Lemma c_usage_set_active_map v c : c_usage (set_active_map v c) = c_usage c. Proof. reflexivity. Qed.
Lemma c_unmap_seq_set_active_map v c : c_unmap_seq (set_active_map v c) = c_unmap_seq c. Proof. reflexivity. Qed.
Lemma c_bounces_set_active_map v c : c_bounces (set_active_map v c) = c_bounces c. Proof. reflexivity. Qed.
Lemma c_seq_set_active_map v c : c_seq (set_active_map v c) = c_seq c. Proof. reflexivity. Qed.
Lemma c_brk_set_active_map v c : c_brk (set_active_map v c) = c_brk c. Proof. reflexivity. Qed.
Lemma c_secret_set_usage_map v c : c_secret (set_usage_map v c) = c_secret c. Proof. reflexivity. Qed.
Lemma c_init_done_set_usage_map v c : c_init_done (set_usage_map v c) = c_init_done c. Proof. reflexivity. Qed.
Lemma c_mmap_counter_set_usage_map v c : c_mmap_counter (set_usage_map v c) = c_mmap_counter c. Proof. reflexivity. Qed.
Lemma c_free_meta_head_set_usage_map v c : c_free_meta_head (set_usage_map v c) = c_free_meta_head c. Proof. reflexivity. Qed.
Lemma c_avail_meta_set_usage_map v c : c_avail_meta (set_usage_map v c) = c_avail_meta c. Proof. reflexivity. Qed.
Lemma c_avail_meta_count_set_usage_map v c : c_avail_meta_count (set_usage_map v c) = c_avail_meta_count c. Proof. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_usage_map v c : c_avail_meta_area_count (set_usage_map v c) = c_avail_meta_area_count c. Proof. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_usage_map v c : c_meta_alloc_shift (set_usage_map v c) = c_meta_alloc_shift c. Proof. reflexivity. Qed.
Lemma c_meta_area_head_set_usage_map v c : c_meta_area_head (set_usage_map v c) = c_meta_area_head c. Proof. reflexivity. Qed.
Lemma c_meta_area_tail_set_usage_map v c : c_meta_area_tail (set_usage_map v c) = c_meta_area_tail c. Proof. reflexivity. Qed.
Lemma c_avail_meta_areas_set_usage_map v c : c_avail_meta_areas (set_usage_map v c) = c_avail_meta_areas c. Proof. reflexivity. Qed.
Lemma c_active_set_usage_map v c : c_active (set_usage_map v c) = c_active c. Proof. reflexivity. Qed.
Lemma c_usage_set_usage_map v c : c_usage (set_usage_map v c) = v. Proof. reflexivity. Qed.
Lemma c_unmap_seq_set_usage_map v c : c_unmap_seq (set_usage_map v c) = c_unmap_seq c. Proof. reflexivity. Qed.
Lemma c_bounces_set_usage_map v c : c_bounces (set_usage_map v c) = c_bounces c. Proof. reflexivity. Qed.
Lemma c_seq_set_usage_map v c : c_seq (set_usage_map v c) = c_seq c. Proof. reflexivity. Qed.
Lemma c_brk_set_usage_map v c : c_brk (set_usage_map v c) = c_brk c. Proof. reflexivity. Qed.
Lemma c_secret_set_unmap_seq_map v c : c_secret (set_unmap_seq_map v c) = c_secret c. Proof. reflexivity. Qed.
Lemma c_init_done_set_unmap_seq_map v c : c_init_done (set_unmap_seq_map v c) = c_init_done c. Proof. reflexivity. Qed.
Lemma c_mmap_counter_set_unmap_seq_map v c : c_mmap_counter (set_unmap_seq_map v c) = c_mmap_counter c. Proof. reflexivity. Qed.
Lemma c_free_meta_head_set_unmap_seq_map v c : c_free_meta_head (set_unmap_seq_map v c) = c_free_meta_head c. Proof. reflexivity. Qed.
Lemma c_avail_meta_set_unmap_seq_map v c : c_avail_meta (set_unmap_seq_map v c) = c_avail_meta c. Proof. reflexivity. Qed.
Lemma c_avail_meta_count_set_unmap_seq_map v c : c_avail_meta_count (set_unmap_seq_map v c) = c_avail_meta_count c. Proof. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_unmap_seq_map v c : c_avail_meta_area_count (set_unmap_seq_map v c) = c_avail_meta_area_count c. Proof. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_unmap_seq_map v c : c_meta_alloc_shift (set_unmap_seq_map v c) = c_meta_alloc_shift c. Proof. reflexivity. Qed.
Lemma c_meta_area_head_set_unmap_seq_map v c : c_meta_area_head (set_unmap_seq_map v c) = c_meta_area_head c. Proof. reflexivity. Qed.
Lemma c_meta_area_tail_set_unmap_seq_map v c : c_meta_area_tail (set_unmap_seq_map v c) = c_meta_area_tail c. Proof. reflexivity. Qed.
Lemma c_avail_meta_areas_set_unmap_seq_map v c : c_avail_meta_areas (set_unmap_seq_map v c) = c_avail_meta_areas c. Proof. reflexivity. Qed.
Lemma c_active_set_unmap_seq_map v c : c_active (set_unmap_seq_map v c) = c_active c. Proof. reflexivity. Qed.
Lemma c_usage_set_unmap_seq_map v c : c_usage (set_unmap_seq_map v c) = c_usage c. Proof. reflexivity. Qed.
Lemma c_unmap_seq_set_unmap_seq_map v c : c_unmap_seq (set_unmap_seq_map v c) = v. Proof. reflexivity. Qed.
Lemma c_bounces_set_unmap_seq_map v c : c_bounces (set_unmap_seq_map v c) = c_bounces c. Proof. reflexivity. Qed.
Lemma c_seq_set_unmap_seq_map v c : c_seq (set_unmap_seq_map v c) = c_seq c. Proof. reflexivity. Qed.
Lemma c_brk_set_unmap_seq_map v c : c_brk (set_unmap_seq_map v c) = c_brk c. Proof. reflexivity. Qed.
Lemma c_secret_set_bounces_map v c : c_secret (set_bounces_map v c) = c_secret c. Proof. reflexivity. Qed.
Lemma c_init_done_set_bounces_map v c : c_init_done (set_bounces_map v c) = c_init_done c. Proof. reflexivity. Qed.
Lemma c_mmap_counter_set_bounces_map v c : c_mmap_counter (set_bounces_map v c) = c_mmap_counter c. Proof. reflexivity. Qed.
Lemma c_free_meta_head_set_bounces_map v c : c_free_meta_head (set_bounces_map v c) = c_free_meta_head c. Proof. reflexivity. Qed.
Lemma c_avail_meta_set_bounces_map v c : c_avail_meta (set_bounces_map v c) = c_avail_meta c. Proof. reflexivity. Qed.
Lemma c_avail_meta_count_set_bounces_map v c : c_avail_meta_count (set_bounces_map v c) = c_avail_meta_count c. Proof. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_bounces_map v c : c_avail_meta_area_count (set_bounces_map v c) = c_avail_meta_area_count c. Proof. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_bounces_map v c : c_meta_alloc_shift (set_bounces_map v c) = c_meta_alloc_shift c. Proof. reflexivity. Qed.
Lemma c_meta_area_head_set_bounces_map v c : c_meta_area_head (set_bounces_map v c) = c_meta_area_head c. Proof. reflexivity. Qed.
Lemma c_meta_area_tail_set_bounces_map v c : c_meta_area_tail (set_bounces_map v c) = c_meta_area_tail c. Proof. reflexivity. Qed.
Lemma c_avail_meta_areas_set_bounces_map v c : c_avail_meta_areas (set_bounces_map v c) = c_avail_meta_areas c. Proof. reflexivity. Qed.
Lemma c_active_set_bounces_map v c : c_active (set_bounces_map v c) = c_active c. Proof. reflexivity. Qed.
Lemma c_usage_set_bounces_map v c : c_usage (set_bounces_map v c) = c_usage c. Proof. reflexivity. Qed.
Lemma c_unmap_seq_set_bounces_map v c : c_unmap_seq (set_bounces_map v c) = c_unmap_seq c. Proof. reflexivity. Qed.
Lemma c_bounces_set_bounces_map v c : c_bounces (set_bounces_map v c) = v. Proof. reflexivity. Qed.
Lemma c_seq_set_bounces_map v c : c_seq (set_bounces_map v c) = c_seq c. Proof. reflexivity. Qed.
Lemma c_brk_set_bounces_map v c : c_brk (set_bounces_map v c) = c_brk c. Proof. reflexivity. Qed.
Lemma c_secret_set_seq v c : c_secret (set_seq v c) = c_secret c. Proof. reflexivity. Qed.
Lemma c_init_done_set_seq v c : c_init_done (set_seq v c) = c_init_done c. Proof. reflexivity. Qed.
Lemma c_mmap_counter_set_seq v c : c_mmap_counter (set_seq v c) = c_mmap_counter c. Proof. reflexivity. Qed.
Lemma c_free_meta_head_set_seq v c : c_free_meta_head (set_seq v c) = c_free_meta_head c. Proof. reflexivity. Qed.
Lemma c_avail_meta_set_seq v c : c_avail_meta (set_seq v c) = c_avail_meta c. Proof. reflexivity. Qed.
Lemma c_avail_meta_count_set_seq v c : c_avail_meta_count (set_seq v c) = c_avail_meta_count c. Proof. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_seq v c : c_avail_meta_area_count (set_seq v c) = c_avail_meta_area_count c. Proof. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_seq v c : c_meta_alloc_shift (set_seq v c) = c_meta_alloc_shift c. Proof. reflexivity. Qed.
Lemma c_meta_area_head_set_seq v c : c_meta_area_head (set_seq v c) = c_meta_area_head c. Proof. reflexivity. Qed.
Lemma c_meta_area_tail_set_seq v c : c_meta_area_tail (set_seq v c) = c_meta_area_tail c. Proof. reflexivity. Qed.
Lemma c_avail_meta_areas_set_seq v c : c_avail_meta_areas (set_seq v c) = c_avail_meta_areas c. Proof. reflexivity. Qed.
Lemma c_active_set_seq v c : c_active (set_seq v c) = c_active c. Proof. reflexivity. Qed.
Lemma c_usage_set_seq v c : c_usage (set_seq v c) = c_usage c. Proof. reflexivity. Qed.
Lemma c_unmap_seq_set_seq v c : c_unmap_seq (set_seq v c) = c_unmap_seq c. Proof. reflexivity. Qed.
Lemma c_bounces_set_seq v c : c_bounces (set_seq v c) = c_bounces c. Proof. reflexivity. Qed.
Lemma c_seq_set_seq v c : c_seq (set_seq v c) = v. Proof. reflexivity. Qed.
Lemma c_brk_set_seq v c : c_brk (set_seq v c) = c_brk c. Proof. reflexivity. Qed.
Lemma c_secret_set_brk v c : c_secret (set_brk v c) = c_secret c. Proof. reflexivity. Qed.
Lemma c_init_done_set_brk v c : c_init_done (set_brk v c) = c_init_done c. Proof. reflexivity. Qed.
Lemma c_mmap_counter_set_brk v c : c_mmap_counter (set_brk v c) = c_mmap_counter c. Proof. reflexivity. Qed.
Lemma c_free_meta_head_set_brk v c : c_free_meta_head (set_brk v c) = c_free_meta_head c. Proof. reflexivity. Qed.
Lemma c_avail_meta_set_brk v c : c_avail_meta (set_brk v c) = c_avail_meta c. Proof. reflexivity. Qed.
Lemma c_avail_meta_count_set_brk v c : c_avail_meta_count (set_brk v c) = c_avail_meta_count c. Proof. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_brk v c : c_avail_meta_area_count (set_brk v c) = c_avail_meta_area_count c. Proof. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_brk v c : c_meta_alloc_shift (set_brk v c) = c_meta_alloc_shift c. Proof. reflexivity. Qed.
Lemma c_meta_area_head_set_brk v c : c_meta_area_head (set_brk v c) = c_meta_area_head c. Proof. reflexivity. Qed.
Lemma c_meta_area_tail_set_brk v c : c_meta_area_tail (set_brk v c) = c_meta_area_tail c. Proof. reflexivity. Qed.
Lemma c_avail_meta_areas_set_brk v c : c_avail_meta_areas (set_brk v c) = c_avail_meta_areas c. Proof. reflexivity. Qed.
Lemma c_active_set_brk v c : c_active (set_brk v c) = c_active c. Proof. reflexivity. Qed.
Lemma c_usage_set_brk v c : c_usage (set_brk v c) = c_usage c. Proof. reflexivity. Qed.
Lemma c_unmap_seq_set_brk v c : c_unmap_seq (set_brk v c) = c_unmap_seq c. Proof. reflexivity. Qed.
Lemma c_bounces_set_brk v c : c_bounces (set_brk v c) = c_bounces c. Proof. reflexivity. Qed.
Lemma c_seq_set_brk v c : c_seq (set_brk v c) = c_seq c. Proof. reflexivity. Qed.
Lemma c_brk_set_brk v c : c_brk (set_brk v c) = v. Proof. reflexivity. Qed.
#[export] Hint Rewrite s_ctx_upd_ctx s_regions_upd_ctx s_shadow_upd_ctx s_next_rid_upd_ctx s_metas_upd_ctx s_areas_upd_ctx s_groups_upd_ctx s_slots_upd_ctx s_tick_upd_ctx s_secret_upd_ctx s_reserved_upd_ctx s_atop_upd_ctx s_ctx_set_regions s_regions_set_regions s_shadow_set_regions s_next_rid_set_regions s_metas_set_regions s_areas_set_regions s_groups_set_regions s_slots_set_regions s_tick_set_regions s_secret_set_regions s_reserved_set_regions s_atop_set_regions s_ctx_set_shadow s_regions_set_shadow s_shadow_set_shadow s_next_rid_set_shadow s_metas_set_shadow s_areas_set_shadow s_groups_set_shadow s_slots_set_shadow s_tick_set_shadow s_secret_set_shadow s_reserved_set_shadow s_atop_set_shadow s_ctx_set_next_rid s_regions_set_next_rid s_shadow_set_next_rid s_next_rid_set_next_rid s_metas_set_next_rid s_areas_set_next_rid s_groups_set_next_rid s_slots_set_next_rid s_tick_set_next_rid s_secret_set_next_rid s_reserved_set_next_rid s_atop_set_next_rid s_ctx_set_metas s_regions_set_metas s_shadow_set_metas s_next_rid_set_metas s_metas_set_metas s_areas_set_metas s_groups_set_metas s_slots_set_metas s_tick_set_metas s_secret_set_metas s_reserved_set_metas s_atop_set_metas s_ctx_set_areas s_regions_set_areas s_shadow_set_areas s_next_rid_set_areas s_metas_set_areas s_areas_set_areas s_groups_set_areas s_slots_set_areas s_tick_set_areas s_secret_set_areas s_reserved_set_areas s_atop_set_areas s_ctx_set_groups s_regions_set_groups s_shadow_set_groups s_next_rid_set_groups s_metas_set_groups s_areas_set_groups s_groups_set_groups s_slots_set_groups s_tick_set_groups s_secret_set_groups s_reserved_set_groups s_atop_set_groups s_ctx_set_slots s_regions_set_slots s_shadow_set_slots s_next_rid_set_slots s_metas_set_slots s_areas_set_slots s_groups_set_slots s_slots_set_slots s_tick_set_slots s_secret_set_slots s_reserved_set_slots s_atop_set_slots s_ctx_set_tick s_regions_set_tick s_shadow_set_tick s_next_rid_set_tick s_metas_set_tick s_areas_set_tick s_groups_set_tick s_slots_set_tick s_tick_set_tick s_secret_set_tick s_reserved_set_tick s_atop_set_tick c_secret_set_secret c_init_done_set_secret c_mmap_counter_set_secret c_free_meta_head_set_secret c_avail_meta_set_secret c_avail_meta_count_set_secret c_avail_meta_area_count_set_secret c_meta_alloc_shift_set_secret c_meta_area_head_set_secret c_meta_area_tail_set_secret c_avail_meta_areas_set_secret c_active_set_secret c_usage_set_secret c_unmap_seq_set_secret c_bounces_set_secret c_seq_set_secret c_brk_set_secret c_secret_set_init_done c_init_done_set_init_done c_mmap_counter_set_init_done c_free_meta_head_set_init_done c_avail_meta_set_init_done c_avail_meta_count_set_init_done c_avail_meta_area_count_set_init_done c_meta_alloc_shift_set_init_done c_meta_area_head_set_init_done c_meta_area_tail_set_init_done c_avail_meta_areas_set_init_done c_active_set_init_done c_usage_set_init_done c_unmap_seq_set_init_done c_bounces_set_init_done c_seq_set_init_done c_brk_set_init_done c_secret_set_mmap_counter c_init_done_set_mmap_counter c_mmap_counter_set_mmap_counter c_free_meta_head_set_mmap_counter c_avail_meta_set_mmap_counter c_avail_meta_count_set_mmap_counter c_avail_meta_area_count_set_mmap_counter c_meta_alloc_shift_set_mmap_counter c_meta_area_head_set_mmap_counter c_meta_area_tail_set_mmap_counter c_avail_meta_areas_set_mmap_counter c_active_set_mmap_counter c_usage_set_mmap_counter c_unmap_seq_set_mmap_counter c_bounces_set_mmap_counter c_seq_set_mmap_counter c_brk_set_mmap_counter c_secret_set_free_meta_head c_init_done_set_free_meta_head c_mmap_counter_set_free_meta_head c_free_meta_head_set_free_meta_head c_avail_meta_set_free_meta_head c_avail_meta_count_set_free_meta_head c_avail_meta_area_count_set_free_meta_head c_meta_alloc_shift_set_free_meta_head c_meta_area_head_set_free_meta_head c_meta_area_tail_set_free_meta_head c_avail_meta_areas_set_free_meta_head c_active_set_free_meta_head c_usage_set_free_meta_head c_unmap_seq_set_free_meta_head c_bounces_set_free_meta_head c_seq_set_free_meta_head c_brk_set_free_meta_head c_secret_set_avail_meta c_init_done_set_avail_meta c_mmap_counter_set_avail_meta c_free_meta_head_set_avail_meta c_avail_meta_set_avail_meta c_avail_meta_count_set_avail_meta c_avail_meta_area_count_set_avail_meta c_meta_alloc_shift_set_avail_meta c_meta_area_head_set_avail_meta c_meta_area_tail_set_avail_meta c_avail_meta_areas_set_avail_meta c_active_set_avail_meta c_usage_set_avail_meta c_unmap_seq_set_avail_meta c_bounces_set_avail_meta c_seq_set_avail_meta c_brk_set_avail_meta c_secret_set_avail_meta_count c_init_done_set_avail_meta_count c_mmap_counter_set_avail_meta_count c_free_meta_head_set_avail_meta_count c_avail_meta_set_avail_meta_count c_avail_meta_count_set_avail_meta_count c_avail_meta_area_count_set_avail_meta_count c_meta_alloc_shift_set_avail_meta_count c_meta_area_head_set_avail_meta_count c_meta_area_tail_set_avail_meta_count c_avail_meta_areas_set_avail_meta_count c_active_set_avail_meta_count c_usage_set_avail_meta_count c_unmap_seq_set_avail_meta_count c_bounces_set_avail_meta_count c_seq_set_avail_meta_count c_brk_set_avail_meta_count c_secret_set_avail_meta_area_count c_init_done_set_avail_meta_area_count c_mmap_counter_set_avail_meta_area_count c_free_meta_head_set_avail_meta_area_count c_avail_meta_set_avail_meta_area_count c_avail_meta_count_set_avail_meta_area_count c_avail_meta_area_count_set_avail_meta_area_count c_meta_alloc_shift_set_avail_meta_area_count c_meta_area_head_set_avail_meta_area_count c_meta_area_tail_set_avail_meta_area_count c_avail_meta_areas_set_avail_meta_area_count c_active_set_avail_meta_area_count c_usage_set_avail_meta_area_count c_unmap_seq_set_avail_meta_area_count c_bounces_set_avail_meta_area_count c_seq_set_avail_meta_area_count c_brk_set_avail_meta_area_count c_secret_set_meta_alloc_shift c_init_done_set_meta_alloc_shift c_mmap_counter_set_meta_alloc_shift c_free_meta_head_set_meta_alloc_shift c_avail_meta_set_meta_alloc_shift c_avail_meta_count_set_meta_alloc_shift c_avail_meta_area_count_set_meta_alloc_shift c_meta_alloc_shift_set_meta_alloc_shift c_meta_area_head_set_meta_alloc_shift c_meta_area_tail_set_meta_alloc_shift c_avail_meta_areas_set_meta_alloc_shift c_active_set_meta_alloc_shift c_usage_set_meta_alloc_shift c_unmap_seq_set_meta_alloc_shift c_bounces_set_meta_alloc_shift c_seq_set_meta_alloc_shift c_brk_set_meta_alloc_shift c_secret_set_meta_area_head c_init_done_set_meta_area_head c_mmap_counter_set_meta_area_head c_free_meta_head_set_meta_area_head c_avail_meta_set_meta_area_head c_avail_meta_count_set_meta_area_head c_avail_meta_area_count_set_meta_area_head c_meta_alloc_shift_set_meta_area_head c_meta_area_head_set_meta_area_head c_meta_area_tail_set_meta_area_head c_avail_meta_areas_set_meta_area_head c_active_set_meta_area_head c_usage_set_meta_area_head c_unmap_seq_set_meta_area_head c_bounces_set_meta_area_head c_seq_set_meta_area_head c_brk_set_meta_area_head c_secret_set_meta_area_tail c_init_done_set_meta_area_tail c_mmap_counter_set_meta_area_tail c_free_meta_head_set_meta_area_tail c_avail_meta_set_meta_area_tail c_avail_meta_count_set_meta_area_tail c_avail_meta_area_count_set_meta_area_tail c_meta_alloc_shift_set_meta_area_tail c_meta_area_head_set_meta_area_tail c_meta_area_tail_set_meta_area_tail c_avail_meta_areas_set_meta_area_tail c_active_set_meta_area_tail c_usage_set_meta_area_tail c_unmap_seq_set_meta_area_tail c_bounces_set_meta_area_tail c_seq_set_meta_area_tail c_brk_set_meta_area_tail c_secret_set_avail_meta_areas c_init_done_set_avail_meta_areas c_mmap_counter_set_avail_meta_areas c_free_meta_head_set_avail_meta_areas c_avail_meta_set_avail_meta_areas c_avail_meta_count_set_avail_meta_areas c_avail_meta_area_count_set_avail_meta_areas c_meta_alloc_shift_set_avail_meta_areas c_meta_area_head_set_avail_meta_areas c_meta_area_tail_set_avail_meta_areas c_avail_meta_areas_set_avail_meta_areas c_active_set_avail_meta_areas c_usage_set_avail_meta_areas c_unmap_seq_set_avail_meta_areas c_bounces_set_avail_meta_areas c_seq_set_avail_meta_areas c_brk_set_avail_meta_areas c_secret_set_active_map c_init_done_set_active_map c_mmap_counter_set_active_map c_free_meta_head_set_active_map c_avail_meta_set_active_map c_avail_meta_count_set_active_map c_avail_meta_area_count_set_active_map c_meta_alloc_shift_set_active_map c_meta_area_head_set_active_map c_meta_area_tail_set_active_map c_avail_meta_areas_set_active_map c_active_set_active_map c_usage_set_active_map c_unmap_seq_set_active_map c_bounces_set_active_map c_seq_set_active_map c_brk_set_active_map c_secret_set_usage_map c_init_done_set_usage_map c_mmap_counter_set_usage_map c_free_meta_head_set_usage_map c_avail_meta_set_usage_map c_avail_meta_count_set_usage_map c_avail_meta_area_count_set_usage_map c_meta_alloc_shift_set_usage_map c_meta_area_head_set_usage_map c_meta_area_tail_set_usage_map c_avail_meta_areas_set_usage_map c_active_set_usage_map c_usage_set_usage_map c_unmap_seq_set_usage_map c_bounces_set_usage_map c_seq_set_usage_map c_brk_set_usage_map c_secret_set_unmap_seq_map c_init_done_set_unmap_seq_map c_mmap_counter_set_unmap_seq_map c_free_meta_head_set_unmap_seq_map c_avail_meta_set_unmap_seq_map c_avail_meta_count_set_unmap_seq_map c_avail_meta_area_count_set_unmap_seq_map c_meta_alloc_shift_set_unmap_seq_map c_meta_area_head_set_unmap_seq_map c_meta_area_tail_set_unmap_seq_map c_avail_meta_areas_set_unmap_seq_map c_active_set_unmap_seq_map c_usage_set_unmap_seq_map c_unmap_seq_set_unmap_seq_map c_bounces_set_unmap_seq_map c_seq_set_unmap_seq_map c_brk_set_unmap_seq_map c_secret_set_bounces_map c_init_done_set_bounces_map c_mmap_counter_set_bounces_map c_free_meta_head_set_bounces_map c_avail_meta_set_bounces_map c_avail_meta_count_set_bounces_map c_avail_meta_area_count_set_bounces_map c_meta_alloc_shift_set_bounces_map c_meta_area_head_set_bounces_map c_meta_area_tail_set_bounces_map c_avail_meta_areas_set_bounces_map c_active_set_bounces_map c_usage_set_bounces_map c_unmap_seq_set_bounces_map c_bounces_set_bounces_map c_seq_set_bounces_map c_brk_set_bounces_map c_secret_set_seq c_init_done_set_seq c_mmap_counter_set_seq c_free_meta_head_set_seq c_avail_meta_set_seq c_avail_meta_count_set_seq c_avail_meta_area_count_set_seq c_meta_alloc_shift_set_seq c_meta_area_head_set_seq c_meta_area_tail_set_seq c_avail_meta_areas_set_seq c_active_set_seq c_usage_set_seq c_unmap_seq_set_seq c_bounces_set_seq c_seq_set_seq c_brk_set_seq c_secret_set_brk c_init_done_set_brk c_mmap_counter_set_brk c_free_meta_head_set_brk c_avail_meta_set_brk c_avail_meta_count_set_brk c_avail_meta_area_count_set_brk c_meta_alloc_shift_set_brk c_meta_area_head_set_brk c_meta_area_tail_set_brk c_avail_meta_areas_set_brk c_active_set_brk c_usage_set_brk c_unmap_seq_set_brk c_bounces_set_brk c_seq_set_brk c_brk_set_brk : mst.
Lemma s_regions_set_active sc v st : s_regions (set_active sc v st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_shadow_set_active sc v st : s_shadow (set_active sc v st) = s_shadow st. Proof. reflexivity. Qed.
Lemma s_next_rid_set_active sc v st : s_next_rid (set_active sc v st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_metas_set_active sc v st : s_metas (set_active sc v st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_set_active sc v st : s_areas (set_active sc v st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_set_active sc v st : s_groups (set_active sc v st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_slots_set_active sc v st : s_slots (set_active sc v st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_tick_set_active sc v st : s_tick (set_active sc v st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_set_active sc v st : s_secret (set_active sc v st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_set_active sc v st : s_reserved (set_active sc v st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_atop_set_active sc v st : s_atop (set_active sc v st) = s_atop st. Proof. reflexivity. Qed.
Lemma s_regions_set_usage sc v st : s_regions (set_usage sc v st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_shadow_set_usage sc v st : s_shadow (set_usage sc v st) = s_shadow st. Proof. reflexivity. Qed.
Lemma s_next_rid_set_usage sc v st : s_next_rid (set_usage sc v st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_metas_set_usage sc v st : s_metas (set_usage sc v st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_set_usage sc v st : s_areas (set_usage sc v st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_set_usage sc v st : s_groups (set_usage sc v st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_slots_set_usage sc v st : s_slots (set_usage sc v st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_tick_set_usage sc v st : s_tick (set_usage sc v st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_set_usage sc v st : s_secret (set_usage sc v st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_set_usage sc v st : s_reserved (set_usage sc v st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_atop_set_usage sc v st : s_atop (set_usage sc v st) = s_atop st. Proof. reflexivity. Qed.
Lemma s_regions_set_bounce i v st : s_regions (set_bounce i v st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_shadow_set_bounce i v st : s_shadow (set_bounce i v st) = s_shadow st. Proof. reflexivity. Qed.
Lemma s_next_rid_set_bounce i v st : s_next_rid (set_bounce i v st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_metas_set_bounce i v st : s_metas (set_bounce i v st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_set_bounce i v st : s_areas (set_bounce i v st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_set_bounce i v st : s_groups (set_bounce i v st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_slots_set_bounce i v st : s_slots (set_bounce i v st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_tick_set_bounce i v st : s_tick (set_bounce i v st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_set_bounce i v st : s_secret (set_bounce i v st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_set_bounce i v st : s_reserved (set_bounce i v st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_atop_set_bounce i v st : s_atop (set_bounce i v st) = s_atop st. Proof. reflexivity. Qed.
Lemma s_ctx_put_meta m r st : s_ctx (put_meta m r st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_regions_put_meta m r st : s_regions (put_meta m r st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_shadow_put_meta m r st : s_shadow (put_meta m r st) = s_shadow st. Proof. reflexivity. Qed.
Lemma s_next_rid_put_meta m r st : s_next_rid (put_meta m r st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_areas_put_meta m r st : s_areas (put_meta m r st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_put_meta m r st : s_groups (put_meta m r st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_slots_put_meta m r st : s_slots (put_meta m r st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_tick_put_meta m r st : s_tick (put_meta m r st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_put_meta m r st : s_secret (put_meta m r st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_put_meta m r st : s_reserved (put_meta m r st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_atop_put_meta m r st : s_atop (put_meta m r st) = s_atop st. Proof. reflexivity. Qed.
Lemma s_ctx_upd_meta m f st : s_ctx (upd_meta m f st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_regions_upd_meta m f st : s_regions (upd_meta m f st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_shadow_upd_meta m f st : s_shadow (upd_meta m f st) = s_shadow st. Proof. reflexivity. Qed.
Lemma s_next_rid_upd_meta m f st : s_next_rid (upd_meta m f st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_areas_upd_meta m f st : s_areas (upd_meta m f st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_upd_meta m f st : s_groups (upd_meta m f st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_slots_upd_meta m f st : s_slots (upd_meta m f st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_tick_upd_meta m f st : s_tick (upd_meta m f st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_upd_meta m f st : s_secret (upd_meta m f st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_upd_meta m f st : s_reserved (upd_meta m f st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_atop_upd_meta m f st : s_atop (upd_meta m f st) = s_atop st. Proof. reflexivity. Qed.
Lemma s_ctx_put_group g mo ai st : s_ctx (put_group g mo ai st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_regions_put_group g mo ai st : s_regions (put_group g mo ai st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_shadow_put_group g mo ai st : s_shadow (put_group g mo ai st) = s_shadow st. Proof. reflexivity. Qed.
Lemma s_next_rid_put_group g mo ai st : s_next_rid (put_group g mo ai st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_metas_put_group g mo ai st : s_metas (put_group g mo ai st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_put_group g mo ai st : s_areas (put_group g mo ai st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_slots_put_group g mo ai st : s_slots (put_group g mo ai st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_tick_put_group g mo ai st : s_tick (put_group g mo ai st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_put_group g mo ai st : s_secret (put_group g mo ai st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_put_group g mo ai st : s_reserved (put_group g mo ai st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_atop_put_group g mo ai st : s_atop (put_group g mo ai st) = s_atop st. Proof. reflexivity. Qed.
Lemma s_ctx_del_group g st : s_ctx (del_group g st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_regions_del_group g st : s_regions (del_group g st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_shadow_del_group g st : s_shadow (del_group g st) = s_shadow st. Proof. reflexivity. Qed.
Lemma s_next_rid_del_group g st : s_next_rid (del_group g st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_metas_del_group g st : s_metas (del_group g st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_del_group g st : s_areas (del_group g st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_slots_del_group g st : s_slots (del_group g st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_tick_del_group g st : s_tick (del_group g st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_del_group g st : s_secret (del_group g st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_del_group g st : s_reserved (del_group g st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_atop_del_group g st : s_atop (del_group g st) = s_atop st. Proof. reflexivity. Qed.
Lemma s_ctx_set_group_active_idx g ai st : s_ctx (set_group_active_idx g ai st) = s_ctx st. Proof. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
Lemma s_regions_set_group_active_idx g ai st : s_regions (set_group_active_idx g ai st) = s_regions st. Proof. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
Lemma s_shadow_set_group_active_idx g ai st : s_shadow (set_group_active_idx g ai st) = s_shadow st. Proof. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
Lemma s_next_rid_set_group_active_idx g ai st : s_next_rid (set_group_active_idx g ai st) = s_next_rid st. Proof. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
Lemma s_metas_set_group_active_idx g ai st : s_metas (set_group_active_idx g ai st) = s_metas st. Proof. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
Lemma s_areas_set_group_active_idx g ai st : s_areas (set_group_active_idx g ai st) = s_areas st. Proof. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
Lemma s_slots_set_group_active_idx g ai st : s_slots (set_group_active_idx g ai st) = s_slots st. Proof. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
Lemma s_tick_set_group_active_idx g ai st : s_tick (set_group_active_idx g ai st) = s_tick st. Proof. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
Lemma s_secret_set_group_active_idx g ai st : s_secret (set_group_active_idx g ai st) = s_secret st. Proof. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
Lemma s_reserved_set_group_active_idx g ai st : s_reserved (set_group_active_idx g ai st) = s_reserved st. Proof. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
Lemma s_atop_set_group_active_idx g ai st : s_atop (set_group_active_idx g ai st) = s_atop st. Proof. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
Lemma s_ctx_drop_region rid st : s_ctx (drop_region rid st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_next_rid_drop_region rid st : s_next_rid (drop_region rid st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_metas_drop_region rid st : s_metas (drop_region rid st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_drop_region rid st : s_areas (drop_region rid st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_drop_region rid st : s_groups (drop_region rid st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_slots_drop_region rid st : s_slots (drop_region rid st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_tick_drop_region rid st : s_tick (drop_region rid st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_drop_region rid st : s_secret (drop_region rid st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_drop_region rid st : s_reserved (drop_region rid st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_atop_drop_region rid st : s_atop (drop_region rid st) = s_atop st. Proof. reflexivity. Qed.
Lemma s_ctx_upd_region rid f st : s_ctx (upd_region rid f st) = s_ctx st. Proof. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
Lemma s_shadow_upd_region rid f st : s_shadow (upd_region rid f st) = s_shadow st. Proof. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
Lemma s_next_rid_upd_region rid f st : s_next_rid (upd_region rid f st) = s_next_rid st. Proof. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
Lemma s_metas_upd_region rid f st : s_metas (upd_region rid f st) = s_metas st. Proof. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
Lemma s_areas_upd_region rid f st : s_areas (upd_region rid f st) = s_areas st. Proof. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
Lemma s_groups_upd_region rid f st : s_groups (upd_region rid f st) = s_groups st. Proof. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
Lemma s_slots_upd_region rid f st : s_slots (upd_region rid f st) = s_slots st. Proof. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
Lemma s_tick_upd_region rid f st : s_tick (upd_region rid f st) = s_tick st. Proof. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
Lemma s_secret_upd_region rid f st : s_secret (upd_region rid f st) = s_secret st. Proof. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
Lemma s_reserved_upd_region rid f st : s_reserved (upd_region rid f st) = s_reserved st. Proof. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
Lemma s_atop_upd_region rid f st : s_atop (upd_region rid f st) = s_atop st. Proof. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
Lemma s_ctx_add_slots m p stride cnt st : s_ctx (add_slots m p stride cnt st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_regions_add_slots m p stride cnt st : s_regions (add_slots m p stride cnt st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_shadow_add_slots m p stride cnt st : s_shadow (add_slots m p stride cnt st) = s_shadow st. Proof. reflexivity. Qed.
Lemma s_next_rid_add_slots m p stride cnt st : s_next_rid (add_slots m p stride cnt st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_metas_add_slots m p stride cnt st : s_metas (add_slots m p stride cnt st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_add_slots m p stride cnt st : s_areas (add_slots m p stride cnt st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_add_slots m p stride cnt st : s_groups (add_slots m p stride cnt st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_tick_add_slots m p stride cnt st : s_tick (add_slots m p stride cnt st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_add_slots m p stride cnt st : s_secret (add_slots m p stride cnt st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_add_slots m p stride cnt st : s_reserved (add_slots m p stride cnt st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_atop_add_slots m p stride cnt st : s_atop (add_slots m p stride cnt st) = s_atop st. Proof. reflexivity. Qed.
Lemma s_ctx_del_slots p stride cnt st : s_ctx (del_slots p stride cnt st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_regions_del_slots p stride cnt st : s_regions (del_slots p stride cnt st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_shadow_del_slots p stride cnt st : s_shadow (del_slots p stride cnt st) = s_shadow st. Proof. reflexivity. Qed.
Lemma s_next_rid_del_slots p stride cnt st : s_next_rid (del_slots p stride cnt st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_metas_del_slots p stride cnt st : s_metas (del_slots p stride cnt st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_del_slots p stride cnt st : s_areas (del_slots p stride cnt st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_del_slots p stride cnt st : s_groups (del_slots p stride cnt st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_tick_del_slots p stride cnt st : s_tick (del_slots p stride cnt st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_del_slots p stride cnt st : s_secret (del_slots p stride cnt st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_del_slots p stride cnt st : s_reserved (del_slots p stride cnt st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_atop_del_slots p stride cnt st : s_atop (del_slots p stride cnt st) = s_atop st. Proof. reflexivity. Qed.
Lemma s_ctx_upd_shadow rid f st : s_ctx (upd_shadow rid f st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_regions_upd_shadow rid f st : s_regions (upd_shadow rid f st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_next_rid_upd_shadow rid f st : s_next_rid (upd_shadow rid f st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_metas_upd_shadow rid f st : s_metas (upd_shadow rid f st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_upd_shadow rid f st : s_areas (upd_shadow rid f st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_upd_shadow rid f st : s_groups (upd_shadow rid f st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_slots_upd_shadow rid f st : s_slots (upd_shadow rid f st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_tick_upd_shadow rid f st : s_tick (upd_shadow rid f st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_upd_shadow rid f st : s_secret (upd_shadow rid f st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_upd_shadow rid f st : s_reserved (upd_shadow rid f st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_atop_upd_shadow rid f st : s_atop (upd_shadow rid f st) = s_atop st. Proof. reflexivity. Qed.
Lemma s_ctx_wr8 p v st : s_ctx (wr8 p v st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_regions_wr8 p v st : s_regions (wr8 p v st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_next_rid_wr8 p v st : s_next_rid (wr8 p v st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_metas_wr8 p v st : s_metas (wr8 p v st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_wr8 p v st : s_areas (wr8 p v st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_wr8 p v st : s_groups (wr8 p v st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_slots_wr8 p v st : s_slots (wr8 p v st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_tick_wr8 p v st : s_tick (wr8 p v st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_wr8 p v st : s_secret (wr8 p v st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_wr8 p v st : s_reserved (wr8 p v st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_atop_wr8 p v st : s_atop (wr8 p v st) = s_atop st. Proof. reflexivity. Qed.
Lemma s_ctx_wr16 p v st : s_ctx (wr16 p v st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_regions_wr16 p v st : s_regions (wr16 p v st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_next_rid_wr16 p v st : s_next_rid (wr16 p v st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_metas_wr16 p v st : s_metas (wr16 p v st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_wr16 p v st : s_areas (wr16 p v st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_wr16 p v st : s_groups (wr16 p v st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_slots_wr16 p v st : s_slots (wr16 p v st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_tick_wr16 p v st : s_tick (wr16 p v st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_wr16 p v st : s_secret (wr16 p v st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_wr16 p v st : s_reserved (wr16 p v st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_atop_wr16 p v st : s_atop (wr16 p v st) = s_atop st. Proof. reflexivity. Qed.
Lemma s_ctx_wr32 p v st : s_ctx (wr32 p v st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_regions_wr32 p v st : s_regions (wr32 p v st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_next_rid_wr32 p v st : s_next_rid (wr32 p v st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_metas_wr32 p v st : s_metas (wr32 p v st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_wr32 p v st : s_areas (wr32 p v st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_wr32 p v st : s_groups (wr32 p v st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_slots_wr32 p v st : s_slots (wr32 p v st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_tick_wr32 p v st : s_tick (wr32 p v st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_wr32 p v st : s_secret (wr32 p v st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_wr32 p v st : s_reserved (wr32 p v st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_atop_wr32 p v st : s_atop (wr32 p v st) = s_atop st. Proof. reflexivity. Qed.
Lemma s_ctx_havoc p n st : s_ctx (havoc p n st) = s_ctx st. Proof. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
Lemma s_regions_havoc p n st : s_regions (havoc p n st) = s_regions st. Proof. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
Lemma s_next_rid_havoc p n st : s_next_rid (havoc p n st) = s_next_rid st. Proof. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
Lemma s_metas_havoc p n st : s_metas (havoc p n st) = s_metas st. Proof. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
Lemma s_areas_havoc p n st : s_areas (havoc p n st) = s_areas st. Proof. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
Lemma s_groups_havoc p n st : s_groups (havoc p n st) = s_groups st. Proof. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
Lemma s_slots_havoc p n st : s_slots (havoc p n st) = s_slots st. Proof. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
Lemma s_tick_havoc p n st : s_tick (havoc p n st) = s_tick st. Proof. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
Lemma s_secret_havoc p n st : s_secret (havoc p n st) = s_secret st. Proof. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
Lemma s_reserved_havoc p n st : s_reserved (havoc p n st) = s_reserved st. Proof. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
Lemma s_atop_havoc p n st : s_atop (havoc p n st) = s_atop st. Proof. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
Lemma s_ctx_hdr_havoc b st : s_ctx (hdr_havoc b st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_regions_hdr_havoc b st : s_regions (hdr_havoc b st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_next_rid_hdr_havoc b st : s_next_rid (hdr_havoc b st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_metas_hdr_havoc b st : s_metas (hdr_havoc b st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_hdr_havoc b st : s_areas (hdr_havoc b st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_hdr_havoc b st : s_groups (hdr_havoc b st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_slots_hdr_havoc b st : s_slots (hdr_havoc b st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_tick_hdr_havoc b st : s_tick (hdr_havoc b st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_hdr_havoc b st : s_secret (hdr_havoc b st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_hdr_havoc b st : s_reserved (hdr_havoc b st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_atop_hdr_havoc b st : s_atop (hdr_havoc b st) = s_atop st. Proof. reflexivity. Qed.
Lemma s_regions_step_seq  st : s_regions (step_seq st) = s_regions st. Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma s_shadow_step_seq  st : s_shadow (step_seq st) = s_shadow st. Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma s_next_rid_step_seq  st : s_next_rid (step_seq st) = s_next_rid st. Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma s_metas_step_seq  st : s_metas (step_seq st) = s_metas st. Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma s_areas_step_seq  st : s_areas (step_seq st) = s_areas st. Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma s_groups_step_seq  st : s_groups (step_seq st) = s_groups st. Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma s_slots_step_seq  st : s_slots (step_seq st) = s_slots st. Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma s_tick_step_seq  st : s_tick (step_seq st) = s_tick st. Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma s_secret_step_seq  st : s_secret (step_seq st) = s_secret st. Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma s_reserved_step_seq  st : s_reserved (step_seq st) = s_reserved st. Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma s_atop_step_seq  st : s_atop (step_seq st) = s_atop st. Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma s_regions_record_seq sc st : s_regions (record_seq sc st) = s_regions st. Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma s_shadow_record_seq sc st : s_shadow (record_seq sc st) = s_shadow st. Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma s_next_rid_record_seq sc st : s_next_rid (record_seq sc st) = s_next_rid st. Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma s_metas_record_seq sc st : s_metas (record_seq sc st) = s_metas st. Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma s_areas_record_seq sc st : s_areas (record_seq sc st) = s_areas st. Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma s_groups_record_seq sc st : s_groups (record_seq sc st) = s_groups st. Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma s_slots_record_seq sc st : s_slots (record_seq sc st) = s_slots st. Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma s_tick_record_seq sc st : s_tick (record_seq sc st) = s_tick st. Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma s_secret_record_seq sc st : s_secret (record_seq sc st) = s_secret st. Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma s_reserved_record_seq sc st : s_reserved (record_seq sc st) = s_reserved st. Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma s_atop_record_seq sc st : s_atop (record_seq sc st) = s_atop st. Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma s_regions_account_bounce sc st : s_regions (account_bounce sc st) = s_regions st. Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma s_shadow_account_bounce sc st : s_shadow (account_bounce sc st) = s_shadow st. Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma s_next_rid_account_bounce sc st : s_next_rid (account_bounce sc st) = s_next_rid st. Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma s_metas_account_bounce sc st : s_metas (account_bounce sc st) = s_metas st. Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma s_areas_account_bounce sc st : s_areas (account_bounce sc st) = s_areas st. Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma s_groups_account_bounce sc st : s_groups (account_bounce sc st) = s_groups st. Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma s_slots_account_bounce sc st : s_slots (account_bounce sc st) = s_slots st. Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma s_tick_account_bounce sc st : s_tick (account_bounce sc st) = s_tick st. Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma s_secret_account_bounce sc st : s_secret (account_bounce sc st) = s_secret st. Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma s_reserved_account_bounce sc st : s_reserved (account_bounce sc st) = s_reserved st. Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma s_atop_account_bounce sc st : s_atop (account_bounce sc st) = s_atop st. Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma s_regions_decay_bounces sc st : s_regions (decay_bounces sc st) = s_regions st. Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma s_shadow_decay_bounces sc st : s_shadow (decay_bounces sc st) = s_shadow st. Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma s_next_rid_decay_bounces sc st : s_next_rid (decay_bounces sc st) = s_next_rid st. Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma s_metas_decay_bounces sc st : s_metas (decay_bounces sc st) = s_metas st. Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma s_areas_decay_bounces sc st : s_areas (decay_bounces sc st) = s_areas st. Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma s_groups_decay_bounces sc st : s_groups (decay_bounces sc st) = s_groups st. Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma s_slots_decay_bounces sc st : s_slots (decay_bounces sc st) = s_slots st. Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma s_tick_decay_bounces sc st : s_tick (decay_bounces sc st) = s_tick st. Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma s_secret_decay_bounces sc st : s_secret (decay_bounces sc st) = s_secret st. Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma s_reserved_decay_bounces sc st : s_reserved (decay_bounces sc st) = s_reserved st. Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma s_atop_decay_bounces sc st : s_atop (decay_bounces sc st) = s_atop st. Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma s_regions_set_head h v st : s_regions (set_head h v st) = s_regions st. Proof. destruct h; reflexivity. Qed.
Lemma s_shadow_set_head h v st : s_shadow (set_head h v st) = s_shadow st. Proof. destruct h; reflexivity. Qed.
Lemma s_next_rid_set_head h v st : s_next_rid (set_head h v st) = s_next_rid st. Proof. destruct h; reflexivity. Qed.
Lemma s_metas_set_head h v st : s_metas (set_head h v st) = s_metas st. Proof. destruct h; reflexivity. Qed.
Lemma s_areas_set_head h v st : s_areas (set_head h v st) = s_areas st. Proof. destruct h; reflexivity. Qed.
Lemma s_groups_set_head h v st : s_groups (set_head h v st) = s_groups st. Proof. destruct h; reflexivity. Qed.
Lemma s_slots_set_head h v st : s_slots (set_head h v st) = s_slots st. Proof. destruct h; reflexivity. Qed.
Lemma s_tick_set_head h v st : s_tick (set_head h v st) = s_tick st. Proof. destruct h; reflexivity. Qed.
Lemma s_secret_set_head h v st : s_secret (set_head h v st) = s_secret st. Proof. destruct h; reflexivity. Qed.
Lemma s_reserved_set_head h v st : s_reserved (set_head h v st) = s_reserved st. Proof. destruct h; reflexivity. Qed.
Lemma s_atop_set_head h v st : s_atop (set_head h v st) = s_atop st. Proof. destruct h; reflexivity. Qed.
Lemma s_regions_dequeue h m st : s_regions (dequeue h m st) = s_regions st. Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma s_shadow_dequeue h m st : s_shadow (dequeue h m st) = s_shadow st. Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma s_next_rid_dequeue h m st : s_next_rid (dequeue h m st) = s_next_rid st. Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma s_areas_dequeue h m st : s_areas (dequeue h m st) = s_areas st. Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma s_groups_dequeue h m st : s_groups (dequeue h m st) = s_groups st. Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma s_slots_dequeue h m st : s_slots (dequeue h m st) = s_slots st. Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma s_tick_dequeue h m st : s_tick (dequeue h m st) = s_tick st. Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma s_secret_dequeue h m st : s_secret (dequeue h m st) = s_secret st. Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma s_reserved_dequeue h m st : s_reserved (dequeue h m st) = s_reserved st. Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma s_atop_dequeue h m st : s_atop (dequeue h m st) = s_atop st. Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma s_ctx_set_size p e n b3 st : s_ctx (set_size p e n b3 st) = s_ctx st. Proof. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma s_regions_set_size p e n b3 st : s_regions (set_size p e n b3 st) = s_regions st. Proof. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma s_next_rid_set_size p e n b3 st : s_next_rid (set_size p e n b3 st) = s_next_rid st. Proof. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma s_metas_set_size p e n b3 st : s_metas (set_size p e n b3 st) = s_metas st. Proof. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma s_areas_set_size p e n b3 st : s_areas (set_size p e n b3 st) = s_areas st. Proof. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma s_groups_set_size p e n b3 st : s_groups (set_size p e n b3 st) = s_groups st. Proof. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma s_slots_set_size p e n b3 st : s_slots (set_size p e n b3 st) = s_slots st. Proof. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma s_tick_set_size p e n b3 st : s_tick (set_size p e n b3 st) = s_tick st. Proof. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma s_secret_set_size p e n b3 st : s_secret (set_size p e n b3 st) = s_secret st. Proof. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma s_reserved_set_size p e n b3 st : s_reserved (set_size p e n b3 st) = s_reserved st. Proof. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma s_atop_set_size p e n b3 st : s_atop (set_size p e n b3 st) = s_atop st. Proof. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma c_secret_set_active sc v st : c_secret (s_ctx (set_active sc v st)) = c_secret (s_ctx st). Proof. reflexivity. Qed.
Lemma c_init_done_set_active sc v st : c_init_done (s_ctx (set_active sc v st)) = c_init_done (s_ctx st). Proof. reflexivity. Qed.
Lemma c_mmap_counter_set_active sc v st : c_mmap_counter (s_ctx (set_active sc v st)) = c_mmap_counter (s_ctx st). Proof. reflexivity. Qed.
Lemma c_free_meta_head_set_active sc v st : c_free_meta_head (s_ctx (set_active sc v st)) = c_free_meta_head (s_ctx st). Proof. reflexivity. Qed.
Lemma c_avail_meta_set_active sc v st : c_avail_meta (s_ctx (set_active sc v st)) = c_avail_meta (s_ctx st). Proof. reflexivity. Qed.
Lemma c_avail_meta_count_set_active sc v st : c_avail_meta_count (s_ctx (set_active sc v st)) = c_avail_meta_count (s_ctx st). Proof. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_active sc v st : c_avail_meta_area_count (s_ctx (set_active sc v st)) = c_avail_meta_area_count (s_ctx st). Proof. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_active sc v st : c_meta_alloc_shift (s_ctx (set_active sc v st)) = c_meta_alloc_shift (s_ctx st). Proof. reflexivity. Qed.
Lemma c_meta_area_head_set_active sc v st : c_meta_area_head (s_ctx (set_active sc v st)) = c_meta_area_head (s_ctx st). Proof. reflexivity. Qed.
Lemma c_meta_area_tail_set_active sc v st : c_meta_area_tail (s_ctx (set_active sc v st)) = c_meta_area_tail (s_ctx st). Proof. reflexivity. Qed.
Lemma c_avail_meta_areas_set_active sc v st : c_avail_meta_areas (s_ctx (set_active sc v st)) = c_avail_meta_areas (s_ctx st). Proof. reflexivity. Qed.
Lemma c_usage_set_active sc v st : c_usage (s_ctx (set_active sc v st)) = c_usage (s_ctx st). Proof. reflexivity. Qed.
Lemma c_unmap_seq_set_active sc v st : c_unmap_seq (s_ctx (set_active sc v st)) = c_unmap_seq (s_ctx st). Proof. reflexivity. Qed.
Lemma c_bounces_set_active sc v st : c_bounces (s_ctx (set_active sc v st)) = c_bounces (s_ctx st). Proof. reflexivity. Qed.
Lemma c_seq_set_active sc v st : c_seq (s_ctx (set_active sc v st)) = c_seq (s_ctx st). Proof. reflexivity. Qed.
Lemma c_brk_set_active sc v st : c_brk (s_ctx (set_active sc v st)) = c_brk (s_ctx st). Proof. reflexivity. Qed.
Lemma c_secret_set_usage sc v st : c_secret (s_ctx (set_usage sc v st)) = c_secret (s_ctx st). Proof. reflexivity. Qed.
Lemma c_init_done_set_usage sc v st : c_init_done (s_ctx (set_usage sc v st)) = c_init_done (s_ctx st). Proof. reflexivity. Qed.
Lemma c_mmap_counter_set_usage sc v st : c_mmap_counter (s_ctx (set_usage sc v st)) = c_mmap_counter (s_ctx st). Proof. reflexivity. Qed.
Lemma c_free_meta_head_set_usage sc v st : c_free_meta_head (s_ctx (set_usage sc v st)) = c_free_meta_head (s_ctx st). Proof. reflexivity. Qed.
Lemma c_avail_meta_set_usage sc v st : c_avail_meta (s_ctx (set_usage sc v st)) = c_avail_meta (s_ctx st). Proof. reflexivity. Qed.
Lemma c_avail_meta_count_set_usage sc v st : c_avail_meta_count (s_ctx (set_usage sc v st)) = c_avail_meta_count (s_ctx st). Proof. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_usage sc v st : c_avail_meta_area_count (s_ctx (set_usage sc v st)) = c_avail_meta_area_count (s_ctx st). Proof. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_usage sc v st : c_meta_alloc_shift (s_ctx (set_usage sc v st)) = c_meta_alloc_shift (s_ctx st). Proof. reflexivity. Qed.
Lemma c_meta_area_head_set_usage sc v st : c_meta_area_head (s_ctx (set_usage sc v st)) = c_meta_area_head (s_ctx st). Proof. reflexivity. Qed.
Lemma c_meta_area_tail_set_usage sc v st : c_meta_area_tail (s_ctx (set_usage sc v st)) = c_meta_area_tail (s_ctx st). Proof. reflexivity. Qed.
Lemma c_avail_meta_areas_set_usage sc v st : c_avail_meta_areas (s_ctx (set_usage sc v st)) = c_avail_meta_areas (s_ctx st). Proof. reflexivity. Qed.
Lemma c_active_set_usage sc v st : c_active (s_ctx (set_usage sc v st)) = c_active (s_ctx st). Proof. reflexivity. Qed.
Lemma c_unmap_seq_set_usage sc v st : c_unmap_seq (s_ctx (set_usage sc v st)) = c_unmap_seq (s_ctx st). Proof. reflexivity. Qed.
Lemma c_bounces_set_usage sc v st : c_bounces (s_ctx (set_usage sc v st)) = c_bounces (s_ctx st). Proof. reflexivity. Qed.
Lemma c_seq_set_usage sc v st : c_seq (s_ctx (set_usage sc v st)) = c_seq (s_ctx st). Proof. reflexivity. Qed.
Lemma c_brk_set_usage sc v st : c_brk (s_ctx (set_usage sc v st)) = c_brk (s_ctx st). Proof. reflexivity. Qed.
Lemma c_secret_set_bounce i v st : c_secret (s_ctx (set_bounce i v st)) = c_secret (s_ctx st). Proof. reflexivity. Qed.
Lemma c_init_done_set_bounce i v st : c_init_done (s_ctx (set_bounce i v st)) = c_init_done (s_ctx st). Proof. reflexivity. Qed.
Lemma c_mmap_counter_set_bounce i v st : c_mmap_counter (s_ctx (set_bounce i v st)) = c_mmap_counter (s_ctx st). Proof. reflexivity. Qed.
Lemma c_free_meta_head_set_bounce i v st : c_free_meta_head (s_ctx (set_bounce i v st)) = c_free_meta_head (s_ctx st). Proof. reflexivity. Qed.
Lemma c_avail_meta_set_bounce i v st : c_avail_meta (s_ctx (set_bounce i v st)) = c_avail_meta (s_ctx st). Proof. reflexivity. Qed.
Lemma c_avail_meta_count_set_bounce i v st : c_avail_meta_count (s_ctx (set_bounce i v st)) = c_avail_meta_count (s_ctx st). Proof. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_bounce i v st : c_avail_meta_area_count (s_ctx (set_bounce i v st)) = c_avail_meta_area_count (s_ctx st). Proof. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_bounce i v st : c_meta_alloc_shift (s_ctx (set_bounce i v st)) = c_meta_alloc_shift (s_ctx st). Proof. reflexivity. Qed.
Lemma c_meta_area_head_set_bounce i v st : c_meta_area_head (s_ctx (set_bounce i v st)) = c_meta_area_head (s_ctx st). Proof. reflexivity. Qed.
Lemma c_meta_area_tail_set_bounce i v st : c_meta_area_tail (s_ctx (set_bounce i v st)) = c_meta_area_tail (s_ctx st). Proof. reflexivity. Qed.
Lemma c_avail_meta_areas_set_bounce i v st : c_avail_meta_areas (s_ctx (set_bounce i v st)) = c_avail_meta_areas (s_ctx st). Proof. reflexivity. Qed.
Lemma c_active_set_bounce i v st : c_active (s_ctx (set_bounce i v st)) = c_active (s_ctx st). Proof. reflexivity. Qed.
Lemma c_usage_set_bounce i v st : c_usage (s_ctx (set_bounce i v st)) = c_usage (s_ctx st). Proof. reflexivity. Qed.
Lemma c_unmap_seq_set_bounce i v st : c_unmap_seq (s_ctx (set_bounce i v st)) = c_unmap_seq (s_ctx st). Proof. reflexivity. Qed.
Lemma c_seq_set_bounce i v st : c_seq (s_ctx (set_bounce i v st)) = c_seq (s_ctx st). Proof. reflexivity. Qed.
Lemma c_brk_set_bounce i v st : c_brk (s_ctx (set_bounce i v st)) = c_brk (s_ctx st). Proof. reflexivity. Qed.
Lemma c_secret_step_seq  st : c_secret (s_ctx (step_seq st)) = c_secret (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_init_done_step_seq  st : c_init_done (s_ctx (step_seq st)) = c_init_done (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_mmap_counter_step_seq  st : c_mmap_counter (s_ctx (step_seq st)) = c_mmap_counter (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_free_meta_head_step_seq  st : c_free_meta_head (s_ctx (step_seq st)) = c_free_meta_head (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_avail_meta_step_seq  st : c_avail_meta (s_ctx (step_seq st)) = c_avail_meta (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_avail_meta_count_step_seq  st : c_avail_meta_count (s_ctx (step_seq st)) = c_avail_meta_count (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_avail_meta_area_count_step_seq  st : c_avail_meta_area_count (s_ctx (step_seq st)) = c_avail_meta_area_count (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_meta_alloc_shift_step_seq  st : c_meta_alloc_shift (s_ctx (step_seq st)) = c_meta_alloc_shift (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_meta_area_head_step_seq  st : c_meta_area_head (s_ctx (step_seq st)) = c_meta_area_head (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_meta_area_tail_step_seq  st : c_meta_area_tail (s_ctx (step_seq st)) = c_meta_area_tail (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_avail_meta_areas_step_seq  st : c_avail_meta_areas (s_ctx (step_seq st)) = c_avail_meta_areas (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_active_step_seq  st : c_active (s_ctx (step_seq st)) = c_active (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_usage_step_seq  st : c_usage (s_ctx (step_seq st)) = c_usage (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_bounces_step_seq  st : c_bounces (s_ctx (step_seq st)) = c_bounces (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_brk_step_seq  st : c_brk (s_ctx (step_seq st)) = c_brk (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_secret_record_seq sc st : c_secret (s_ctx (record_seq sc st)) = c_secret (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_init_done_record_seq sc st : c_init_done (s_ctx (record_seq sc st)) = c_init_done (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_mmap_counter_record_seq sc st : c_mmap_counter (s_ctx (record_seq sc st)) = c_mmap_counter (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_free_meta_head_record_seq sc st : c_free_meta_head (s_ctx (record_seq sc st)) = c_free_meta_head (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_avail_meta_record_seq sc st : c_avail_meta (s_ctx (record_seq sc st)) = c_avail_meta (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_avail_meta_count_record_seq sc st : c_avail_meta_count (s_ctx (record_seq sc st)) = c_avail_meta_count (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_avail_meta_area_count_record_seq sc st : c_avail_meta_area_count (s_ctx (record_seq sc st)) = c_avail_meta_area_count (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_meta_alloc_shift_record_seq sc st : c_meta_alloc_shift (s_ctx (record_seq sc st)) = c_meta_alloc_shift (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_meta_area_head_record_seq sc st : c_meta_area_head (s_ctx (record_seq sc st)) = c_meta_area_head (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_meta_area_tail_record_seq sc st : c_meta_area_tail (s_ctx (record_seq sc st)) = c_meta_area_tail (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_avail_meta_areas_record_seq sc st : c_avail_meta_areas (s_ctx (record_seq sc st)) = c_avail_meta_areas (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_active_record_seq sc st : c_active (s_ctx (record_seq sc st)) = c_active (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_usage_record_seq sc st : c_usage (s_ctx (record_seq sc st)) = c_usage (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_bounces_record_seq sc st : c_bounces (s_ctx (record_seq sc st)) = c_bounces (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_seq_record_seq sc st : c_seq (s_ctx (record_seq sc st)) = c_seq (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_brk_record_seq sc st : c_brk (s_ctx (record_seq sc st)) = c_brk (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_secret_account_bounce sc st : c_secret (s_ctx (account_bounce sc st)) = c_secret (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_init_done_account_bounce sc st : c_init_done (s_ctx (account_bounce sc st)) = c_init_done (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_mmap_counter_account_bounce sc st : c_mmap_counter (s_ctx (account_bounce sc st)) = c_mmap_counter (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_free_meta_head_account_bounce sc st : c_free_meta_head (s_ctx (account_bounce sc st)) = c_free_meta_head (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_avail_meta_account_bounce sc st : c_avail_meta (s_ctx (account_bounce sc st)) = c_avail_meta (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_avail_meta_count_account_bounce sc st : c_avail_meta_count (s_ctx (account_bounce sc st)) = c_avail_meta_count (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_avail_meta_area_count_account_bounce sc st : c_avail_meta_area_count (s_ctx (account_bounce sc st)) = c_avail_meta_area_count (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_meta_alloc_shift_account_bounce sc st : c_meta_alloc_shift (s_ctx (account_bounce sc st)) = c_meta_alloc_shift (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_meta_area_head_account_bounce sc st : c_meta_area_head (s_ctx (account_bounce sc st)) = c_meta_area_head (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_meta_area_tail_account_bounce sc st : c_meta_area_tail (s_ctx (account_bounce sc st)) = c_meta_area_tail (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_avail_meta_areas_account_bounce sc st : c_avail_meta_areas (s_ctx (account_bounce sc st)) = c_avail_meta_areas (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_active_account_bounce sc st : c_active (s_ctx (account_bounce sc st)) = c_active (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_usage_account_bounce sc st : c_usage (s_ctx (account_bounce sc st)) = c_usage (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_unmap_seq_account_bounce sc st : c_unmap_seq (s_ctx (account_bounce sc st)) = c_unmap_seq (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_seq_account_bounce sc st : c_seq (s_ctx (account_bounce sc st)) = c_seq (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_brk_account_bounce sc st : c_brk (s_ctx (account_bounce sc st)) = c_brk (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_secret_decay_bounces sc st : c_secret (s_ctx (decay_bounces sc st)) = c_secret (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_init_done_decay_bounces sc st : c_init_done (s_ctx (decay_bounces sc st)) = c_init_done (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_mmap_counter_decay_bounces sc st : c_mmap_counter (s_ctx (decay_bounces sc st)) = c_mmap_counter (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_free_meta_head_decay_bounces sc st : c_free_meta_head (s_ctx (decay_bounces sc st)) = c_free_meta_head (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_avail_meta_decay_bounces sc st : c_avail_meta (s_ctx (decay_bounces sc st)) = c_avail_meta (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_avail_meta_count_decay_bounces sc st : c_avail_meta_count (s_ctx (decay_bounces sc st)) = c_avail_meta_count (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_avail_meta_area_count_decay_bounces sc st : c_avail_meta_area_count (s_ctx (decay_bounces sc st)) = c_avail_meta_area_count (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_meta_alloc_shift_decay_bounces sc st : c_meta_alloc_shift (s_ctx (decay_bounces sc st)) = c_meta_alloc_shift (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_meta_area_head_decay_bounces sc st : c_meta_area_head (s_ctx (decay_bounces sc st)) = c_meta_area_head (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_meta_area_tail_decay_bounces sc st : c_meta_area_tail (s_ctx (decay_bounces sc st)) = c_meta_area_tail (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_avail_meta_areas_decay_bounces sc st : c_avail_meta_areas (s_ctx (decay_bounces sc st)) = c_avail_meta_areas (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_active_decay_bounces sc st : c_active (s_ctx (decay_bounces sc st)) = c_active (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_usage_decay_bounces sc st : c_usage (s_ctx (decay_bounces sc st)) = c_usage (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_unmap_seq_decay_bounces sc st : c_unmap_seq (s_ctx (decay_bounces sc st)) = c_unmap_seq (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_seq_decay_bounces sc st : c_seq (s_ctx (decay_bounces sc st)) = c_seq (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_brk_decay_bounces sc st : c_brk (s_ctx (decay_bounces sc st)) = c_brk (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_secret_dequeue h m st : c_secret (s_ctx (dequeue h m st)) = c_secret (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_init_done_dequeue h m st : c_init_done (s_ctx (dequeue h m st)) = c_init_done (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_mmap_counter_dequeue h m st : c_mmap_counter (s_ctx (dequeue h m st)) = c_mmap_counter (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_avail_meta_dequeue h m st : c_avail_meta (s_ctx (dequeue h m st)) = c_avail_meta (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_avail_meta_count_dequeue h m st : c_avail_meta_count (s_ctx (dequeue h m st)) = c_avail_meta_count (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_avail_meta_area_count_dequeue h m st : c_avail_meta_area_count (s_ctx (dequeue h m st)) = c_avail_meta_area_count (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_meta_alloc_shift_dequeue h m st : c_meta_alloc_shift (s_ctx (dequeue h m st)) = c_meta_alloc_shift (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_meta_area_head_dequeue h m st : c_meta_area_head (s_ctx (dequeue h m st)) = c_meta_area_head (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_meta_area_tail_dequeue h m st : c_meta_area_tail (s_ctx (dequeue h m st)) = c_meta_area_tail (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_avail_meta_areas_dequeue h m st : c_avail_meta_areas (s_ctx (dequeue h m st)) = c_avail_meta_areas (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_usage_dequeue h m st : c_usage (s_ctx (dequeue h m st)) = c_usage (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_unmap_seq_dequeue h m st : c_unmap_seq (s_ctx (dequeue h m st)) = c_unmap_seq (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_bounces_dequeue h m st : c_bounces (s_ctx (dequeue h m st)) = c_bounces (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_seq_dequeue h m st : c_seq (s_ctx (dequeue h m st)) = c_seq (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_brk_dequeue h m st : c_brk (s_ctx (dequeue h m st)) = c_brk (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
#[export] Hint Rewrite s_regions_set_active s_shadow_set_active s_next_rid_set_active s_metas_set_active s_areas_set_active s_groups_set_active s_slots_set_active s_tick_set_active s_secret_set_active s_reserved_set_active s_atop_set_active s_regions_set_usage s_shadow_set_usage s_next_rid_set_usage s_metas_set_usage s_areas_set_usage s_groups_set_usage s_slots_set_usage s_tick_set_usage s_secret_set_usage s_reserved_set_usage s_atop_set_usage s_regions_set_bounce s_shadow_set_bounce s_next_rid_set_bounce s_metas_set_bounce s_areas_set_bounce s_groups_set_bounce s_slots_set_bounce s_tick_set_bounce s_secret_set_bounce s_reserved_set_bounce s_atop_set_bounce s_ctx_put_meta s_regions_put_meta s_shadow_put_meta s_next_rid_put_meta s_areas_put_meta s_groups_put_meta s_slots_put_meta s_tick_put_meta s_secret_put_meta s_reserved_put_meta s_atop_put_meta s_ctx_upd_meta s_regions_upd_meta s_shadow_upd_meta s_next_rid_upd_meta s_areas_upd_meta s_groups_upd_meta s_slots_upd_meta s_tick_upd_meta s_secret_upd_meta s_reserved_upd_meta s_atop_upd_meta s_ctx_put_group s_regions_put_group s_shadow_put_group s_next_rid_put_group s_metas_put_group s_areas_put_group s_slots_put_group s_tick_put_group s_secret_put_group s_reserved_put_group s_atop_put_group s_ctx_del_group s_regions_del_group s_shadow_del_group s_next_rid_del_group s_metas_del_group s_areas_del_group s_slots_del_group s_tick_del_group s_secret_del_group s_reserved_del_group s_atop_del_group s_ctx_set_group_active_idx s_regions_set_group_active_idx s_shadow_set_group_active_idx s_next_rid_set_group_active_idx s_metas_set_group_active_idx s_areas_set_group_active_idx s_slots_set_group_active_idx s_tick_set_group_active_idx s_secret_set_group_active_idx s_reserved_set_group_active_idx s_atop_set_group_active_idx s_ctx_drop_region s_next_rid_drop_region s_metas_drop_region s_areas_drop_region s_groups_drop_region s_slots_drop_region s_tick_drop_region s_secret_drop_region s_reserved_drop_region s_atop_drop_region s_ctx_upd_region s_shadow_upd_region s_next_rid_upd_region s_metas_upd_region s_areas_upd_region s_groups_upd_region s_slots_upd_region s_tick_upd_region s_secret_upd_region s_reserved_upd_region s_atop_upd_region s_ctx_add_slots s_regions_add_slots s_shadow_add_slots s_next_rid_add_slots s_metas_add_slots s_areas_add_slots s_groups_add_slots s_tick_add_slots s_secret_add_slots s_reserved_add_slots s_atop_add_slots s_ctx_del_slots s_regions_del_slots s_shadow_del_slots s_next_rid_del_slots s_metas_del_slots s_areas_del_slots s_groups_del_slots s_tick_del_slots s_secret_del_slots s_reserved_del_slots s_atop_del_slots s_ctx_upd_shadow s_regions_upd_shadow s_next_rid_upd_shadow s_metas_upd_shadow s_areas_upd_shadow s_groups_upd_shadow s_slots_upd_shadow s_tick_upd_shadow s_secret_upd_shadow s_reserved_upd_shadow s_atop_upd_shadow s_ctx_wr8 s_regions_wr8 s_next_rid_wr8 s_metas_wr8 s_areas_wr8 s_groups_wr8 s_slots_wr8 s_tick_wr8 s_secret_wr8 s_reserved_wr8 s_atop_wr8 s_ctx_wr16 s_regions_wr16 s_next_rid_wr16 s_metas_wr16 s_areas_wr16 s_groups_wr16 s_slots_wr16 s_tick_wr16 s_secret_wr16 s_reserved_wr16 s_atop_wr16 s_ctx_wr32 s_regions_wr32 s_next_rid_wr32 s_metas_wr32 s_areas_wr32 s_groups_wr32 s_slots_wr32 s_tick_wr32 s_secret_wr32 s_reserved_wr32 s_atop_wr32 s_ctx_havoc s_regions_havoc s_next_rid_havoc s_metas_havoc s_areas_havoc s_groups_havoc s_slots_havoc s_tick_havoc s_secret_havoc s_reserved_havoc s_atop_havoc s_ctx_hdr_havoc s_regions_hdr_havoc s_next_rid_hdr_havoc s_metas_hdr_havoc s_areas_hdr_havoc s_groups_hdr_havoc s_slots_hdr_havoc s_tick_hdr_havoc s_secret_hdr_havoc s_reserved_hdr_havoc s_atop_hdr_havoc s_regions_step_seq s_shadow_step_seq s_next_rid_step_seq s_metas_step_seq s_areas_step_seq s_groups_step_seq s_slots_step_seq s_tick_step_seq s_secret_step_seq s_reserved_step_seq s_atop_step_seq s_regions_record_seq s_shadow_record_seq s_next_rid_record_seq s_metas_record_seq s_areas_record_seq s_groups_record_seq s_slots_record_seq s_tick_record_seq s_secret_record_seq s_reserved_record_seq s_atop_record_seq s_regions_account_bounce s_shadow_account_bounce s_next_rid_account_bounce s_metas_account_bounce s_areas_account_bounce s_groups_account_bounce s_slots_account_bounce s_tick_account_bounce s_secret_account_bounce s_reserved_account_bounce s_atop_account_bounce s_regions_decay_bounces s_shadow_decay_bounces s_next_rid_decay_bounces s_metas_decay_bounces s_areas_decay_bounces s_groups_decay_bounces s_slots_decay_bounces s_tick_decay_bounces s_secret_decay_bounces s_reserved_decay_bounces s_atop_decay_bounces s_regions_set_head s_shadow_set_head s_next_rid_set_head s_metas_set_head s_areas_set_head s_groups_set_head s_slots_set_head s_tick_set_head s_secret_set_head s_reserved_set_head s_atop_set_head s_regions_dequeue s_shadow_dequeue s_next_rid_dequeue s_areas_dequeue s_groups_dequeue s_slots_dequeue s_tick_dequeue s_secret_dequeue s_reserved_dequeue s_atop_dequeue s_ctx_set_size s_regions_set_size s_next_rid_set_size s_metas_set_size s_areas_set_size s_groups_set_size s_slots_set_size s_tick_set_size s_secret_set_size s_reserved_set_size s_atop_set_size c_secret_set_active c_init_done_set_active c_mmap_counter_set_active c_free_meta_head_set_active c_avail_meta_set_active c_avail_meta_count_set_active c_avail_meta_area_count_set_active c_meta_alloc_shift_set_active c_meta_area_head_set_active c_meta_area_tail_set_active c_avail_meta_areas_set_active c_usage_set_active c_unmap_seq_set_active c_bounces_set_active c_seq_set_active c_brk_set_active c_secret_set_usage c_init_done_set_usage c_mmap_counter_set_usage c_free_meta_head_set_usage c_avail_meta_set_usage c_avail_meta_count_set_usage c_avail_meta_area_count_set_usage c_meta_alloc_shift_set_usage c_meta_area_head_set_usage c_meta_area_tail_set_usage c_avail_meta_areas_set_usage c_active_set_usage c_unmap_seq_set_usage c_bounces_set_usage c_seq_set_usage c_brk_set_usage c_secret_set_bounce c_init_done_set_bounce c_mmap_counter_set_bounce c_free_meta_head_set_bounce c_avail_meta_set_bounce c_avail_meta_count_set_bounce c_avail_meta_area_count_set_bounce c_meta_alloc_shift_set_bounce c_meta_area_head_set_bounce c_meta_area_tail_set_bounce c_avail_meta_areas_set_bounce c_active_set_bounce c_usage_set_bounce c_unmap_seq_set_bounce c_seq_set_bounce c_brk_set_bounce c_secret_step_seq c_init_done_step_seq c_mmap_counter_step_seq c_free_meta_head_step_seq c_avail_meta_step_seq c_avail_meta_count_step_seq c_avail_meta_area_count_step_seq c_meta_alloc_shift_step_seq c_meta_area_head_step_seq c_meta_area_tail_step_seq c_avail_meta_areas_step_seq c_active_step_seq c_usage_step_seq c_bounces_step_seq c_brk_step_seq c_secret_record_seq c_init_done_record_seq c_mmap_counter_record_seq c_free_meta_head_record_seq c_avail_meta_record_seq c_avail_meta_count_record_seq c_avail_meta_area_count_record_seq c_meta_alloc_shift_record_seq c_meta_area_head_record_seq c_meta_area_tail_record_seq c_avail_meta_areas_record_seq c_active_record_seq c_usage_record_seq c_bounces_record_seq c_seq_record_seq c_brk_record_seq c_secret_account_bounce c_init_done_account_bounce c_mmap_counter_account_bounce c_free_meta_head_account_bounce c_avail_meta_account_bounce c_avail_meta_count_account_bounce c_avail_meta_area_count_account_bounce c_meta_alloc_shift_account_bounce c_meta_area_head_account_bounce c_meta_area_tail_account_bounce c_avail_meta_areas_account_bounce c_active_account_bounce c_usage_account_bounce c_unmap_seq_account_bounce c_seq_account_bounce c_brk_account_bounce c_secret_decay_bounces c_init_done_decay_bounces c_mmap_counter_decay_bounces c_free_meta_head_decay_bounces c_avail_meta_decay_bounces c_avail_meta_count_decay_bounces c_avail_meta_area_count_decay_bounces c_meta_alloc_shift_decay_bounces c_meta_area_head_decay_bounces c_meta_area_tail_decay_bounces c_avail_meta_areas_decay_bounces c_active_decay_bounces c_usage_decay_bounces c_unmap_seq_decay_bounces c_seq_decay_bounces c_brk_decay_bounces c_secret_dequeue c_init_done_dequeue c_mmap_counter_dequeue c_avail_meta_dequeue c_avail_meta_count_dequeue c_avail_meta_area_count_dequeue c_meta_alloc_shift_dequeue c_meta_area_head_dequeue c_meta_area_tail_dequeue c_avail_meta_areas_dequeue c_usage_dequeue c_unmap_seq_dequeue c_bounces_dequeue c_seq_dequeue c_brk_dequeue : mst.

Lemma strip_fields st :
  s_ctx (strip st) = s_ctx st /\ s_regions (strip st) = s_regions st /\ s_next_rid (strip st) = s_next_rid st
  /\ s_metas (strip st) = s_metas st /\ s_areas (strip st) = s_areas st /\ s_groups (strip st) = s_groups st
  /\ s_slots (strip st) = s_slots st /\ s_secret (strip st) = s_secret st /\ s_reserved (strip st) = s_reserved st
  /\ s_atop (strip st) = s_atop st.
Proof. repeat split; reflexivity. Qed.

Ltac by_strip H :=
  first [ apply (f_equal s_ctx) in H | apply (f_equal s_regions) in H | apply (f_equal s_next_rid) in H
        | apply (f_equal s_metas) in H | apply (f_equal s_areas) in H | apply (f_equal s_groups) in H
        | apply (f_equal s_slots) in H | apply (f_equal s_secret) in H | apply (f_equal s_reserved) in H
        | apply (f_equal s_atop) in H ]; exact H.

Section LAYOUT_FIELDS.
  Ltac lay lem := intros; pose proof lem as H; cbn [strip] in H;
    match goal with |- ?F _ = _ => apply (f_equal F) in H; cbn in H; exact H end.
  Lemma s_ctx_zero_hdrs p size i cnt st : s_ctx (zero_hdrs p size i cnt st) = s_ctx st. Proof. lay (strip_zero_hdrs p size i cnt st). Qed.
  Lemma s_regions_zero_hdrs p size i cnt st : s_regions (zero_hdrs p size i cnt st) = s_regions st. Proof. lay (strip_zero_hdrs p size i cnt st). Qed.
  Lemma s_next_rid_zero_hdrs p size i cnt st : s_next_rid (zero_hdrs p size i cnt st) = s_next_rid st. Proof. lay (strip_zero_hdrs p size i cnt st). Qed.
  Lemma s_metas_zero_hdrs p size i cnt st : s_metas (zero_hdrs p size i cnt st) = s_metas st. Proof. lay (strip_zero_hdrs p size i cnt st). Qed.
  Lemma s_areas_zero_hdrs p size i cnt st : s_areas (zero_hdrs p size i cnt st) = s_areas st. Proof. lay (strip_zero_hdrs p size i cnt st). Qed.
  Lemma s_groups_zero_hdrs p size i cnt st : s_groups (zero_hdrs p size i cnt st) = s_groups st. Proof. lay (strip_zero_hdrs p size i cnt st). Qed.
  Lemma s_slots_zero_hdrs p size i cnt st : s_slots (zero_hdrs p size i cnt st) = s_slots st. Proof. lay (strip_zero_hdrs p size i cnt st). Qed.
  Lemma s_secret_zero_hdrs p size i cnt st : s_secret (zero_hdrs p size i cnt st) = s_secret st. Proof. lay (strip_zero_hdrs p size i cnt st). Qed.
  Lemma s_reserved_zero_hdrs p size i cnt st : s_reserved (zero_hdrs p size i cnt st) = s_reserved st. Proof. lay (strip_zero_hdrs p size i cnt st). Qed.
  Lemma s_atop_zero_hdrs p size i cnt st : s_atop (zero_hdrs p size i cnt st) = s_atop st. Proof. lay (strip_zero_hdrs p size i cnt st). Qed.
  Lemma s_tick_zero_hdrs p size i cnt st : s_tick (zero_hdrs p size i cnt st) = s_tick st.
  Proof. revert i st; induction cnt; intros; cbn [zero_hdrs]; [reflexivity|]. rewrite IHcnt. reflexivity. Qed.

  Lemma s_ctx_enframe_at st g idx n off : s_ctx (fst (enframe_at st g idx n off)) = s_ctx st. Proof. lay (strip_enframe_at st g idx n off). Qed.
  Lemma s_regions_enframe_at st g idx n off : s_regions (fst (enframe_at st g idx n off)) = s_regions st. Proof. lay (strip_enframe_at st g idx n off). Qed.
  Lemma s_next_rid_enframe_at st g idx n off : s_next_rid (fst (enframe_at st g idx n off)) = s_next_rid st. Proof. lay (strip_enframe_at st g idx n off). Qed.
  Lemma s_metas_enframe_at st g idx n off : s_metas (fst (enframe_at st g idx n off)) = s_metas st. Proof. lay (strip_enframe_at st g idx n off). Qed.
  Lemma s_areas_enframe_at st g idx n off : s_areas (fst (enframe_at st g idx n off)) = s_areas st. Proof. lay (strip_enframe_at st g idx n off). Qed.
  Lemma s_groups_enframe_at st g idx n off : s_groups (fst (enframe_at st g idx n off)) = s_groups st. Proof. lay (strip_enframe_at st g idx n off). Qed.
  Lemma s_slots_enframe_at st g idx n off : s_slots (fst (enframe_at st g idx n off)) = s_slots st. Proof. lay (strip_enframe_at st g idx n off). Qed.
  Lemma s_secret_enframe_at st g idx n off : s_secret (fst (enframe_at st g idx n off)) = s_secret st. Proof. lay (strip_enframe_at st g idx n off). Qed.
  Lemma s_reserved_enframe_at st g idx n off : s_reserved (fst (enframe_at st g idx n off)) = s_reserved st. Proof. lay (strip_enframe_at st g idx n off). Qed.
  Lemma s_atop_enframe_at st g idx n off : s_atop (fst (enframe_at st g idx n off)) = s_atop st. Proof. lay (strip_enframe_at st g idx n off). Qed.
  Lemma s_tick_enframe_at st g idx n off : s_tick (fst (enframe_at st g idx n off)) = s_tick st.
  Proof. unfold enframe_at. destruct (negb (off =? 0)); cbn -[set_size wr8 wr16 Z.add Z.sub Z.mul Z.div get_stride];
    unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.

  Lemma s_ctx_nest_layout st g idx j size cnt : s_ctx (nest_layout st g idx j size cnt) = s_ctx st. Proof. lay (strip_nest_layout st g idx j size cnt). Qed.
  Lemma s_regions_nest_layout st g idx j size cnt : s_regions (nest_layout st g idx j size cnt) = s_regions st. Proof. lay (strip_nest_layout st g idx j size cnt). Qed.
  Lemma s_next_rid_nest_layout st g idx j size cnt : s_next_rid (nest_layout st g idx j size cnt) = s_next_rid st. Proof. lay (strip_nest_layout st g idx j size cnt). Qed.
  Lemma s_metas_nest_layout st g idx j size cnt : s_metas (nest_layout st g idx j size cnt) = s_metas st. Proof. lay (strip_nest_layout st g idx j size cnt). Qed.
  Lemma s_areas_nest_layout st g idx j size cnt : s_areas (nest_layout st g idx j size cnt) = s_areas st. Proof. lay (strip_nest_layout st g idx j size cnt). Qed.
  Lemma s_groups_nest_layout st g idx j size cnt : s_groups (nest_layout st g idx j size cnt) = s_groups st. Proof. lay (strip_nest_layout st g idx j size cnt). Qed.
  Lemma s_slots_nest_layout st g idx j size cnt : s_slots (nest_layout st g idx j size cnt) = s_slots st. Proof. lay (strip_nest_layout st g idx j size cnt). Qed.
  Lemma s_secret_nest_layout st g idx j size cnt : s_secret (nest_layout st g idx j size cnt) = s_secret st. Proof. lay (strip_nest_layout st g idx j size cnt). Qed.
  Lemma s_reserved_nest_layout st g idx j size cnt : s_reserved (nest_layout st g idx j size cnt) = s_reserved st. Proof. lay (strip_nest_layout st g idx j size cnt). Qed.
  Lemma s_atop_nest_layout st g idx j size cnt : s_atop (nest_layout st g idx j size cnt) = s_atop st. Proof. lay (strip_nest_layout st g idx j size cnt). Qed.
  Lemma s_tick_nest_layout st g idx j size cnt : s_tick (nest_layout st g idx j size cnt) = s_tick st.
  Proof. unfold nest_layout. destruct (enframe_at st g idx _ 0) as [st1 p] eqn:E.
    rewrite s_tick_zero_hdrs. cbn. pose proof (s_tick_enframe_at st g idx (UNIT * size_class j - IB) 0) as H. rewrite E in H. exact H. Qed.
End LAYOUT_FIELDS.
#[export] Hint Rewrite s_ctx_zero_hdrs s_regions_zero_hdrs s_next_rid_zero_hdrs s_metas_zero_hdrs s_areas_zero_hdrs s_groups_zero_hdrs s_slots_zero_hdrs s_secret_zero_hdrs s_reserved_zero_hdrs s_atop_zero_hdrs s_tick_zero_hdrs
  s_ctx_enframe_at s_regions_enframe_at s_next_rid_enframe_at s_metas_enframe_at s_areas_enframe_at s_groups_enframe_at s_slots_enframe_at s_secret_enframe_at s_reserved_enframe_at s_atop_enframe_at s_tick_enframe_at
  s_ctx_nest_layout s_regions_nest_layout s_next_rid_nest_layout s_metas_nest_layout s_areas_nest_layout s_groups_nest_layout s_slots_nest_layout s_secret_nest_layout s_reserved_nest_layout s_atop_nest_layout s_tick_nest_layout : mst.

Lemma s_regions_new_region k b l st : s_regions (fst (new_region k b l st)) = <[s_next_rid st := mkRegion k b l]> (s_regions st).
Proof. reflexivity. Qed.
Lemma s_next_rid_new_region k b l st : s_next_rid (fst (new_region k b l st)) = N.succ (s_next_rid st).
Proof. reflexivity. Qed.
Lemma snd_new_region k b l st : snd (new_region k b l st) = s_next_rid st.
Proof. reflexivity. Qed.
Lemma s_regions_drop_region rid st : s_regions (drop_region rid st) = delete rid (s_regions st).
Proof. reflexivity. Qed.
Lemma s_shadow_drop_region rid st : s_shadow (drop_region rid st) = delete rid (s_shadow st).
Proof. reflexivity. Qed.
Lemma s_groups_put_group g mo ai st : s_groups (put_group g mo ai st) = <[g := mkGhdr mo (Z.land ai 31)]> (s_groups st).
Proof. reflexivity. Qed.
Lemma s_groups_del_group g st : s_groups (del_group g st) = delete g (s_groups st).
Proof. reflexivity. Qed.
Lemma s_shadow_upd_shadow rid f st : s_shadow (upd_shadow rid f st) = <[rid := f (get_shadow st rid)]> (s_shadow st).
Proof. reflexivity. Qed.
#[export] Hint Rewrite s_regions_new_region s_next_rid_new_region snd_new_region s_regions_drop_region s_shadow_drop_region
  s_groups_put_group s_groups_del_group s_shadow_upd_shadow : mst.

Lemma active_set_active st sc v sc' : active (set_active sc v st) sc' = if sc' =? sc then v else active st sc'.
Proof.
  unfold active, set_active, ctx; cbn. destruct (Z.eqb_spec sc' sc) as [->|NE].
  - destruct v; [rewrite lookup_insert_eq| rewrite lookup_delete_eq]; reflexivity.
  - destruct v; [rewrite lookup_insert_ne by congruence| rewrite lookup_delete_ne by congruence]; reflexivity.
Qed.
Lemma usage_set_usage st sc v sc' : usage (set_usage sc v st) sc' = if sc' =? sc then v else usage st sc'.
Proof.
  unfold usage, set_usage, ctx; cbn. destruct (Z.eqb_spec sc' sc) as [->|NE];
  [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.
Lemma bounces_set_bounce st i v i' : bounces (set_bounce i v st) i' = if i' =? i then v else bounces st i'.
Proof.
  unfold bounces, set_bounce, ctx; cbn. destruct (Z.eqb_spec i' i) as [->|NE];
  [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.
Lemma get_head_set_head st h v : get_head (set_head h v st) h = v.
Proof. destruct h; cbn; [rewrite active_set_active, Z.eqb_refl|]; reflexivity. Qed.
Lemma get_head_set_head_other st h h' v : h' <> h -> get_head (set_head h v st) h' = get_head st h'.
Proof.
  intros NE. destruct h as [sc|], h' as [sc'|]; cbn; try reflexivity; try congruence.
  rewrite active_set_active. destruct (Z.eqb_spec sc' sc); [congruence| reflexivity].
Qed.
Lemma active_upd_meta st m f sc : active (upd_meta m f st) sc = active st sc. Proof. reflexivity. Qed.
Lemma active_put_meta st m r sc : active (put_meta m r st) sc = active st sc. Proof. reflexivity. Qed.
Lemma usage_upd_meta st m f sc : usage (upd_meta m f st) sc = usage st sc. Proof. reflexivity. Qed.
Lemma get_head_upd_meta st m f h : get_head (upd_meta m f st) h = get_head st h. Proof. destruct h; reflexivity. Qed.
Lemma get_head_put_meta st m r h : get_head (put_meta m r st) h = get_head st h. Proof. destruct h; reflexivity. Qed.
Lemma get_meta_rec_set_head st h v x : get_meta_rec (set_head h v st) x = get_meta_rec st x. Proof. destruct h; reflexivity. Qed.
Lemma get_meta_rec_upd_ctx st f x : get_meta_rec (upd_ctx f st) x = get_meta_rec st x. Proof. reflexivity. Qed.
#[export] Hint Rewrite active_set_active usage_set_usage bounces_set_bounce get_head_set_head
  active_upd_meta active_put_meta usage_upd_meta get_head_upd_meta get_head_put_meta get_meta_rec_set_head get_meta_rec_upd_ctx : mst.


Lemma lookup_new_region k b l st rid :
  s_regions (fst (new_region k b l st)) !! rid = if (rid =? s_next_rid st)%N then Some (mkRegion k b l) else s_regions st !! rid.
Proof.
  rewrite s_regions_new_region. destruct (N.eqb_spec rid (s_next_rid st)) as [->|NE];
  [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.
Lemma lookup_drop_region rid st rid' :
  s_regions (drop_region rid st) !! rid' = if (rid' =? rid)%N then None else s_regions st !! rid'.
Proof.
  rewrite s_regions_drop_region. destruct (N.eqb_spec rid' rid) as [->|NE];
  [rewrite lookup_delete_eq| rewrite lookup_delete_ne by congruence]; reflexivity.
Qed.
Lemma lookup_upd_region rid f st rid' :
  s_regions (upd_region rid f st) !! rid' =
  if (rid' =? rid)%N then option_map f (s_regions st !! rid) else s_regions st !! rid'.
Proof.
  unfold upd_region, get_region. destruct (s_regions st !! rid) as [r|] eqn:E; cbn.
  - destruct (N.eqb_spec rid' rid) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; [reflexivity|reflexivity].
  - destruct (N.eqb_spec rid' rid) as [->|NE]; [rewrite E|]; reflexivity.
Qed.
Lemma conc_eq st p r : s_regions st !! (fst p) = Some r -> conc st p = r_base r + snd p.
Proof. intros H. unfold conc, get_region. rewrite H. reflexivity. Qed.


Lemma lookup_put_group g mo ai st b :
  s_groups (put_group g mo ai st) !! b = if aptr_eqb b g then Some (mkGhdr mo (Z.land ai 31)) else s_groups st !! b.
Proof.
  rewrite s_groups_put_group. destruct (aptr_eqb_spec b g) as [->|NE];
  [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.
Lemma lookup_del_group g st b :
  s_groups (del_group g st) !! b = if aptr_eqb b g then None else s_groups st !! b.
Proof.
  rewrite s_groups_del_group. destruct (aptr_eqb_spec b g) as [->|NE];
  [rewrite lookup_delete_eq| rewrite lookup_delete_ne by congruence]; reflexivity.
Qed.
Lemma lookup_set_group_active_idx g ai st b :
  s_groups (set_group_active_idx g ai st) !! b =
  if aptr_eqb b g then option_map (fun h => mkGhdr (g_meta h) (Z.land ai 31)) (s_groups st !! g) else s_groups st !! b.
Proof.
  unfold set_group_active_idx, get_group. destruct (s_groups st !! g) as [h|] eqn:E; cbn.
  - destruct (aptr_eqb_spec b g) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
  - destruct (aptr_eqb_spec b g) as [->|NE]; [rewrite E|]; reflexivity.
Qed.
Lemma group_active_idx_eq st g m ai : s_groups st !! g = Some (mkGhdr m ai) -> group_active_idx st g = Z.land ai 31.
Proof. intros H. unfold group_active_idx, get_group. rewrite H. reflexivity. Qed.


Lemma Z_iter_ind {A} (f : A -> A) (P : Z -> A -> Prop) x :
  P 0 x -> (forall n a, 0 <= n -> P n a -> P (n + 1) (f a)) -> forall n, 0 <= n -> P n (Z.iter n f x).
Proof.
  intros H0 HS n Hn. rewrite iter_nat_of_Z by exact Hn.
  rewrite <- (Z2Nat.id n) at 1 by exact Hn. rewrite <- Zabs2Nat.abs_nat_nonneg by exact Hn.
  induction (Z.abs_nat n) as [|k IH]; [exact H0|].
  cbn [nat_rect]. rewrite Nat2Z.inj_succ, <- Z.add_1_r. apply HS; [lia| exact IH].
Qed.

Lemma lookup_add_slots m p stride cnt st s : 0 <= cnt -> 0 < stride ->
  s_slots (add_slots m p stride cnt st) !! s =
  if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod stride =? 0) && ((snd s - snd p - UNIT) / stride <? cnt)
  then Some (m, (snd s - snd p - UNIT) / stride) else s_slots st !! s.
Proof.
  intros Hc Hs. unfold add_slots. cbn -[Z.iter Z.add Z.mul Z.sub Z.div Z.modulo Z.leb Z.ltb Z.eqb lookup insert].
  set (F := fun acc : Z * gmap aptr (aptr * Z) => let (i, tb) := acc in (i + 1, <[aadd p (UNIT + stride * i) := (m, i)]> tb)).
  assert (GEN : forall n, 0 <= n -> let r := Z.iter n F (0, s_slots st) in fst r = n /\
            snd r !! s = if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod stride =? 0) && ((snd s - snd p - UNIT) / stride <? n)
                         then Some (m, (snd s - snd p - UNIT) / stride) else s_slots st !! s).
  { intros n Hn. apply (Z_iter_ind F (fun n r => fst r = n /\ snd r !! s = (if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod stride =? 0) && ((snd s - snd p - UNIT) / stride <? n) then Some (m, (snd s - snd p - UNIT) / stride) else s_slots st !! s))); [| |exact Hn].
    - cbn. split; [reflexivity|]. destruct ((fst s =? fst p)%N && _ && _) eqn:E; [|reflexivity].
      destruct (Z.ltb_spec ((snd s - snd p - UNIT) / stride) 0); [|rewrite Bool.andb_false_r; reflexivity].
      exfalso. apply Bool.andb_true_iff in E as [E _]. apply Bool.andb_true_iff in E as [_ E]. apply Z.leb_le in E.
      pose proof (Z.div_pos (snd s - snd p - UNIT) stride E Hs). lia.
    - intros k [i tb] Hk [Hi IH]. cbn in Hi; subst i. unfold F. cbn [fst snd]. split; [reflexivity|].
      destruct (aptr_eqb_spec s (aadd p (UNIT + stride * k))) as [->|NE].
      + rewrite lookup_insert_eq. unfold aadd; cbn [fst snd]. rewrite N.eqb_refl.
        replace (snd p + (UNIT + stride * k) - snd p - UNIT) with (k * stride) by lia.
        rewrite Z_mod_mult, Z.div_mul, Z.eqb_refl by lia. cbn.
        destruct (Z.leb_spec 0 (k * stride)); [|nia]. destruct (Z.ltb_spec k (k + 1)); [|lia]. reflexivity.
      + rewrite lookup_insert_ne by congruence. rewrite IH.
        destruct ((fst s =? fst p)%N) eqn:E1; cbn; [|reflexivity].
        destruct (Z.leb_spec 0 (snd s - snd p - UNIT)); cbn; [|reflexivity].
        destruct (Z.eqb_spec ((snd s - snd p - UNIT) mod stride) 0); cbn; [|reflexivity].
        destruct (Z.ltb_spec ((snd s - snd p - UNIT) / stride) k), (Z.ltb_spec ((snd s - snd p - UNIT) / stride) (k + 1)); try reflexivity; try lia.
        exfalso. apply NE. apply N.eqb_eq in E1. unfold aadd. destruct s as [sr so], p as [pr po]; cbn in *. subst sr. f_equal.
        assert ((so - po - UNIT) / stride = k) by lia.
        pose proof (Z.div_mod (so - po - UNIT) stride ltac:(lia)). lia. }
  destruct (GEN cnt Hc) as [_ G]. exact G.
Qed.

Lemma lookup_del_slots p stride cnt st s : 0 <= cnt -> 0 < stride ->
  s_slots (del_slots p stride cnt st) !! s =
  if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod stride =? 0) && ((snd s - snd p - UNIT) / stride <? cnt)
  then None else s_slots st !! s.
Proof.
  intros Hc Hs. unfold del_slots. cbn -[Z.iter Z.add Z.mul Z.sub Z.div Z.modulo Z.leb Z.ltb Z.eqb lookup delete].
  set (F := fun acc : Z * gmap aptr (aptr * Z) => let (i, tb) := acc in (i + 1, delete (aadd p (UNIT + stride * i)) tb)).
  assert (GEN : forall n, 0 <= n -> let r := Z.iter n F (0, s_slots st) in fst r = n /\
            snd r !! s = if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod stride =? 0) && ((snd s - snd p - UNIT) / stride <? n)
                         then None else s_slots st !! s).
  { intros n Hn. apply (Z_iter_ind F (fun n r => fst r = n /\ snd r !! s = (if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod stride =? 0) && ((snd s - snd p - UNIT) / stride <? n) then None else s_slots st !! s))); [| |exact Hn].
    - cbn. split; [reflexivity|]. destruct ((fst s =? fst p)%N && _ && _) eqn:E; [|reflexivity].
      destruct (Z.ltb_spec ((snd s - snd p - UNIT) / stride) 0); [|rewrite Bool.andb_false_r; reflexivity].
      exfalso. apply Bool.andb_true_iff in E as [E _]. apply Bool.andb_true_iff in E as [_ E]. apply Z.leb_le in E.
      pose proof (Z.div_pos (snd s - snd p - UNIT) stride E Hs). lia.
    - intros k [i tb] Hk [Hi IH]. cbn in Hi; subst i. unfold F. cbn [fst snd]. split; [reflexivity|].
      destruct (aptr_eqb_spec s (aadd p (UNIT + stride * k))) as [->|NE].
      + rewrite lookup_delete_eq. unfold aadd; cbn [fst snd]. rewrite N.eqb_refl.
        replace (snd p + (UNIT + stride * k) - snd p - UNIT) with (k * stride) by lia.
        rewrite Z_mod_mult, Z.div_mul, Z.eqb_refl by lia. cbn.
        destruct (Z.leb_spec 0 (k * stride)); [|nia]. destruct (Z.ltb_spec k (k + 1)); [|lia]. reflexivity.
      + rewrite lookup_delete_ne by congruence. rewrite IH.
        destruct ((fst s =? fst p)%N) eqn:E1; cbn; [|reflexivity].
        destruct (Z.leb_spec 0 (snd s - snd p - UNIT)); cbn; [|reflexivity].
        destruct (Z.eqb_spec ((snd s - snd p - UNIT) mod stride) 0); cbn; [|reflexivity].
        destruct (Z.ltb_spec ((snd s - snd p - UNIT) / stride) k), (Z.ltb_spec ((snd s - snd p - UNIT) / stride) (k + 1)); try reflexivity; try lia.
        exfalso. apply NE. apply N.eqb_eq in E1. unfold aadd. destruct s as [sr so], p as [pr po]; cbn in *. subst sr. f_equal.
        assert ((so - po - UNIT) / stride = k) by lia.
        pose proof (Z.div_mod (so - po - UNIT) stride ltac:(lia)). lia. }
  destruct (GEN cnt Hc) as [_ G]. exact G.
Qed.

Lemma slot_key_test p stride cnt s : 0 < stride ->
  ((fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod stride =? 0) && ((snd s - snd p - UNIT) / stride <? cnt)) = true
  <-> exists i, 0 <= i < cnt /\ s = aadd p (UNIT + stride * i).
Proof.
  intros Hs. rewrite !Bool.andb_true_iff, N.eqb_eq, Z.leb_le, Z.eqb_eq, Z.ltb_lt. split.
  - intros [[[E1 E2] E3] E4]. exists ((snd s - snd p - UNIT) / stride). split.
    + split; [apply Z.div_pos; lia| exact E4].
    + unfold aadd. destruct s as [sr so], p as [pr po]; cbn in *. subst sr. f_equal.
      pose proof (Z.div_mod (so - po - UNIT) stride ltac:(lia)). lia.
  - intros (i & Hi & ->). unfold aadd; cbn. replace (snd p + (UNIT + stride * i) - snd p - UNIT) with (i * stride) by lia.
    rewrite Z_mod_mult, Z.div_mul by lia. repeat split; auto; try lia.
Qed.


Lemma get_shadow_eq st rid : get_shadow st rid = default shadow0 (s_shadow st !! rid).
Proof. reflexivity. Qed.
Lemma get_shadow_ext st st' rid : s_shadow st' = s_shadow st -> get_shadow st' rid = get_shadow st rid.
Proof. intros H. unfold get_shadow. rewrite H. reflexivity. Qed.
Lemma get_shadow_upd_shadow rid f st rid' :
  get_shadow (upd_shadow rid f st) rid' = if (rid' =? rid)%N then f (get_shadow st rid) else get_shadow st rid'.
Proof.
  unfold get_shadow, upd_shadow; cbn. destruct (N.eqb_spec rid' rid) as [->|NE];
  [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.

Lemma cell_read_wr8 p v st q :
  cell_read (get_shadow (wr8 p v st) (fst q)) (snd q) =
  if aptr_eqb q p then
    (let r := get_shadow st (fst p) in
     let hl := default [] (r_hav r !! (snd p / 16)) in
     let hp := r_havp r !! (snd p / 4096) in
     if stale_pg hp (Some (s_tick st)) || stale hl (snd p mod 16) (Some (s_tick st)) then Unknown (Z.land v 255) else Known (Z.land v 255))
  else cell_read (get_shadow st (fst q)) (snd q).
Proof.
  unfold wr8. rewrite get_shadow_upd_shadow. destruct (aptr_eqb_spec q p) as [->|NE].
  - rewrite N.eqb_refl. unfold cell_read; cbn. rewrite lookup_insert_eq. reflexivity.
  - destruct (N.eqb_spec (fst q) (fst p)) as [E|NE2]; [|reflexivity].
    unfold cell_read; cbn. rewrite E. rewrite lookup_insert_ne; [reflexivity|].
    intros E2. apply NE. destruct q, p; cbn in *; congruence.
Qed.

Definition sh_ticks (r : shadow) (t : N) : Prop :=
  (forall u hl ch, r_hav r !! u = Some hl -> In ch hl -> (snd ch <= t)%N)
  /\ (forall pg t', r_havp r !! pg = Some t' -> (t' <= t)%N).

Lemma not_stale_cur r t b : sh_ticks r t ->
  forall u pg, stale_pg (r_havp r !! pg) (Some t) || stale (default [] (r_hav r !! u)) b (Some t) = false.
Proof.
  intros [Hh Hp] u pg. apply Bool.orb_false_iff. split.
  - destruct (r_havp r !! pg) as [t'|] eqn:E; cbn; [|reflexivity]. apply N.ltb_ge. eapply Hp; eauto.
  - unfold stale. apply Bool.not_true_iff_false. rewrite existsb_exists. intros ([c h] & Hin & Hb). cbn in Hb.
    apply Bool.andb_true_iff in Hb as [_ Hb]. apply N.ltb_lt in Hb.
    destruct (r_hav r !! u) as [hl|] eqn:E; cbn in Hin; [|contradiction].
    pose proof (Hh u hl (c, h) E Hin). cbn in H. lia.
Qed.

Lemma cell_read_wr8_same p v st : sh_ticks (get_shadow st (fst p)) (s_tick st) ->
  cell_read (get_shadow (wr8 p v st) (fst p)) (snd p) = Known (Z.land v 255).
Proof.
  intros HT. rewrite (cell_read_wr8 p v st p), aptr_eqb_refl. cbn zeta. rewrite (not_stale_cur _ _ _ HT). reflexivity.
Qed.
Lemma cell_read_wr8_other p v st q : q <> p ->
  cell_read (get_shadow (wr8 p v st) (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Proof. intros NE. rewrite cell_read_wr8, aptr_eqb_neq by exact NE. reflexivity. Qed.

Lemma sh_ticks_wr8 p v st rid : sh_ticks (get_shadow st rid) (s_tick st) -> sh_ticks (get_shadow (wr8 p v st) rid) (s_tick st).
Proof.
  intros H. unfold wr8. rewrite get_shadow_upd_shadow. destruct (N.eqb_spec rid (fst p)) as [->|NE]; [|exact H].
  destruct H as [Hh Hp]. split; cbn; eauto.
Qed.
End MI_Kit.
