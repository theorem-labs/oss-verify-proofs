(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKyU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKyU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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
s_next_rid_strip s_secret_strip s_reserved_strip active_strip usage_strip unmap_seq_strip bounces_strip
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
s_ctx s_regions s_shadow s_metas s_areas s_groups s_slots s_next_rid s_tick s_secret s_reserved
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

#[export] Set Keyed Unification.

Ltac srw_pass :=
try (match goal with |- context [strip (hdr_havoc _ _)] => idtac end; repeat rewrite strip_hdr_havoc);
try (match goal with |- context [strip (nest_layout _ _ _ _ _ _)] => idtac end; repeat rewrite strip_nest_layout);
try (match goal with |- context [strip (set_size _ _ _ _ _)] => idtac end; repeat rewrite strip_set_size);
try (match goal with |- context [strip (zero_hdrs _ _ _ _ _)] => idtac end; repeat rewrite strip_zero_hdrs);
try (match goal with |- context [strip (set_tick _ _)] => idtac end; repeat rewrite strip_set_tick);
try (match goal with |- context [strip (havoc _ _ _)] => idtac end; repeat rewrite strip_havoc);
try (match goal with |- context [strip (wr32 _ _ _)] => idtac end; repeat rewrite strip_wr32);
try (match goal with |- context [strip (wr16 _ _ _)] => idtac end; repeat rewrite strip_wr16);
try (match goal with |- context [strip (wr8 _ _ _)] => idtac end; repeat rewrite strip_wr8);
try (match goal with |- context [strip (strip _)] => idtac end; repeat rewrite strip_strip);
try (match goal with |- context [dequeue _ _ (strip _)] => idtac end; repeat rewrite strip_dequeue);
try (match goal with |- context [decay_bounces _ (strip _)] => idtac end; repeat rewrite strip_decay_bounces);
try (match goal with |- context [account_bounce _ (strip _)] => idtac end; repeat rewrite strip_account_bounce);
try (match goal with |- context [record_seq _ (strip _)] => idtac end; repeat rewrite strip_record_seq);
try (match goal with |- context [step_seq (strip _)] => idtac end; repeat rewrite strip_step_seq);
try (match goal with |- context [upd_region _ _ (strip _)] => idtac end; repeat rewrite strip_upd_region);
try (match goal with |- context [new_region _ _ _ (strip _)] => idtac end; repeat rewrite strip_new_region);
try (match goal with |- context [drop_region _ (strip _)] => idtac end; repeat rewrite strip_drop_region);
try (match goal with |- context [del_slots _ _ _ (strip _)] => idtac end; repeat rewrite strip_del_slots);
try (match goal with |- context [add_slots _ _ _ _ (strip _)] => idtac end; repeat rewrite strip_add_slots);
try (match goal with |- context [del_group _ (strip _)] => idtac end; repeat rewrite strip_del_group);
try (match goal with |- context [set_group_active_idx _ _ (strip _)] => idtac end; repeat rewrite strip_set_group_active_idx);
try (match goal with |- context [put_group _ _ _ (strip _)] => idtac end; repeat rewrite strip_put_group);
try (match goal with |- context [set_areas _ (strip _)] => idtac end; repeat rewrite strip_set_areas);
try (match goal with |- context [set_bounce _ _ (strip _)] => idtac end; repeat rewrite strip_set_bounce);
try (match goal with |- context [set_usage _ _ (strip _)] => idtac end; repeat rewrite strip_set_usage);
try (match goal with |- context [set_head _ _ (strip _)] => idtac end; repeat rewrite strip_set_head);
try (match goal with |- context [set_active _ _ (strip _)] => idtac end; repeat rewrite strip_set_active);
try (match goal with |- context [put_meta _ _ (strip _)] => idtac end; repeat rewrite strip_put_meta);
try (match goal with |- context [upd_meta _ _ (strip _)] => idtac end; repeat rewrite strip_upd_meta);
try (match goal with |- context [upd_ctx _ (strip _)] => idtac end; repeat rewrite strip_upd_ctx);
try (match goal with |- context [slot_of (strip _) _ _] => idtac end; repeat rewrite slot_of_strip);
try (match goal with |- context [okay_to_free (strip _) _] => idtac end; repeat rewrite okay_to_free_strip);
try (match goal with |- context [is_bouncing _ (strip _)] => idtac end; repeat rewrite is_bouncing_strip);
try (match goal with |- context [get_head (strip _) _] => idtac end; repeat rewrite get_head_strip);
try (match goal with |- context [brk_pages_ok (strip _) _ _] => idtac end; repeat rewrite brk_pages_ok_strip);
try (match goal with |- context [live_ranges (strip _)] => idtac end; repeat rewrite live_ranges_strip);
try (match goal with |- context [conc (strip _) _] => idtac end; repeat rewrite conc_strip);
try (match goal with |- context [get_region (strip _) _] => idtac end; repeat rewrite get_region_strip);
try (match goal with |- context [group_active_idx (strip _) _] => idtac end; repeat rewrite group_active_idx_strip);
try (match goal with |- context [get_group (strip _) _] => idtac end; repeat rewrite get_group_strip);
try (match goal with |- context [get_meta_rec (strip _) _] => idtac end; repeat rewrite get_meta_rec_strip);
try (match goal with |- context [bounces (strip _) _] => idtac end; repeat rewrite bounces_strip);
try (match goal with |- context [unmap_seq (strip _) _] => idtac end; repeat rewrite unmap_seq_strip);
try (match goal with |- context [usage (strip _) _] => idtac end; repeat rewrite usage_strip);
try (match goal with |- context [active (strip _) _] => idtac end; repeat rewrite active_strip);
try (match goal with |- context [s_reserved (strip _)] => idtac end; repeat rewrite s_reserved_strip);
try (match goal with |- context [s_secret (strip _)] => idtac end; repeat rewrite s_secret_strip);
try (match goal with |- context [s_next_rid (strip _)] => idtac end; repeat rewrite s_next_rid_strip);
try (match goal with |- context [s_slots (strip _)] => idtac end; repeat rewrite s_slots_strip);
try (match goal with |- context [s_groups (strip _)] => idtac end; repeat rewrite s_groups_strip);
try (match goal with |- context [s_areas (strip _)] => idtac end; repeat rewrite s_areas_strip);
try (match goal with |- context [s_metas (strip _)] => idtac end; repeat rewrite s_metas_strip);
try (match goal with |- context [s_regions (strip _)] => idtac end; repeat rewrite s_regions_strip);
try (match goal with |- context [s_ctx (strip _)] => idtac end; repeat rewrite s_ctx_strip);
try (match goal with |- context [ctx (strip _)] => idtac end; repeat rewrite ctx_strip).

Ltac srw_hit := first [
match goal with |- context [strip ?x] => lazymatch x with
| hdr_havoc _ _ => rewrite strip_hdr_havoc
| nest_layout _ _ _ _ _ _ => rewrite strip_nest_layout
| set_size _ _ _ _ _ => rewrite strip_set_size
| zero_hdrs _ _ _ _ _ => rewrite strip_zero_hdrs
| set_tick _ _ => rewrite strip_set_tick
| havoc _ _ _ => rewrite strip_havoc
| wr32 _ _ _ => rewrite strip_wr32
| wr16 _ _ _ => rewrite strip_wr16
| wr8 _ _ _ => rewrite strip_wr8
| strip _ => rewrite strip_strip
end end
|   match goal with |- context [?G (strip _)] => lazymatch G with
| dequeue _ _ => rewrite strip_dequeue
| decay_bounces _ => rewrite strip_decay_bounces
| account_bounce _ => rewrite strip_account_bounce
| record_seq _ => rewrite strip_record_seq
| step_seq => rewrite strip_step_seq
| upd_region _ _ => rewrite strip_upd_region
| new_region _ _ _ => rewrite strip_new_region
| drop_region _ => rewrite strip_drop_region
| del_slots _ _ _ => rewrite strip_del_slots
| add_slots _ _ _ _ => rewrite strip_add_slots
| del_group _ => rewrite strip_del_group
| set_group_active_idx _ _ => rewrite strip_set_group_active_idx
| put_group _ _ _ => rewrite strip_put_group
| set_areas _ => rewrite strip_set_areas
| set_bounce _ _ => rewrite strip_set_bounce
| set_usage _ _ => rewrite strip_set_usage
| set_head _ _ => rewrite strip_set_head
| set_active _ _ => rewrite strip_set_active
| put_meta _ _ => rewrite strip_put_meta
| upd_meta _ _ => rewrite strip_upd_meta
| upd_ctx _ => rewrite strip_upd_ctx
| slot_of => rewrite slot_of_strip
| okay_to_free => rewrite okay_to_free_strip
| is_bouncing _ => rewrite is_bouncing_strip
| get_head => rewrite get_head_strip
| brk_pages_ok => rewrite brk_pages_ok_strip
| live_ranges => rewrite live_ranges_strip
| conc => rewrite conc_strip
| get_region => rewrite get_region_strip
| group_active_idx => rewrite group_active_idx_strip
| get_group => rewrite get_group_strip
| get_meta_rec => rewrite get_meta_rec_strip
| bounces => rewrite bounces_strip
| unmap_seq => rewrite unmap_seq_strip
| usage => rewrite usage_strip
| active => rewrite active_strip
| s_reserved => rewrite s_reserved_strip
| s_secret => rewrite s_secret_strip
| s_next_rid => rewrite s_next_rid_strip
| s_slots => rewrite s_slots_strip
| s_groups => rewrite s_groups_strip
| s_areas => rewrite s_areas_strip
| s_metas => rewrite s_metas_strip
| s_regions => rewrite s_regions_strip
| s_ctx => rewrite s_ctx_strip
| ctx => rewrite ctx_strip
end end ].
Ltac srw := repeat srw_hit.

Ltac strip_in1 :=
first
[ (match goal with |- context [strip (nest_layout _ _ _ _ _ _)] => idtac end; rewrite strip_nest_layout)
| (match goal with |- context [strip (hdr_havoc _ _)] => idtac end; rewrite strip_hdr_havoc)
| (match goal with |- context [strip (fst (enframe_at _ _ _ _ _))] => idtac end; rewrite strip_enframe_at)
| (match goal with |- context [strip (zero_hdrs _ _ _ _ _)] => idtac end; rewrite strip_zero_hdrs)
| (match goal with |- context [strip (set_size _ _ _ _ _)] => idtac end; rewrite strip_set_size)
| (match goal with |- context [strip (havoc _ _ _)] => idtac end; rewrite strip_havoc)
| (match goal with |- context [strip (wr32 _ _ _)] => idtac end; rewrite strip_wr32)
| (match goal with |- context [strip (wr16 _ _ _)] => idtac end; rewrite strip_wr16)
| (match goal with |- context [strip (wr8 _ _ _)] => idtac end; rewrite strip_wr8)
| (match goal with |- context [strip (set_tick _ _)] => idtac end; rewrite strip_set_tick)
| (match goal with |- context [strip (strip _)] => idtac end; rewrite strip_strip)
| (match goal with |- context [strip (dequeue _ _ _)] => idtac end; rewrite <- strip_dequeue)
| (match goal with |- context [strip (step_seq _)] => idtac end; rewrite <- strip_step_seq)
| (match goal with |- context [strip (record_seq _ _)] => idtac end; rewrite <- strip_record_seq)
| (match goal with |- context [strip (account_bounce _ _)] => idtac end; rewrite <- strip_account_bounce)
| (match goal with |- context [strip (decay_bounces _ _)] => idtac end; rewrite <- strip_decay_bounces)
| (match goal with |- context [strip (drop_region _ _)] => idtac end; rewrite <- strip_drop_region)
| (match goal with |- context [strip (del_slots _ _ _ _)] => idtac end; rewrite <- strip_del_slots)
| (match goal with |- context [strip (add_slots _ _ _ _ _)] => idtac end; rewrite <- strip_add_slots)
| (match goal with |- context [strip (del_group _ _)] => idtac end; rewrite <- strip_del_group)
| (match goal with |- context [strip (set_group_active_idx _ _ _)] => idtac end; rewrite <- strip_set_group_active_idx)
| (match goal with |- context [strip (put_group _ _ _ _)] => idtac end; rewrite <- strip_put_group)
| (match goal with |- context [strip (upd_region _ _ _)] => idtac end; rewrite <- strip_upd_region)
| (match goal with |- context [strip (set_head _ _ _)] => idtac end; rewrite <- strip_set_head)
| (match goal with |- context [strip (set_active _ _ _)] => idtac end; rewrite <- strip_set_active)
| (match goal with |- context [strip (set_usage _ _ _)] => idtac end; rewrite <- strip_set_usage)
| (match goal with |- context [strip (set_bounce _ _ _)] => idtac end; rewrite <- strip_set_bounce)
| (match goal with |- context [strip (upd_meta _ _ _)] => idtac end; rewrite <- strip_upd_meta)
| (match goal with |- context [strip (put_meta _ _ _)] => idtac end; rewrite <- strip_put_meta)
| (match goal with |- context [strip (set_areas _ _)] => idtac end; rewrite <- strip_set_areas)
| (match goal with |- context [strip (upd_ctx _ _)] => idtac end; rewrite <- strip_upd_ctx) ].
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
Local Notation BREL := (BREL pans pupd).
Local Notation prun := (prun pans pupd).

Definition DREL {X1 X2} (XX : O * X1 -> X2 -> Prop) (dec1 : decoder X1) (dec2 : decoder X2) : Prop :=
forall p k1 k2 b1 b2,
(forall o m idx, strel XX (prun o (k1 m idx)) (k2 m idx)) ->
BREL XX b1 b2 ->
forall o st cst, cst = strip st -> strel XX (prun o (dec1 st p k1 b1)) (dec2 cst p k2 b2).

End CPS.

Section TOP.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).

Definition CREL (x : O * (mstate * option (aptr * Z))) (y : mstate * option (aptr * Z)) : Prop :=
strip (fst (snd x)) = fst y /\ snd (snd x) = snd y.

Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.

Definition MREL (x : O * (mstate * optr)) (y : mstate * option cptr) : Prop :=
strip (fst (snd x)) = fst y /\
match snd (snd x), snd y with
| None, None => True
| Some p, Some c => fst p = fst c /\ exists off, snd p = snd c + UNIT * off
| _, _ => False
end.

Definition FREL (x : O * mstate) (y : mstate) : Prop := strip (snd x) = y.

Definition hdr_ok (st : mstate) (p : aptr) (c : cptr) : Prop :=
exists st1 g idx,
(forall o, (prun pans pupd) o (free_hdr st p) = SRet (o, Some (st1, g, idx)))
/\ strip st1 = strip st
/\ (s_slots st) !! c = Some (g, idx)
/\ (forall o, strel (fun x y => strip (snd x) = strip y)
((prun pans pupd) o (free_tail dec_hdr st1 g idx))
(free_tail dec_slots (strip st) g idx)).

Fixpoint follow {R} (t : M R) (ans : list Z) : option R :=
match t, ans with
| SRet r, _ => Some r
| SVis (EUndef _) _, _ => None
| SVis _ k, a :: ans' => follow (k a) ans'
| SVis _ _, [] => None
end.

Inductive reach : mstate -> list aptr -> list cptr -> Prop :=
| reach_init secret res : reach (minit secret res) [] []
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

