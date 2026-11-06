(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv.
Import ListNotations.
Local Open Scope Z_scope.

Definition rebase_region (rho : N -> Z) (rid : N) (r : region) : region := mkRegion (r_kind r) (rho rid) (r_len r).
Definition rebase_regions (rho : N -> Z) (m : gmap N region) : gmap N region :=
map_imap (fun rid r => Some (rebase_region rho rid r)) m.
Definition rebase (rho : N -> Z) (resv : list (Z * Z)) (ceil : Z) (cs : mstate) : mstate :=
mkState (s_ctx cs) (rebase_regions rho (s_regions cs)) (s_shadow cs) (s_next_rid cs)
(s_metas cs) (s_areas cs) (s_groups cs) (s_slots cs) (s_tick cs) (s_secret cs) ceil resv.

Definition nupd (rho : N -> Z) (rid : N) (b : Z) : N -> Z := fun r => if (r =? rid)%N then b else rho r.

Lemma lookup_rebase_regions rho m rid : rebase_regions rho m !! rid = option_map (rebase_region rho rid) (m !! rid).
Proof. unfold rebase_regions. rewrite map_lookup_imap. destruct (m !! rid); reflexivity. Qed.

Lemma rebase_regions_delete rho m rid : rebase_regions rho (delete rid m) = delete rid (rebase_regions rho m).
Proof. unfold rebase_regions. apply map_imap_delete. Qed.

Lemma rebase_regions_insert rho m rid r :
rebase_regions rho (<[rid := r]> m) = <[rid := rebase_region rho rid r]> (rebase_regions rho m).
Proof. unfold rebase_regions. rewrite map_imap_insert. reflexivity. Qed.

Lemma rebase_regions_ext rho rho' m : (forall rid, m !! rid <> None -> rho' rid = rho rid) ->
rebase_regions rho' m = rebase_regions rho m.
Proof.
intros H. apply map_eq. intros i. rewrite !lookup_rebase_regions.
destruct (m !! i) as [r|] eqn:E; [| reflexivity]. cbn. unfold rebase_region. rewrite (H i) by (rewrite E; discriminate). reflexivity.
Qed.

Section REBASE_RW.
Variables (rho : N -> Z) (resv : list (Z * Z)). Context {ceil : Z}.
Local Notation RB := (rebase rho resv ceil).
Implicit Types cs : mstate.

#[using="Type"] Lemma ctx_rebase cs : ctx (RB cs) = ctx cs. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_ctx_rebase cs : s_ctx (RB cs) = s_ctx cs. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_metas_rebase cs : s_metas (RB cs) = s_metas cs. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_areas_rebase cs : s_areas (RB cs) = s_areas cs. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_groups_rebase cs : s_groups (RB cs) = s_groups cs. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_slots_rebase cs : s_slots (RB cs) = s_slots cs. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_shadow_rebase cs : s_shadow (RB cs) = s_shadow cs. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_tick_rebase cs : s_tick (RB cs) = s_tick cs. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_next_rid_rebase cs : s_next_rid (RB cs) = s_next_rid cs. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_secret_rebase cs : s_secret (RB cs) = s_secret cs. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_reserved_rebase cs : s_reserved (RB cs) = resv. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_ceil_rebase cs : s_ceil (RB cs) = ceil. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_regions_rebase cs : s_regions (RB cs) = rebase_regions rho (s_regions cs). Proof. reflexivity. Qed.
#[using="Type"] Lemma active_rebase cs sc : active (RB cs) sc = active cs sc. Proof. reflexivity. Qed.
#[using="Type"] Lemma usage_rebase cs sc : usage (RB cs) sc = usage cs sc. Proof. reflexivity. Qed.
#[using="Type"] Lemma unmap_seq_rebase cs i : unmap_seq (RB cs) i = unmap_seq cs i. Proof. reflexivity. Qed.
#[using="Type"] Lemma bounces_rebase cs i : bounces (RB cs) i = bounces cs i. Proof. reflexivity. Qed.
#[using="Type"] Lemma get_meta_rec_rebase cs m : get_meta_rec (RB cs) m = get_meta_rec cs m. Proof. reflexivity. Qed.
#[using="Type"] Lemma get_group_rebase cs g : get_group (RB cs) g = get_group cs g. Proof. reflexivity. Qed.
#[using="Type"] Lemma group_active_idx_rebase cs g : group_active_idx (RB cs) g = group_active_idx cs g. Proof. reflexivity. Qed.
#[using="Type"] Lemma get_head_rebase cs h : get_head (RB cs) h = get_head cs h. Proof. destruct h; reflexivity. Qed.
#[using="Type"] Lemma is_bouncing_rebase sc cs : is_bouncing sc (RB cs) = is_bouncing sc cs. Proof. reflexivity. Qed.
#[using="Type"] Lemma okay_to_free_rebase cs g : okay_to_free (RB cs) g = okay_to_free cs g. Proof. reflexivity. Qed.
#[using="Type"] Lemma slot_of_rebase cs g i : slot_of (RB cs) g i = slot_of cs g i. Proof. reflexivity. Qed.
#[using="Type"] Lemma get_shadow_rebase cs rid : get_shadow (RB cs) rid = get_shadow cs rid. Proof. reflexivity. Qed.
#[using="Type"] Lemma get_region_rebase cs rid : get_region (RB cs) rid = option_map (rebase_region rho rid) (get_region cs rid).
Proof. unfold get_region. apply lookup_rebase_regions. Qed.
#[using="Type"] Lemma conc_rebase cs p : conc (RB cs) p = match get_region cs (fst p) with Some _ => rho (fst p) + snd p | None => 0 end.
Proof. unfold conc. rewrite get_region_rebase. destruct (get_region cs (fst p)); reflexivity. Qed.

#[using="Type"] Lemma rebase_upd_ctx f cs : upd_ctx f (RB cs) = RB (upd_ctx f cs). Proof. reflexivity. Qed.
#[using="Type"] Lemma rebase_upd_meta m f cs : upd_meta m f (RB cs) = RB (upd_meta m f cs). Proof. reflexivity. Qed.
#[using="Type"] Lemma rebase_put_meta m r cs : put_meta m r (RB cs) = RB (put_meta m r cs). Proof. reflexivity. Qed.
#[using="Type"] Lemma rebase_set_active sc v cs : set_active sc v (RB cs) = RB (set_active sc v cs). Proof. reflexivity. Qed.
#[using="Type"] Lemma rebase_set_head h v cs : set_head h v (RB cs) = RB (set_head h v cs). Proof. destruct h; reflexivity. Qed.
#[using="Type"] Lemma rebase_set_usage sc v cs : set_usage sc v (RB cs) = RB (set_usage sc v cs). Proof. reflexivity. Qed.
#[using="Type"] Lemma rebase_set_bounce i v cs : set_bounce i v (RB cs) = RB (set_bounce i v cs). Proof. reflexivity. Qed.
#[using="Type"] Lemma rebase_set_areas a cs : set_areas a (RB cs) = RB (set_areas a cs). Proof. reflexivity. Qed.
#[using="Type"] Lemma rebase_set_metas a cs : set_metas a (RB cs) = RB (set_metas a cs). Proof. reflexivity. Qed.
#[using="Type"] Lemma rebase_set_groups a cs : set_groups a (RB cs) = RB (set_groups a cs). Proof. reflexivity. Qed.
#[using="Type"] Lemma rebase_set_slots a cs : set_slots a (RB cs) = RB (set_slots a cs). Proof. reflexivity. Qed.
#[using="Type"] Lemma rebase_set_tick t cs : set_tick t (RB cs) = RB (set_tick t cs). Proof. reflexivity. Qed.
#[using="Type"] Lemma rebase_put_group g m ai cs : put_group g m ai (RB cs) = RB (put_group g m ai cs). Proof. reflexivity. Qed.
#[using="Type"] Lemma rebase_set_group_active_idx g ai cs : set_group_active_idx g ai (RB cs) = RB (set_group_active_idx g ai cs).
Proof. unfold set_group_active_idx. rewrite get_group_rebase. destruct (get_group cs g); reflexivity. Qed.
#[using="Type"] Lemma rebase_del_group g cs : del_group g (RB cs) = RB (del_group g cs). Proof. reflexivity. Qed.
#[using="Type"] Lemma rebase_add_slots m p s c cs : add_slots m p s c (RB cs) = RB (add_slots m p s c cs). Proof. reflexivity. Qed.
#[using="Type"] Lemma rebase_del_slots p s c cs : del_slots p s c (RB cs) = RB (del_slots p s c cs). Proof. reflexivity. Qed.
#[using="Type"] Lemma rebase_drop_region rid cs : drop_region rid (RB cs) = RB (drop_region rid cs).
Proof. unfold drop_region, rebase; cbn. rewrite rebase_regions_delete. reflexivity. Qed.
#[using="Type"] Lemma rebase_step_seq cs : step_seq (RB cs) = RB (step_seq cs).
Proof. unfold step_seq. rewrite ctx_rebase. destruct (c_seq (ctx cs) =? 255); reflexivity. Qed.
#[using="Type"] Lemma rebase_record_seq sc cs : record_seq sc (RB cs) = RB (record_seq sc cs).
Proof. unfold record_seq. destruct (sc_in_seq_range sc); reflexivity. Qed.
#[using="Type"] Lemma rebase_account_bounce sc cs : account_bounce sc (RB cs) = RB (account_bounce sc cs).
Proof. unfold account_bounce. rewrite !unmap_seq_rebase, !bounces_rebase, !ctx_rebase.
destruct (sc_in_seq_range sc); [|reflexivity]. destruct (negb _ && _); [|reflexivity]. destruct (_ <? 100); reflexivity. Qed.
#[using="Type"] Lemma rebase_decay_bounces sc cs : decay_bounces sc (RB cs) = RB (decay_bounces sc cs).
Proof. unfold decay_bounces. rewrite !bounces_rebase. destruct (_ && _); reflexivity. Qed.
#[using="Type"] Lemma rebase_dequeue h m cs : dequeue h m (RB cs) = RB (dequeue h m cs).
Proof.
unfold dequeue. rewrite !get_meta_rec_rebase.
destruct (negb _); [|rewrite rebase_set_head; reflexivity].
destruct (m_prev _); destruct (m_next _); rewrite ?rebase_upd_meta, ?get_head_rebase;
destruct (optr_eqb _ _); rewrite ?rebase_set_head, ?rebase_upd_meta; reflexivity.
Qed.
#[using="Type"] Lemma rebase_wr8 p v cs : wr8 p v (RB cs) = RB (wr8 p v cs). Proof. reflexivity. Qed.
#[using="Type"] Lemma rebase_hdr_havoc b cs : hdr_havoc b (RB cs) = RB (hdr_havoc b cs). Proof. reflexivity. Qed.
#[using="Type"] Lemma rebase_upd_region rid f cs : (forall r, f (rebase_region rho rid r) = rebase_region rho rid (f r)) ->
upd_region rid f (RB cs) = RB (upd_region rid f cs).
Proof.
intros Hf. unfold upd_region. rewrite get_region_rebase. destruct (get_region cs rid) as [r|]; [| reflexivity]. cbn.
unfold rebase. cbn. rewrite rebase_regions_insert, Hf. reflexivity.
Qed.

#[using="Type"] Lemma rebase_new_region k bC l cs bG :
new_region k bC l (RB cs) = (rebase (nupd rho (s_next_rid cs) bC) resv ceil (fst (new_region k bG l cs)), snd (new_region k bG l cs)).
Proof.
unfold new_region, rebase. cbn. f_equal. f_equal. rewrite rebase_regions_insert.
unfold set_next_rid, set_regions. cbn. f_equal. unfold rebase_region, nupd at 1. cbn. rewrite N.eqb_refl. apply map_eq. intros i.
destruct (N.eq_dec i (s_next_rid cs)) as [->|NE]; [rewrite !lookup_insert_eq; reflexivity|].
rewrite !lookup_insert_ne by congruence. rewrite !lookup_rebase_regions. destruct (s_regions cs !! i); [| reflexivity]. cbn.
unfold rebase_region, nupd. destruct (N.eqb_spec i (s_next_rid cs)); [congruence| reflexivity].
Qed.
#[using="Type"] Lemma rebase_strip cs : strip (RB cs) = RB (strip cs). Proof. reflexivity. Qed.
End REBASE_RW.

Hint Rewrite ctx_rebase s_ctx_rebase s_metas_rebase s_areas_rebase s_groups_rebase s_slots_rebase s_shadow_rebase s_tick_rebase
s_next_rid_rebase s_secret_rebase s_ceil_rebase active_rebase usage_rebase unmap_seq_rebase bounces_rebase
get_meta_rec_rebase get_group_rebase group_active_idx_rebase get_head_rebase is_bouncing_rebase okay_to_free_rebase slot_of_rebase get_shadow_rebase
rebase_upd_ctx rebase_upd_meta rebase_put_meta rebase_set_active rebase_set_head rebase_set_usage rebase_set_bounce
rebase_set_areas rebase_set_metas rebase_set_groups rebase_set_slots rebase_set_tick rebase_put_group rebase_set_group_active_idx rebase_del_group rebase_add_slots rebase_del_slots
rebase_drop_region rebase_step_seq rebase_record_seq rebase_account_bounce
rebase_decay_bounces rebase_dequeue rebase_wr8 rebase_hdr_havoc
: reb_rw.

Section RELS.
Variables (rho : N -> Z) (resv : list (Z * Z)). Context {ceil : Z}.
Definition KRELr {X R1 R2} (RR : R1 -> R2 -> Prop) (k1 : mstate -> X -> M R1) (k2 : mstate -> X -> M R2) : Prop :=
forall cs cs' x, cs' = rebase rho resv ceil cs -> strel RR (k1 cs x) (k2 cs' x).
Definition KREL0r {R1 R2} (RR : R1 -> R2 -> Prop) (k1 : mstate -> M R1) (k2 : mstate -> M R2) : Prop :=
forall cs cs', cs' = rebase rho resv ceil cs -> strel RR (k1 cs) (k2 cs').
Definition BRELr {R1 R2} (RR : R1 -> R2 -> Prop) (b1 : M R1) (b2 : M R2) : Prop := strel RR b1 b2.
End RELS.

Ltac rcsimp := cbn -[strip rebase
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

Global Set Keyed Unification.
Ltac rrw := autorewrite with reb_rw.

Ltac reb_out1 :=
first
[ rewrite rebase_hdr_havoc | rewrite rebase_wr8 | rewrite rebase_set_tick
| rewrite rebase_dequeue | rewrite rebase_step_seq | rewrite rebase_record_seq
| rewrite rebase_account_bounce | rewrite rebase_decay_bounces | rewrite rebase_drop_region
| rewrite rebase_del_slots | rewrite rebase_add_slots | rewrite rebase_del_group
| rewrite rebase_set_group_active_idx | rewrite rebase_put_group
| rewrite rebase_set_head | rewrite rebase_set_active | rewrite rebase_set_usage | rewrite rebase_set_bounce
| rewrite rebase_upd_meta | rewrite rebase_put_meta | rewrite rebase_set_areas | rewrite rebase_upd_ctx ].
Ltac rsolve_eq := repeat reb_out1; reflexivity.
Ltac ruse_hyp :=
match goal with
| H : _ |- strel _ _ _ =>
with_strategy opaque [am_take am_carve am_finish am_after_brk alloc_meta ta_fin try_avail ag_tail
alloc_group alloc_slot malloc_small_ctrl malloc_core
nontrivial_free free_group free_tail free_hdr queue free_meta activate_group
enframe_read_off enframe_full]
(eapply H); (try assumption); (try rsolve_eq)
end.
Ltac rnot_numeric T :=
lazymatch T with Z => fail | bool => fail | N => fail | nat => fail | (Z * Z)%type => fail | _ => idtac end.
Ltac rscrut x :=
match x with
| context [if ?c then ?a else _] => let T := type of a in rnot_numeric T; rscrut c
| context [match ?y with _ => _ end] => let T := type of y in (lazymatch T with bool => fail | _ => idtac end); rscrut y
| _ => destruct x eqn:?
end.
Ltac rsync1 :=
first
[ lazymatch goal with
| |- strel _ _ _ => fail
| |- _ = _ => rsolve_eq
| |- _ => progress (hnf; intros);
try match goal with H : ?c = rebase _ _ _ _ |- _ => is_var c; subst c end
end
| lazymatch goal with
| |- strel _ (SRet _) (SRet _) => constructor
| |- strel _ (SVis _ _) (SVis _ _) => constructor; intros ?
| |- strel _ (if ?c then _ else _) _ => rscrut c
| |- strel _ (match ?x with _ => _ end) _ => rscrut x
| |- strel _ _ _ => ruse_hyp
end
| match goal with |- ?g => rscrut g end ].
Ltac rsync := rcsimp; rrw; repeat (rsync1; rcsimp; rrw).

Section CPSR.
Variables (rho : N -> Z) (resv : list (Z * Z)). Context {ceil : Z}.
Context {R1 R2 : Type} (RR : R1 -> R2 -> Prop).
Local Notation KRELr := (KRELr rho resv (ceil:=ceil)).
Local Notation KREL0r := (KREL0r rho resv (ceil:=ceil)).
Local Notation RB := (rebase rho resv ceil).

#[using="Type"] Lemma queue_reb h m k1 k2 b1 b2 :
KREL0r RR k1 k2 -> BRELr RR b1 b2 ->
forall cs cs', cs' = RB cs -> strel RR (queue h m cs k1 b1) (queue h m cs' k2 b2).
Proof. intros HK HB cs cs' ->. unfold queue, guard. rsync. Qed.

#[using="Type"] Lemma free_meta_reb m k1 k2 b1 b2 :
KREL0r RR k1 k2 -> BRELr RR b1 b2 ->
forall cs cs', cs' = RB cs -> strel RR (free_meta m cs k1 b1) (free_meta m cs' k2 b2).
Proof. intros HK HB cs cs' ->. unfold free_meta. eapply queue_reb; eauto. Qed.

#[using="Type"] Lemma activate_group_reb m k1 k2 b1 b2 :
KRELr RR k1 k2 -> BRELr RR b1 b2 ->
forall cs cs', cs' = RB cs -> strel RR (activate_group m cs k1 b1) (activate_group m cs' k2 b2).
Proof. intros HK HB cs cs' ->. unfold activate_group, guard. rsync. Qed.

#[using="Type"] Lemma ta_fin_reb m mask k1 k2 :
KRELr RR k1 k2 ->
forall cs cs', cs' = RB cs -> strel RR (ta_fin cs m mask k1) (ta_fin cs' m mask k2).
Proof. intros HK cs cs' ->. unfold ta_fin. rsync. Qed.

#[using="Type"] Lemma try_avail_reb sc k1 k2 b1 b2 :
KRELr RR k1 k2 -> BRELr RR b1 b2 ->
forall cs cs', cs' = RB cs -> strel RR (try_avail sc cs k1 b1) (try_avail sc cs' k2 b2).
Proof.
intros HK HB cs cs' ->. pose proof (ta_fin_reb) as HF. pose proof (activate_group_reb) as HA.
unfold try_avail, guard. rsync.
Qed.

Definition DRELr {X1 X2} (XX : X1 -> X2 -> Prop) (dec1 : decoder X1) (dec2 : decoder X2) : Prop :=
forall p k1 k2 b1 b2,
(forall m idx, strel XX (k1 m idx) (k2 m idx)) ->
BRELr XX b1 b2 ->
forall cs cs', cs' = RB cs -> strel XX (dec1 cs p k1 b1) (dec2 cs' p k2 b2).

#[using="Type"] Lemma dec_slots_drelr : DRELr RR (@dec_slots R1) (@dec_slots R2).
Proof.
intros p k1 k2 b1 b2 HK HB cs cs' ->. unfold dec_slots. rrw.
destruct (s_slots cs !! p) as [[m idx]|]; [apply HK | rsync].
Qed.

#[using="Type"] Lemma free_group_reb (dec1 : decoder R1) (dec2 : decoder R2) rec1 rec2 g k1 k2 b1 b2 :
DRELr RR dec1 dec2 ->
(forall g' i' k1' k2' b1' b2', KRELr RR k1' k2' -> BRELr RR b1' b2' ->
forall cs cs', cs' = RB cs -> strel RR (rec1 cs g' i' k1' b1') (rec2 cs' g' i' k2' b2')) ->
KRELr RR k1 k2 -> BRELr RR b1 b2 ->
forall cs cs', cs' = RB cs ->
strel RR (free_group R1 dec1 rec1 cs g k1 b1) (free_group R2 dec2 rec2 cs' g k2 b2).
Proof.
intros HD HR HK HB cs cs' ->. pose proof (free_meta_reb) as HF.
unfold free_group. rsync.
all: try (eapply HD; [ intros ? ? | assumption | rsolve_eq ]; rsync).
Qed.

#[using="Type"] Lemma nontrivial_free_reb (dec1 : decoder R1) (dec2 : decoder R2) (HD : DRELr RR dec1 dec2) fuel :
forall g i k1 k2 b1 b2,
KRELr RR k1 k2 -> BRELr RR b1 b2 ->
forall cs cs', cs' = RB cs ->
strel RR (nontrivial_free dec1 fuel cs g i k1 b1) (nontrivial_free dec2 fuel cs' g i k2 b2).
Proof.
induction fuel as [|f IH]; intros g i k1 k2 b1 b2 HK HB cs cs' ->.
{ cbn [nontrivial_free]. rsync. }
pose proof (free_group_reb dec1 dec2 (nontrivial_free dec1 f) (nontrivial_free dec2 f) g) as HG.
pose proof (activate_group_reb) as HA. pose proof (queue_reb) as HQ.
cbn [nontrivial_free]. unfold guard. rsync.
Qed.
End CPSR.

Definition RC (rho : N -> Z) (resv : list (Z * Z)) (ceil : Z) (sG sC : mstate) : Prop :=
strip sC = rebase rho resv ceil (strip sG).

Section RC_FACTS.
Variables (rho : N -> Z) (resv : list (Z * Z)). Context {ceil : Z}.
Local Notation RB := (rebase rho resv ceil).
Local Notation RCr := (RC rho resv ceil).
Implicit Types sG sC : mstate.

#[using="Type"] Lemma RC_strip sG sC : RCr sG sC <-> RCr (strip sG) (strip sC).
Proof. unfold RC. rewrite !strip_strip. tauto. Qed.

#[using="Type"] Lemma RC_ctx sG sC : RCr sG sC -> s_ctx sC = s_ctx sG. Proof. intros H. apply (f_equal s_ctx) in H. exact H. Qed.
#[using="Type"] Lemma RC_metas sG sC : RCr sG sC -> s_metas sC = s_metas sG. Proof. intros H. apply (f_equal s_metas) in H. exact H. Qed.
#[using="Type"] Lemma RC_areas sG sC : RCr sG sC -> s_areas sC = s_areas sG. Proof. intros H. apply (f_equal s_areas) in H. exact H. Qed.
#[using="Type"] Lemma RC_groups sG sC : RCr sG sC -> s_groups sC = s_groups sG. Proof. intros H. apply (f_equal s_groups) in H. exact H. Qed.
#[using="Type"] Lemma RC_slots sG sC : RCr sG sC -> s_slots sC = s_slots sG. Proof. intros H. apply (f_equal s_slots) in H. exact H. Qed.
#[using="Type"] Lemma RC_next_rid sG sC : RCr sG sC -> s_next_rid sC = s_next_rid sG. Proof. intros H. apply (f_equal s_next_rid) in H. exact H. Qed.
#[using="Type"] Lemma RC_secret sG sC : RCr sG sC -> s_secret sC = s_secret sG. Proof. intros H. apply (f_equal s_secret) in H. exact H. Qed.
#[using="Type"] Lemma RC_reserved sG sC : RCr sG sC -> s_reserved sC = resv. Proof. intros H. apply (f_equal s_reserved) in H. exact H. Qed.
#[using="Type"] Lemma RC_regions sG sC : RCr sG sC -> s_regions sC = rebase_regions rho (s_regions sG).
Proof. intros H. apply (f_equal s_regions) in H. exact H. Qed.
#[using="Type"] Lemma RC_region sG sC rid : RCr sG sC -> s_regions sC !! rid = option_map (rebase_region rho rid) (s_regions sG !! rid).
Proof. intros H. rewrite (RC_regions _ _ H). apply lookup_rebase_regions. Qed.
#[using="Type"] Lemma RC_MRc sG sC m : RCr sG sC -> get_meta_rec sC m = get_meta_rec sG m.
Proof. intros H. unfold get_meta_rec. rewrite (RC_metas _ _ H). reflexivity. Qed.
#[using="Type"] Lemma RC_active sG sC sc : RCr sG sC -> active sC sc = active sG sc.
Proof. intros H. unfold active, ctx. rewrite (RC_ctx _ _ H). reflexivity. Qed.
#[using="Type"] Lemma RC_usage sG sC sc : RCr sG sC -> usage sC sc = usage sG sc.
Proof. intros H. unfold usage, ctx. rewrite (RC_ctx _ _ H). reflexivity. Qed.
#[using="Type"] Lemma RC_get_head sG sC h : RCr sG sC -> get_head sC h = get_head sG h.
Proof. intros H. destruct h; cbn; [apply RC_active; exact H| unfold ctx; rewrite (RC_ctx _ _ H); reflexivity]. Qed.
#[using="Type"] Lemma RC_conc sG sC p : RCr sG sC ->
conc sC p = match s_regions sG !! fst p with Some _ => rho (fst p) + snd p | None => 0 end.
Proof. intros H. unfold conc, get_region. rewrite (RC_region _ _ _ H). destruct (s_regions sG !! fst p); reflexivity. Qed.

#[using="Type"] Lemma RC_layout sG sC sG' sC' : RCr sG sC -> strip sG' = strip sG -> strip sC' = strip sC -> RCr sG' sC'.
Proof. unfold RC. intros H -> ->. exact H. Qed.

#[using="Type"] Lemma RC_lift (U : mstate -> mstate) sG sC :
(forall s, U (strip s) = strip (U s)) -> (forall cs, U (RB cs) = RB (U cs)) -> RCr sG sC -> RCr (U sG) (U sC).
Proof. intros HS HR H. unfold RC in *. rewrite <- !HS, H, HR. reflexivity. Qed.

#[using="Type"] Lemma RC_upd_ctx f sG sC : RCr sG sC -> RCr (upd_ctx f sG) (upd_ctx f sC). Proof. apply RC_lift; reflexivity. Qed.
#[using="Type"] Lemma RC_upd_meta m f sG sC : RCr sG sC -> RCr (upd_meta m f sG) (upd_meta m f sC). Proof. apply RC_lift; reflexivity. Qed.
#[using="Type"] Lemma RC_put_meta m r sG sC : RCr sG sC -> RCr (put_meta m r sG) (put_meta m r sC). Proof. apply RC_lift; reflexivity. Qed.
#[using="Type"] Lemma RC_set_active sc v sG sC : RCr sG sC -> RCr (set_active sc v sG) (set_active sc v sC). Proof. apply RC_lift; reflexivity. Qed.
#[using="Type"] Lemma RC_set_head h v sG sC : RCr sG sC -> RCr (set_head h v sG) (set_head h v sC).
Proof. apply RC_lift; [apply strip_set_head| apply rebase_set_head]. Qed.
#[using="Type"] Lemma RC_set_usage sc v sG sC : RCr sG sC -> RCr (set_usage sc v sG) (set_usage sc v sC). Proof. apply RC_lift; reflexivity. Qed.
#[using="Type"] Lemma RC_set_bounce i v sG sC : RCr sG sC -> RCr (set_bounce i v sG) (set_bounce i v sC). Proof. apply RC_lift; reflexivity. Qed.
#[using="Type"] Lemma RC_set_areas a sG sC : RCr sG sC -> RCr (set_areas a sG) (set_areas a sC). Proof. apply RC_lift; reflexivity. Qed.
#[using="Type"] Lemma RC_put_group g m ai sG sC : RCr sG sC -> RCr (put_group g m ai sG) (put_group g m ai sC). Proof. apply RC_lift; reflexivity. Qed.
#[using="Type"] Lemma RC_set_group_active_idx g ai sG sC : RCr sG sC -> RCr (set_group_active_idx g ai sG) (set_group_active_idx g ai sC).
Proof. apply RC_lift; [apply strip_set_group_active_idx| apply rebase_set_group_active_idx]. Qed.
#[using="Type"] Lemma RC_del_group g sG sC : RCr sG sC -> RCr (del_group g sG) (del_group g sC). Proof. apply RC_lift; reflexivity. Qed.
#[using="Type"] Lemma RC_add_slots m p s c sG sC : RCr sG sC -> RCr (add_slots m p s c sG) (add_slots m p s c sC). Proof. apply RC_lift; reflexivity. Qed.
#[using="Type"] Lemma RC_del_slots p s c sG sC : RCr sG sC -> RCr (del_slots p s c sG) (del_slots p s c sC). Proof. apply RC_lift; reflexivity. Qed.
#[using="Type"] Lemma RC_drop_region rid sG sC : RCr sG sC -> RCr (drop_region rid sG) (drop_region rid sC).
Proof. apply RC_lift; [apply strip_drop_region| apply rebase_drop_region]. Qed.
#[using="Type"] Lemma RC_step_seq sG sC : RCr sG sC -> RCr (step_seq sG) (step_seq sC).
Proof. apply RC_lift; [apply strip_step_seq| apply rebase_step_seq]. Qed.
#[using="Type"] Lemma RC_record_seq sc sG sC : RCr sG sC -> RCr (record_seq sc sG) (record_seq sc sC).
Proof. apply RC_lift; [apply strip_record_seq| apply rebase_record_seq]. Qed.
#[using="Type"] Lemma RC_account_bounce sc sG sC : RCr sG sC -> RCr (account_bounce sc sG) (account_bounce sc sC).
Proof. apply RC_lift; [apply strip_account_bounce| apply rebase_account_bounce]. Qed.
#[using="Type"] Lemma RC_decay_bounces sc sG sC : RCr sG sC -> RCr (decay_bounces sc sG) (decay_bounces sc sC).
Proof. apply RC_lift; [apply strip_decay_bounces| apply rebase_decay_bounces]. Qed.
#[using="Type"] Lemma RC_dequeue h m sG sC : RCr sG sC -> RCr (dequeue h m sG) (dequeue h m sC).
Proof. apply RC_lift; [apply strip_dequeue| apply rebase_dequeue]. Qed.
#[using="Type"] Lemma RC_upd_region rid f sG sC : (forall r, f (rebase_region rho rid r) = rebase_region rho rid (f r)) ->
RCr sG sC -> RCr (upd_region rid f sG) (upd_region rid f sC).
Proof. intros Hf. apply RC_lift; [apply strip_upd_region| intros cs; apply rebase_upd_region; exact Hf]. Qed.
#[using="Type"] Lemma RC_set_tick t t' sG sC : RCr sG sC -> RCr (set_tick t sG) (set_tick t' sC).
Proof. intros H. eapply RC_layout; [exact H| apply strip_set_tick| apply strip_set_tick]. Qed.

#[using="Type"] Lemma RC_new_region k bG bC l sG sC : RCr sG sC ->
RC (nupd rho (s_next_rid sG) bC) resv ceil (fst (new_region k bG l sG)) (fst (new_region k bC l sC))
/\ snd (new_region k bC l sC) = snd (new_region k bG l sG).
Proof.
intros H. unfold RC in *.
change (strip (fst (new_region k bC l sC))) with (fst (new_region k bC l (strip sC))).
rewrite H, (rebase_new_region rho resv k bC l (strip sG) bG). cbn [fst snd].
split; [reflexivity|]. change ((new_region k bC l (strip sC)).2 = (new_region k bG l sG).2). rewrite H. reflexivity.
Qed.
End RC_FACTS.

Definition kP {X Y : Type} : X -> Y -> M (option (X * Y)) := fun x y => SRet (Some (x, y)).
Definition bP {T : Type} : M (option T) := SRet None.

Section LIFT.
Variables (rho : N -> Z) (resv : list (Z * Z)). Context {ceil : Z}.
Local Notation RB := (rebase rho resv ceil).
Local Notation RCr := (RC rho resv ceil).

Definition pz (_ : unit) (_ : aptr) (_ _ : Z) : Z := 0.
Definition pu (o : unit) (_ : ev) (_ : Z) : unit := o.

Definition simg {Y} (x : unit * option (mstate * Y)) (y : option (mstate * Y)) : Prop :=
y = match snd x with Some (s, v) => Some (strip s, v) | None => None end.
Definition rimg {Y} (x : option (mstate * Y)) (y : option (mstate * Y)) : Prop :=
y = match x with Some (s, v) => Some (RB s, v) | None => None end.

#[using="Type"] Lemma strel_ret_inv {E A R1 R2} (RR : R1 -> R2 -> Prop) (x : R1) (t : stree E A R2) :
strel RR (SRet x) t -> exists y, t = SRet y /\ RR x y.
Proof. intros H. inversion H; subst. eexists; split; [reflexivity| assumption]. Qed.
#[using="Type"] Lemma strel_ret_inv_r {E A R1 R2} (RR : R1 -> R2 -> Prop) (t : stree E A R1) (y : R2) :
strel RR t (SRet y) -> exists x, t = SRet x /\ RR x y.
Proof. intros H. inversion H; subst. eexists; split; [reflexivity| assumption]. Qed.

#[using="Type"] Lemma KREL_kP {Y} : KREL pz pu (@simg Y) kP kP.
Proof. intros o st cst x ->. unfold kP, prun. cbn. constructor. reflexivity. Qed.
#[using="Type"] Lemma BREL_bP {Y} : BREL pz pu (@simg Y) bP bP.
Proof. unfold BREL, bP, prun. cbn. constructor. reflexivity. Qed.
#[using="Type"] Lemma KRELr_kP {Y} : KRELr rho resv (ceil:=ceil) (@rimg Y) kP kP.
Proof. intros cs cs' x ->. unfold kP. constructor. reflexivity. Qed.
#[using="Type"] Lemma BRELr_bP {Y} : BRELr (@rimg Y) bP bP.
Proof. unfold BRELr, bP. constructor. reflexivity. Qed.

#[using="Type"] Lemma SRet_pair_inj {E A S Y} (a b : S) (x y : Y) : @SRet E A _ (Some (a, x)) = SRet (Some (b, y)) -> a = b /\ x = y.
Proof. intros H. injection H. auto. Qed.

#[using="Type"] Lemma chain_RC {Y} (tG tC : M (option (mstate * Y))) (tGc tCc : M (option (mstate * Y))) sG1 sC1 (x x' : Y) :
strel simg (prun pz pu tt tG) tGc -> strel rimg tGc tCc -> strel simg (prun pz pu tt tC) tCc ->
tG = SRet (Some (sG1, x)) -> tC = SRet (Some (sC1, x')) -> x' = x /\ RCr sG1 sC1.
Proof.
intros S1 S2 S3 -> ->. unfold prun in S1, S3. cbn in S1, S3.
apply strel_ret_inv in S1 as (y1 & -> & R1). unfold simg in R1. cbn in R1. subst y1.
apply strel_ret_inv in S2 as (y2 & -> & R2). unfold rimg in R2. subst y2.
apply strel_ret_inv in S3 as (y3 & E3 & R3). unfold simg in R3. cbn in R3. subst y3.
apply SRet_pair_inj in E3 as [E4 E5]. split; [symmetry; exact E5|]. unfold RC. symmetry. exact E4.
Qed.

#[using="Type"] Theorem try_avail_RC sG sC sc sG1 sC1 (f f' : Z) :
RCr sG sC -> try_avail sc sG kP bP = SRet (Some (sG1, f)) -> try_avail sc sC kP bP = SRet (Some (sC1, f')) ->
f' = f /\ RCr sG1 sC1.
Proof.
intros H EG EC.
eapply (chain_RC (try_avail sc sG kP bP) (try_avail sc sC kP bP) (try_avail sc (strip sG) kP bP) (try_avail sc (strip sC) kP bP)); [| | | exact EG| exact EC].
- apply (try_avail_ctrl pz pu simg); [apply KREL_kP| apply BREL_bP| reflexivity].
- apply (try_avail_reb rho resv (ceil:=ceil) rimg); [apply KRELr_kP| apply BRELr_bP| exact H].
- apply (try_avail_ctrl pz pu simg); [apply KREL_kP| apply BREL_bP| reflexivity].
Qed.

#[using="Type"] Theorem nontrivial_free_RC fuel sG sC g i sG1 sC1 (mi mi' : mapinfo) :
RCr sG sC -> nontrivial_free dec_slots fuel sG g i kP bP = SRet (Some (sG1, mi)) ->
nontrivial_free dec_slots fuel sC g i kP bP = SRet (Some (sC1, mi')) ->
mi' = mi /\ RCr sG1 sC1.
Proof.
intros H EG EC.
eapply (chain_RC (nontrivial_free dec_slots fuel sG g i kP bP) (nontrivial_free dec_slots fuel sC g i kP bP)
(nontrivial_free dec_slots fuel (strip sG) g i kP bP) (nontrivial_free dec_slots fuel (strip sC) g i kP bP)); [| | | exact EG| exact EC].
- apply (nontrivial_free_ctrl pz pu simg dec_slots dec_slots (dec_slots_drel pz pu simg)); [apply KREL_kP| apply BREL_bP| reflexivity].
- apply (nontrivial_free_reb rho resv (ceil:=ceil) rimg dec_slots dec_slots (dec_slots_drelr rho resv (ceil:=ceil) rimg)); [apply KRELr_kP| apply BRELr_bP| exact H].
- apply (nontrivial_free_ctrl pz pu simg dec_slots dec_slots (dec_slots_drel pz pu simg)); [apply KREL_kP| apply BREL_bP| reflexivity].
Qed.
End LIFT.
