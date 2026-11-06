(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc.

(* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Open Scope Z_scope.
Local Open Scope stree_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_MallocCtrl () : Init.string Init.list := ["KREL0"; "BREL"; "OSSVerify.KrLib.Heap.Malloc.mstate"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Heap.Malloc.strip"; "OSSVerify.KrLib.Heap.STree.strel"; "OSSVerify.KrLib.Heap.Malloc.ev"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.prod"; "prun"; "OSSVerify.KrLib.Heap.Malloc.queue"; "OSSVerify.KrLib.Heap.Malloc.free_meta"; "KREL"; "OSSVerify.KrLib.Heap.Malloc.activate_group"; "OSSVerify.KrLib.Heap.Malloc.optr"; "OSSVerify.KrLib.Heap.Malloc.am_take"; "OSSVerify.KrLib.Heap.Malloc.am_carve"; "OSSVerify.KrLib.Heap.Malloc.am_finish"; "OSSVerify.KrLib.Heap.Malloc.am_after_brk"; "OSSVerify.KrLib.Heap.Malloc.alloc_meta"; "OSSVerify.KrLib.Heap.Malloc.ta_fin"; "OSSVerify.KrLib.Heap.Malloc.try_avail"; "OSSVerify.KrLib.Heap.Malloc.ag_tail"; "OSSVerify.KrLib.Heap.Malloc.full_lay"; "OSSVerify.KrLib.Heap.Malloc.lay_none"; "OSSVerify.KrLib.Heap.Malloc.M"; "OSSVerify.KrLib.Heap.Malloc.alloc_group"; "OSSVerify.KrLib.Heap.Malloc.alloc_slot"; "CPS.DREL"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "OSSVerify.KrLib.Heap.Malloc.mapinfo"; "OSSVerify.KrLib.Heap.Malloc.free_group"; "OSSVerify.KrLib.Heap.Malloc.nontrivial_free"; "Corelib.Init.Datatypes.option"; "TOP.CREL"; "OSSVerify.KrLib.Heap.Malloc.malloc_core"; "Corelib.Init.Logic.or"; "Corelib.Init.Datatypes.snd"; "OSSVerify.KrLib.Heap.Malloc.enframe_at"; "OSSVerify.KrLib.Heap.Malloc.slot_of"; "OSSVerify.KrLib.Heap.Malloc.aadd"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Heap.Malloc.UNIT"; "DREL"; "OSSVerify.KrLib.Heap.Malloc.free_tail"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "OSSVerify.KrLib.Heap.Malloc.free_hdr"; "OSSVerify.KrLib.Heap.STree.SRet"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.Some"; "stdpp.base.lookup"; "OSSVerify.KrLib.Heap.Malloc.cptr"; "stdpp.gmap.gmap"; "stdpp.decidable.prod_eq_dec"; "Corelib.Numbers.BinNums.N"; "stdpp.numbers.N.eq_dec"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.N_countable"; "stdpp.countable.Z_countable"; "stdpp.gmap.gmap_lookup"; "OSSVerify.KrLib.Heap.Malloc.s_slots"; "OSSVerify.KrLib.Heap.Malloc.dec_hdr"; "OSSVerify.KrLib.Heap.Malloc.dec_slots"; "TOP.hdr_ok"; "TOP.FREL"; "OSSVerify.KrLib.Heap.Malloc.free"; "OSSVerify.KrLib.Heap.Malloc.cfree"].


Section ORACLE.
Context {O : Type}.
Variable pans : O -> aptr -> Z -> Z -> Z.     (* [comment removed for export] *)
Variable pupd : O -> ev -> Z -> O.            (* [comment removed for export] *)

Definition psel (o : O) (e : ev) : option Z :=
  match e with EPeek p c h => Some (pans o p c h) | _ => None end.
Definition prun {R} (o : O) (t : M R) : M (O * R) := eruns psel pupd o t.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ctx_strip st : ctx (strip st) = ctx st. Proof. reflexivity. Qed.
Lemma s_ctx_strip st : s_ctx (strip st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_regions_strip st : s_regions (strip st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_metas_strip st : s_metas (strip st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_strip st : s_areas (strip st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_strip st : s_groups (strip st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_slots_strip st : s_slots (strip st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_next_rid_strip st : s_next_rid (strip st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_secret_strip st : s_secret (strip st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_canary_strip st : s_canary (strip st) = s_canary st. Proof. reflexivity. Qed.
Lemma s_ceil_strip st : s_ceil (strip st) = s_ceil st. Proof. reflexivity. Qed.
Lemma s_ceil_raw_strip st : s_ceil_raw (strip st) = s_ceil_raw st. Proof. reflexivity. Qed.
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
Lemma brk_pages_ok_strip st lo len : brk_pages_ok (strip st) lo len = brk_pages_ok st lo len. Proof. reflexivity. Qed.  (* [comment removed for export] *)
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
  s_next_rid_strip s_secret_strip s_canary_strip s_ceil_strip s_ceil_raw_strip s_reserved_strip active_strip usage_strip unmap_seq_strip bounces_strip
  get_meta_rec_strip get_group_strip group_active_idx_strip get_region_strip conc_strip live_ranges_strip brk_pages_ok_strip
  get_head_strip is_bouncing_strip okay_to_free_strip slot_of_strip
  strip_upd_ctx strip_upd_meta strip_put_meta strip_set_active strip_set_head strip_set_usage strip_set_bounce
  strip_set_areas strip_put_group strip_set_group_active_idx strip_del_group strip_add_slots strip_del_slots
  strip_drop_region strip_new_region strip_upd_region strip_step_seq strip_record_seq strip_account_bounce
  strip_decay_bounces strip_dequeue
  strip_strip strip_wr8 strip_wr16 strip_wr32 strip_havoc strip_set_tick strip_zero_hdrs strip_set_size strip_nest_layout strip_hdr_havoc
  : strip_rw.
(* [comment removed for export] *)
Hint Rewrite <- strip_upd_ctx strip_upd_meta strip_put_meta strip_set_active strip_set_head strip_set_usage strip_set_bounce
  strip_set_areas strip_put_group strip_set_group_active_idx strip_del_group strip_add_slots strip_del_slots
  strip_drop_region strip_upd_region strip_step_seq strip_record_seq strip_account_bounce
  strip_decay_bounces strip_dequeue : strip_in.
Hint Rewrite strip_strip strip_wr8 strip_wr16 strip_wr32 strip_havoc strip_set_tick strip_zero_hdrs strip_set_size
  strip_nest_layout strip_enframe_at strip_hdr_havoc : strip_in.

(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac csimp := cbn -[strip
   (* [comment removed for export] *) ctx active usage unmap_seq bounces get_meta_rec get_group group_active_idx get_region conc oconc
                   live_ranges brk_pages_ok get_head is_bouncing okay_to_free slot_of get_shadow
                   s_ctx s_regions s_shadow s_metas s_areas s_groups s_slots s_next_rid s_tick s_secret s_canary s_ceil s_ceil_raw s_reserved
   (* [comment removed for export] *)   upd_ctx set_active set_head set_usage set_bounce put_meta upd_meta put_group set_group_active_idx
                   set_areas set_metas set_groups set_slots set_regions set_shadow set_next_rid set_tick
                   new_region drop_region del_group add_slots del_slots upd_region upd_shadow wr8 wr16 wr32 havoc hdr_havoc
                   step_seq record_seq account_bounce decay_bounces dequeue nest_layout enframe_at set_size zero_hdrs
   (* [comment removed for export] *) am_take am_carve am_finish am_after_brk alloc_meta ta_fin try_avail ag_tail alloc_group alloc_slot
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

(* [comment removed for export] *)
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
(* [comment removed for export] *)
Ltac use_hyp :=
  match goal with
  | H : _ |- strel _ _ _ =>
      with_strategy opaque [am_take am_carve am_finish am_after_brk alloc_meta ta_fin try_avail ag_tail
                            alloc_group alloc_slot malloc_small_ctrl malloc_core
                            nontrivial_free free_group free_tail free_hdr queue free_meta activate_group
                            enframe_read_off enframe_full]
        (eapply H); (try assumption); (try solve_eq)
  end.
(* [comment removed for export] *)
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
    | |- _ = _ => solve_eq                (* [comment removed for export] *)
    | |- _ => progress (hnf; intros);    (* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CPS.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Context {R1 R2 : Type} (RR : O * R1 -> R2 -> Prop).
Local Notation KREL := (KREL pans pupd).
Local Notation KREL0 := (KREL0 pans pupd).
Local Notation BREL := (BREL pans pupd).
Local Notation prun := (prun pans pupd).

#[using="Type"] Lemma queue_ctrl h m k1 k2 b1 b2 : ltac2:(CDefT.buildp (gd_tbl_MallocCtrl ()) "P,(0.VO,Vpans,Vpupd,VR1,VR2,VRR,O4.O3.)P,(1.VO,Vpans,Vpupd,VR1,VR2,VRR,O2.O1.)Po,VO,Pst,$2.Pcst,$2.P,(3.$2.R1.(4.R2.))(5.$6.$7.(8.VO,VR1,)VR2,VRR,(9.VO,Vpans,Vpupd,VR1,R4.(:.VR1,O6.O5.R3.O4.O2.))(:.VR2,O6.O5.R2.O3.O1.))")
(* [comment removed for export] *).
Proof. intros HK HB o st cst ->. unfold queue, guard. sync. Qed.

#[using="Type"] Lemma free_meta_ctrl m k1 k2 b1 b2 : ltac2:(CDefT.buildp (gd_tbl_MallocCtrl ()) "P,(0.VO,Vpans,Vpupd,VR1,VR2,VRR,O4.O3.)P,(1.VO,Vpans,Vpupd,VR1,VR2,VRR,O2.O1.)Po,VO,Pst,$2.Pcst,$2.P,(3.$2.R1.(4.R2.))(5.$6.$7.(8.VO,VR1,)VR2,VRR,(9.VO,Vpans,Vpupd,VR1,R4.(;.VR1,O5.R3.O4.O2.))(;.VR2,O5.R2.O3.O1.))")
(* [comment removed for export] *).
Proof. intros HK HB o st cst ->. unfold free_meta. eapply queue_ctrl; eauto. Qed.

#[using="Type"] Lemma activate_group_ctrl m k1 k2 b1 b2 : ltac2:(CDefT.buildp (gd_tbl_MallocCtrl ()) "P,(<.VO,Vpans,Vpupd,$7.VR1,VR2,VRR,O4.O3.)P,(1.VO,Vpans,Vpupd,VR1,VR2,VRR,O2.O1.)Po,VO,Pst,$2.Pcst,$2.P,(3.$2.R1.(4.R2.))(5.$6.$7.(8.VO,VR1,)VR2,VRR,(9.VO,Vpans,Vpupd,VR1,R4.(=.VR1,O5.R3.O4.O2.))(=.VR2,O5.R2.O3.O1.))")
(* [comment removed for export] *).
Proof. intros HK HB o st cst ->. unfold activate_group, guard. sync. Qed.

#[using="Type"] Lemma am_take_ctrl k1 k2 b1 b2 : ltac2:(CDefT.buildp (gd_tbl_MallocCtrl ()) "P,(<.VO,Vpans,Vpupd,$>.VR1,VR2,VRR,O4.O3.)P,(1.VO,Vpans,Vpupd,VR1,VR2,VRR,O2.O1.)Po,VO,Pst,$2.Pcst,$2.P,(3.$2.R1.(4.R2.))(5.$6.$7.(8.VO,VR1,)VR2,VRR,(9.VO,Vpans,Vpupd,VR1,R4.(?.VR1,R3.O4.O2.))(?.VR2,R2.O3.O1.))")
(* [comment removed for export] *).
Proof. intros HK HB o st cst ->. unfold am_take. sync. Qed.

#[using="Type"] Lemma am_carve_ctrl p k1 k2 b1 b2 : ltac2:(CDefT.buildp (gd_tbl_MallocCtrl ()) "P,(<.VO,Vpans,Vpupd,$>.VR1,VR2,VRR,O4.O3.)P,(1.VO,Vpans,Vpupd,VR1,VR2,VRR,O2.O1.)Po,VO,Pst,$2.Pcst,$2.P,(3.$2.R1.(4.R2.))(5.$6.$7.(8.VO,VR1,)VR2,VRR,(9.VO,Vpans,Vpupd,VR1,R4.(10.VR1,R3.O5.O4.O2.))(10.VR2,R2.O5.O3.O1.))")
(* [comment removed for export] *).
Proof. intros HK HB o st cst ->. pose proof (am_take_ctrl k1 k2 b1 b2 HK HB) as HT. unfold am_carve. sync. Qed.

#[using="Type"] Lemma am_finish_ctrl nu k1 k2 b1 b2 : ltac2:(CDefT.buildp (gd_tbl_MallocCtrl ()) "P,(<.VO,Vpans,Vpupd,$>.VR1,VR2,VRR,O4.O3.)P,(1.VO,Vpans,Vpupd,VR1,VR2,VRR,O2.O1.)Po,VO,Pst,$2.Pcst,$2.P,(3.$2.R1.(4.R2.))(5.$6.$7.(8.VO,VR1,)VR2,VRR,(9.VO,Vpans,Vpupd,VR1,R4.(11.VR1,R3.O5.O4.O2.))(11.VR2,R2.O5.O3.O1.))")
(* [comment removed for export] *).
Proof. intros HK HB o st cst ->. pose proof (am_carve_ctrl) as HC. unfold am_finish, bad_answer. sync. Qed.

#[using="Type"] Lemma am_after_brk_ctrl nu k1 k2 b1 b2 : ltac2:(CDefT.buildp (gd_tbl_MallocCtrl ()) "P,(<.VO,Vpans,Vpupd,$>.VR1,VR2,VRR,O4.O3.)P,(1.VO,Vpans,Vpupd,VR1,VR2,VRR,O2.O1.)Po,VO,Pst,$2.Pcst,$2.P,(3.$2.R1.(4.R2.))(5.$6.$7.(8.VO,VR1,)VR2,VRR,(9.VO,Vpans,Vpupd,VR1,R4.(12.VR1,R3.O5.O4.O2.))(12.VR2,R2.O5.O3.O1.))")
(* [comment removed for export] *).
Proof. intros HK HB o st cst ->. pose proof (am_finish_ctrl) as HF. unfold am_after_brk, bad_answer. sync. Qed.

#[using="Type"] Lemma alloc_meta_ctrl k1 k2 b1 b2 : ltac2:(CDefT.buildp (gd_tbl_MallocCtrl ()) "P,(<.VO,Vpans,Vpupd,$>.VR1,VR2,VRR,O4.O3.)P,(1.VO,Vpans,Vpupd,VR1,VR2,VRR,O2.O1.)Po,VO,Pst,$2.Pcst,$2.P,(3.$2.R1.(4.R2.))(5.$6.$7.(8.VO,VR1,)VR2,VRR,(9.VO,Vpans,Vpupd,VR1,R4.(13.VR1,R3.O4.O2.))(13.VR2,R2.O3.O1.))")
(* [comment removed for export] *).
Proof.
  intros HK HB o st cst ->. pose proof (am_after_brk_ctrl) as HA. pose proof (am_take_ctrl k1 k2 b1 b2 HK HB) as HT.
  unfold alloc_meta, bad_answer. sync.
Qed.

#[using="Type"] Lemma ta_fin_ctrl m mask k1 k2 : ltac2:(CDefT.buildp (gd_tbl_MallocCtrl ()) "P,(<.VO,Vpans,Vpupd,$7.VR1,VR2,VRR,O2.O1.)Po,VO,Pst,$2.Pcst,$2.P,(3.$2.R1.(4.R2.))(5.$6.$7.(8.VO,VR1,)VR2,VRR,(9.VO,Vpans,Vpupd,VR1,R4.(14.VR1,R3.O4.O3.O2.))(14.VR2,R2.O4.O3.O1.))")
(* [comment removed for export] *).
Proof. intros HK o st cst ->. unfold ta_fin. sync. Qed.

#[using="Type"] Lemma try_avail_ctrl sc k1 k2 b1 b2 : ltac2:(CDefT.buildp (gd_tbl_MallocCtrl ()) "P,(<.VO,Vpans,Vpupd,$7.VR1,VR2,VRR,O4.O3.)P,(1.VO,Vpans,Vpupd,VR1,VR2,VRR,O2.O1.)Po,VO,Pst,$2.Pcst,$2.P,(3.$2.R1.(4.R2.))(5.$6.$7.(8.VO,VR1,)VR2,VRR,(9.VO,Vpans,Vpupd,VR1,R4.(15.VR1,O5.R3.O4.O2.))(15.VR2,O5.R2.O3.O1.))")
(* [comment removed for export] *).
Proof.
  intros HK HB o st cst ->. pose proof (ta_fin_ctrl) as HF. pose proof (activate_group_ctrl) as HA.
  unfold try_avail, guard. sync.
Qed.

#[using="Type"] Lemma ag_tail_ctrl sc m p cnt ai k1 k2 : ltac2:(CDefT.buildp (gd_tbl_MallocCtrl ()) "P,(<.VO,Vpans,Vpupd,$>.VR1,VR2,VRR,O2.O1.)Po,VO,Pst,$2.Pcst,$2.P,(3.$2.R1.(4.R2.))(5.$6.$7.(8.VO,VR1,)VR2,VRR,(9.VO,Vpans,Vpupd,VR1,R4.(16.VR1,$17.R3.O7.O6.O5.O4.O3.O2.))(16.VR2,$18.R2.O7.O6.O5.O4.O3.O1.))")
(* [comment removed for export] *).
Proof. intros HK o st cst ->. unfold ag_tail. cbn [lh_hdr full_lay lay_none]. rewrite <- (strip_hdr_havoc p st). sync.
Qed.

#[using="Type"] Lemma alloc_group_ctrl rec1 rec2 sc req k1 k2 b1 b2 : ltac2:(CDefT.buildp (gd_tbl_MallocCtrl ()) "P,Psc',$7.Preq',$7.Pk1',P,$2.P,$7.(19.VR1,)Pk2',P,$2.P,$7.(19.VR2,)Pb1',(19.VR1,)Pb2',(19.VR2,)P,(<.VO,Vpans,Vpupd,$7.VR1,VR2,VRR,R4.R3.)P,(1.VO,Vpans,Vpupd,VR1,VR2,VRR,R3.R2.)Po,VO,Pst,$2.Pcst,$2.P,(3.$2.R1.(4.R2.))(5.$6.$7.(8.VO,VR1,)VR2,VRR,(9.VO,Vpans,Vpupd,VR1,R4.A5.O8.R3.R<.R;.R:.R8.)A5.O7.R2.R<.R;.R9.R7.)P,(<.VO,Vpans,Vpupd,$>.VR1,VR2,VRR,O4.O3.)P,(1.VO,Vpans,Vpupd,VR1,VR2,VRR,O2.O1.)Po,VO,Pst,$2.Pcst,$2.P,(3.$2.R1.(4.R2.))(5.$6.$7.(8.VO,VR1,)VR2,VRR,(9.VO,Vpans,Vpupd,VR1,R4.(1:.VR1,$17.O8.R3.O6.O5.O4.O2.))(1:.VR2,$18.O7.R2.O6.O5.O3.O1.))")
(* [comment removed for export] *).
Proof.
  intros HR HK HB o st cst ->. pose proof (ag_tail_ctrl) as HT. pose proof (free_meta_ctrl) as HF. pose proof (alloc_meta_ctrl) as HA.
  unfold alloc_group, bad_answer. cbn [lh_nest full_lay lay_none]. sync.
Qed.

#[using="Type"] Lemma alloc_slot_ctrl fuel : ltac2:(CDefT.buildp (gd_tbl_MallocCtrl ()) "Psc,$7.Preq,$7.Pk1,P,$2.P,$7.(19.VR1,)Pk2,P,$2.P,$7.(19.VR2,)Pb1,(19.VR1,)Pb2,(19.VR2,)P,(<.VO,Vpans,Vpupd,$7.VR1,VR2,VRR,R4.R3.)P,(1.VO,Vpans,Vpupd,VR1,VR2,VRR,R3.R2.)Po,VO,Pst,$2.Pcst,$2.P,(3.$2.R1.(4.R2.))(5.$6.$7.(8.VO,VR1,)VR2,VRR,(9.VO,Vpans,Vpupd,VR1,R4.(1;.VR1,$17.O1.R3.R<.R;.R:.R8.))(1;.VR2,$18.O1.R2.R<.R;.R9.R7.))")
(* [comment removed for export] *).
Proof.
  induction fuel as [|f IH]; intros sc req k1 k2 b1 b2 HK HB o st cst ->.
  { cbn [alloc_slot]. sync. }
  pose proof (try_avail_ctrl) as HTA. pose proof (queue_ctrl) as HQ.
  pose proof (alloc_group_ctrl (alloc_slot full_lay f) (alloc_slot lay_none f)) as HG.
  cbn [alloc_slot]. sync.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition DREL {X1 X2} (XX : O * X1 -> X2 -> Prop) (dec1 : decoder X1) (dec2 : decoder X2) : Prop :=
  forall p k1 k2 b1 b2,
    (forall o m idx, strel XX (prun o (k1 m idx)) (k2 m idx)) ->
    BREL XX b1 b2 ->
    forall o st cst, cst = strip st -> strel XX (prun o (dec1 st p k1 b1)) (dec2 cst p k2 b2).

#[using="Type"] Lemma dec_slots_drel : DREL RR (@dec_slots R1) (@dec_slots R2).
Proof.
  intros p k1 k2 b1 b2 HK HB o st cst ->. unfold dec_slots. srw.
  destruct (s_slots st !! p) as [[m idx]|]; [apply HK | sync].
Qed.

#[using="Type"] Lemma free_group_ctrl (dec1 : decoder R1) (dec2 : decoder R2) rec1 rec2 g k1 k2 b1 b2 : ltac2:(CDefT.buildp (gd_tbl_MallocCtrl ()) "P,(1<.VR1,VR2,VRR,O9.O8.)P,Pg',$1=.Pi',$7.Pk1',P,$2.P,$1>.(19.VR1,)Pk2',P,$2.P,$1>.(19.VR2,)Pb1',(19.VR1,)Pb2',(19.VR2,)P,(<.VO,Vpans,Vpupd,$1>.VR1,VR2,VRR,R4.R3.)P,(1.VO,Vpans,Vpupd,VR1,VR2,VRR,R3.R2.)Po,VO,Pst,$2.Pcst,$2.P,(3.$2.R1.(4.R2.))(5.$6.$7.(8.VO,VR1,)VR2,VRR,(9.VO,Vpans,Vpupd,VR1,R4.A5.O7.R3.R<.R;.R:.R8.)A5.O6.R2.R<.R;.R9.R7.)P,(<.VO,Vpans,Vpupd,$1>.VR1,VR2,VRR,O4.O3.)P,(1.VO,Vpans,Vpupd,VR1,VR2,VRR,O2.O1.)Po,VO,Pst,$2.Pcst,$2.P,(3.$2.R1.(4.R2.))(5.$6.$7.(8.VO,VR1,)VR2,VRR,(9.VO,Vpans,Vpupd,VR1,R4.(1?.VR1,O9.O7.R3.O5.O4.O2.))(1?.VR2,O8.O6.R2.O5.O3.O1.))")
(* [comment removed for export] *).
Proof.
  intros HD HR HK HB o st cst ->. pose proof (free_meta_ctrl) as HF.
  unfold free_group. sync.
  (* [comment removed for export] *)
  all: try (eapply HD; [ intros ? ? ? | assumption | solve_eq ]; sync).
Qed.

#[using="Type"] Lemma nontrivial_free_ctrl (dec1 : decoder R1) (dec2 : decoder R2) (HD : DREL RR dec1 dec2) fuel : ltac2:(CDefT.buildp (gd_tbl_MallocCtrl ()) "Pg,$1=.Pi,$7.Pk1,P,$2.P,$1>.(19.VR1,)Pk2,P,$2.P,$1>.(19.VR2,)Pb1,(19.VR1,)Pb2,(19.VR2,)P,(<.VO,Vpans,Vpupd,$1>.VR1,VR2,VRR,R4.R3.)P,(1.VO,Vpans,Vpupd,VR1,VR2,VRR,R3.R2.)Po,VO,Pst,$2.Pcst,$2.P,(3.$2.R1.(4.R2.))(5.$6.$7.(8.VO,VR1,)VR2,VRR,(9.VO,Vpans,Vpupd,VR1,R4.(20.VR1,O4.O1.R3.R<.R;.R:.R8.))(20.VR2,O3.O1.R2.R<.R;.R9.R7.))")
(* [comment removed for export] *).
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

#[using="Type"] Lemma malloc_small_ctrl_ctrl {R1 R2} (RR : O * R1 -> R2 -> Prop) n k1 k2 b1 b2 :
  KREL RR k1 k2 -> BREL RR b1 b2 ->
  forall o st cst, cst = strip st ->
  strel RR ((prun pans pupd) o (malloc_small_ctrl full_lay st n k1 b1)) (malloc_small_ctrl lay_none cst n k2 b2).
Proof.
  intros HK HB o st cst ->. pose proof (alloc_slot_ctrl pans pupd RR FUEL) as HS.
  unfold malloc_small_ctrl. sync.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma malloc_core_ctrl n : ltac2:(CDefT.buildp (gd_tbl_MallocCtrl ()) "Po,VO,Pst,$2.Pcst,$2.P,(3.$2.R1.(4.R2.))(5.$6.$7.(8.VO,(8.$2.(21.(8.$1=.$7.))))(8.$2.(21.(8.$1=.$7.)))$22.(9.VO,Vpans,Vpupd,(8.$2.(21.(8.$1=.$7.)))R4.(23.$17.R3.O1.))(23.$18.R2.O1.))")
(* [comment removed for export] *).
Proof.
  intros o st cst ->.
  pose proof (@malloc_small_ctrl_ctrl _ _ CREL) as HS. pose proof (@alloc_meta_ctrl O pans pupd _ _ CREL) as HA.
  unfold malloc_core, bad_answer, ret. sync.
  all: try (split; [ solve_eq | reflexivity ]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.

#[using="Hpans"] Lemma rd8_prun {R} st p (k : Z -> M R) o :
  exists o' v, (prun pans pupd) o (rd8 st p k) = (prun pans pupd) o' (k v).
Proof.
  unfold rd8. destruct (cell_read _ _) as [v|hint].
  - dexists o, v; reflexivity.
  - unfold prun. cbn [eruns psel].
    destruct (peek_answer_ok (pans o p (conc st p) hint)) eqn:E.
    + eexists _, _; reflexivity.
    + exfalso. unfold peek_answer_ok in E. pose proof (Hpans o p (conc st p) hint).
      apply Bool.andb_false_iff in E. destruct E as [E|E]; [apply Z.leb_gt in E|apply Z.ltb_ge in E]; lia.
Qed.

#[using="Hpans"] Lemma rd16_prun {R} st p (k : Z -> M R) o :
  exists o' v, (prun pans pupd) o (rd16 st p k) = (prun pans pupd) o' (k v).
Proof.
  unfold rd16. ddestruct (rd8_prun st p (fun b0 => rd8 st (aadd p 1) (fun b1 => k (b0 + 256 * b1))) o) as (o1 & v1 & ->).
  ddestruct (rd8_prun st (aadd p 1) (fun b1 => k (v1 + 256 * b1)) o1) as (o2 & v2 & ->). eauto.
Qed.

#[using="Hpans"] Lemma enframe_read_off_prun {R} st g idx n ctr (k : Z -> M R) o :
  exists o' off, (prun pans pupd) o (enframe_read_off st g idx n ctr k) = (prun pans pupd) o' (k off).
Proof.
  unfold enframe_read_off.
  match goal with |- exists o' off, (prun pans pupd) o (rd8 ?s ?q ?kk) = _ => destruct (rd8_prun s q kk o) as (o1 & b3 & ->) end.
  destruct (negb (b3 =? 0)).
  - match goal with |- exists o' off, (prun pans pupd) o1 (rd16 ?s ?q ?kk) = _ => destruct (rd16_prun s q kk o1) as (o2 & v & ->) end. eauto.
  - eauto.
Qed.

#[using="Type"] Lemma enframe_at_ptr st g idx n off : ltac2:(CDefT.buildp (gd_tbl_MallocCtrl ()) "(24.(3.$1=.(25.$2.$1=.(26.O5.O4.O3.O2.O1.))(27.O5.O4.O3.))(3.$1=.(25.$2.$1=.(26.O5.O4.O3.O2.O1.))(28.(27.O5.O4.O3.)(29.$2:.O1.))))")
(* [comment removed for export] *).
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

#[using="Type"] Lemma strel_smap_r {E A R1 R2 R3} (RR : R1 -> R2 -> Prop) (SS : R1 -> R3 -> Prop) (f : R2 -> R3)
  (t1 : stree E A R1) (t2 : stree E A R2) :
  strel RR t1 t2 -> (forall a b, RR a b -> SS a (f b)) -> strel SS t1 (smap f t2).
Proof. induction 1; intros; cbn; constructor; auto. Qed.

#[using="Type"] Lemma strel_steq_l {E A R1 R2} (RR : R1 -> R2 -> Prop) (t1 t1' : stree E A R1) (t2 : stree E A R2) :
  steq t1 t1' -> strel RR t1' t2 -> strel RR t1 t2.
Proof.
  intros H; revert t2; induction H; intros t2 Ht; inversion Ht; subst; constructor; eauto.
Qed.

(* [comment removed for export] *)
#[using="Hpans"] Theorem malloc_control st n o :
  strel MREL ((prun pans pupd) o (malloc st n)) (cmalloc (strip st) n).
Proof.
  unfold malloc, cmalloc.
  eapply strel_steq_l. { unfold prun. apply eruns_sbind. }
  eapply strel_sbind.
  { apply (malloc_core_ctrl n o (set_tick (N.succ (s_tick st)) st)). reflexivity. }
  intros [o1 [S r]] [S' r'] [HS Hr]; cbn in HS, Hr; subst r' S'.
  destruct r as [[g idx]|].
  - ddestruct (enframe_read_off_prun S g idx n (c_mmap_counter (ctx S))
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

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition FREL (x : O * mstate) (y : mstate) : Prop := strip (snd x) = y.

(* [comment removed for export] *)
#[using="Type"] Theorem free_tail_control (dec1 dec2 : decoder mstate) : ltac2:(CDefT.buildp (gd_tbl_MallocCtrl ()) "P,(2;.VO,Vpans,Vpupd,$2.$2.Lx,(8.VO,$2.)Ly,$2.(3.$2.(4.(25.VO,$2.R2.))(4.R1.))O2.O1.)Pst,$2.Pg,$1=.Pidx,$7.Po,VO,Pcst,$2.P,(3.$2.R1.(4.R5.))(5.$6.$7.(8.VO,$2.)$2.Lx,(8.VO,$2.)Ly,$2.(3.$2.(4.(25.VO,$2.R2.))(4.R1.))(9.VO,Vpans,Vpupd,$2.R3.(2<.O2.R6.R5.R4.))(2<.O1.R2.R5.R4.))")
(* [comment removed for export] *).
Proof.
  intros HD st g idx o cst ->.
  pose proof (nontrivial_free_ctrl pans pupd (fun x y => strip (snd x) = strip y) dec1 dec2 HD FUEL) as HN.
  unfold free_tail, guard, bad_answer, ret. sync.
  all: cbn; rewrite ?strip_strip; try reflexivity; try solve_eq.
Qed.

(* [comment removed for export] *)
Definition hdr_ok (st : mstate) (p : aptr) (c : cptr) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocCtrl ()) "(2=.$2.Lst1,$2.(2=.$1=.Lg,$1=.(2=.$7.Lidx,$7.(2>.Po,VO,(3.(19.(8.VO,(21.(8.(8.$2.$1=.)$7.))))(9.VO,Vpans,Vpupd,(21.(8.(8.$2.$1=.)$7.))R1.(2?.O3.O2.))(30.$6.$7.(8.VO,(21.(8.(8.$2.$1=.)$7.)))(31.VO,(21.(8.(8.$2.$1=.)$7.))R1.(32.(8.(8.$2.$1=.)$7.)(31.(8.$2.$1=.)$7.(31.$2.$1=.R4.R3.)R2.)))))(2>.(3.$2.(4.R3.)(4.O3.))(2>.(3.(21.(8.$1=.$7.))(33.$34.(8.$1=.$7.)(35.$1=.(36.$37.$38.$7.$39.)(3:.$37.$38.$3;.$7.$39.$3<.)(8.$1=.$7.))(3=.$1=.(36.$37.$38.$7.$39.)(3:.$37.$38.$3;.$7.$39.$3<.)(8.$1=.$7.))O1.(3>.O3.))(32.(8.$1=.$7.)(31.$1=.$7.R2.R1.)))Po,VO,(5.$6.$7.(8.VO,$2.)$2.Lx,(8.VO,$2.)Ly,$2.(3.$2.(4.(25.VO,$2.R2.))(4.R1.))(9.VO,Vpans,Vpupd,$2.R1.(2<.(3?.$2.)R4.R3.R2.))(2<.(40.$2.)(4.O3.)R3.R2.))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
#[using="Type"] Theorem free_control st p c o : ltac2:(CDefT.buildp (gd_tbl_MallocCtrl ()) "P,(41.O4.O3.O2.)(5.$6.$7.(8.VO,$2.)$2.$42.(9.VO,Vpans,Vpupd,$2.O1.(43.O4.(32.$1=.O3.)))(44.(4.O4.)(32.$34.O2.)))")
(* [comment removed for export] *).
Proof.
  (intros dd_H; ddestruct dd_H as (st1 & g & idx & Hh & Hs & Hc & Ht)).
  unfold free, cfree. rewrite s_slots_strip, Hc.
  eapply strel_steq_l. { unfold prun. apply eruns_sbind. }
  unfold prun in Hh, Ht |- *. rewrite Hh. cbn [sbind fst snd].
  change (x__ <-- free_tail dec_slots (strip st) g idx;; ret (strip x__))
    with (smap strip (free_tail dec_slots (strip st) g idx)).
  apply (strel_smap_r _ _ _ _ _ (Ht o)). intros [o1 S] S' HS. exact HS.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma free_tail_slots_control st g idx o : ltac2:(CDefT.buildp (gd_tbl_MallocCtrl ()) "(5.$6.$7.(8.VO,$2.)$2.Lx,(8.VO,$2.)Ly,$2.(3.$2.(4.(25.VO,$2.R2.))(4.R1.))(9.VO,Vpans,Vpupd,$2.O1.(2<.(40.$2.)O4.O3.O2.))(2<.(40.$2.)(4.O4.)O3.O2.))")
(* [comment removed for export] *).
Proof. apply free_tail_control; [apply dec_slots_drel | reflexivity]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint follow {R} (t : M R) (ans : list Z) : option R :=
  match t, ans with
  | SRet r, _ => Some r
  | SVis (EUndef _) _, _ => None
  | SVis _ k, a :: ans' => follow (k a) ans'
  | SVis _ _, [] => None
  end.

(* [comment removed for export] *)
Inductive reach : mstate -> list aptr -> list cptr -> Prop :=
| reach_init secret canary ceil res : reach (minit secret canary ceil res) [] []
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

(* [comment removed for export] *)

End TOP.



