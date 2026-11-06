(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.

Module MallocRC.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope stree_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive ev2 : Type :=
| EV (e : ev)                                   (* [comment removed for export] *)
| EMremap (addr old_len new_len : Z).           (* [comment removed for export] *)

Definition M2 (R : Type) := stree ev2 Z R.
Definition ret2 {R} (r : R) : M2 R := SRet r.

Fixpoint lift {R} (t : M R) : M2 R :=
  match t with
  | SRet r => SRet r
  | SVis e k => SVis (EV e) (fun z => lift (k z))
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition bad_answer2 {R} (bail : M2 R) : M2 R := SVis (EV (EUndef UBadAnswer)) (fun _ => bail).
Definition guard2 {R} (tag : Z) (c : bool) (k : M2 R) (bail : M2 R) : M2 R :=
  if c then k else SVis (EV (EUndef (UAssert tag))) (fun _ => bail).

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition mremap_answer_ok (live_minus_old : list (Z * Z)) (new_len r : Z) : bool :=
  is_errno_form r ||
  ((0 <? r) && (r mod PGSZ =? 0) && (r + new_len <=? alloc_ceiling) && ranges_free live_minus_old r new_len).

Definition live_ranges_minus (st : mstate) (rid : N) : list (Z * Z) :=
  s_reserved st ++ map (fun kr : N * region => region_live_range (snd kr))
                        (filter (fun kr : N * region => negb (N.eqb (fst kr) rid)) (map_to_list (s_regions st))).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition set_size_rd {R} (st : mstate) (p e : aptr) (n : Z) (k : mstate -> M R) : M R :=
  rd8 st (aadd p (-3)) (fun b3 => k (set_size p e n b3 st)).

(* [comment removed for export] *)
Definition realloc_mremap {R} (st : mstate) (g : aptr) (p : aptr) (base n : Z)
           (k : mstate -> aptr -> M2 R) (kfail : mstate -> M2 R) (bail : M2 R) : M2 R :=
  let mr := get_meta_rec st g in
  match m_mem mr with
  | None => SVis (EV (EUndef UBadPtr)) (fun _ => bail)
  | Some gm =>
    let rid := fst gm in
    let old_len := m_maplen mr * 4096 in
    let needed := Z.land (n + base + UNIT + IB + 4095) (Z.lnot 4095) in
    let finish (st1 : mstate) : M2 R :=
      (* [comment removed for export] *)
      let st2 := upd_meta g (fun r => m_set_maplen (needed / 4096) (m_set_mem (Some gm) r)) st1 in
      let p' := aadd gm (UNIT + base) in
      let e' := aadd gm (needed - IB) in            (* [comment removed for export] *)
      let st3 := wr8 e' 0 st2 in
      sp <-- lift (set_size_rd st3 p' e' n (fun st4 => ret (havoc p' n st4, p'))) ;; k (fst sp) (snd sp)
    in
    if old_len =? needed then finish st
    else
      SVis (EMremap (conc st gm) old_len needed) (fun r =>
        if negb (mremap_answer_ok (live_ranges_minus st rid) needed r) then bad_answer2 bail
        else if is_err r then kfail st
        else finish (upd_region rid (fun rg => mkRegion (r_kind rg) r needed) st))
  end.

(* [comment removed for export] *)
Definition realloc (st00 : mstate) (p : aptr) (n : Z) : M2 (mstate * optr) :=
  let st0 := set_tick (N.succ (s_tick st00)) st00 in
  let bail := ret2 (st0, @None aptr) in
  if size_overflows n then ret2 (st0, None) else
  hdr <-- lift (get_meta st0 p (fun g offset idx =>
          let mr := get_meta_rec st0 g in
          match slot_start mr idx with
          | None => SVis (EUndef UBadPtr) (fun _ => ret None)
          | Some start =>
            let e := aadd start (get_stride mr - IB) in
            get_nominal_size st0 p e (fun old_size => ret (Some (g, idx, start, e, old_size))) (ret None)
          end) (ret None)) ;;
  match hdr with
  | None => bail
  | Some (g, idx, start, e, old_size) =>
    let mr := get_meta_rec st0 g in
    let avail := snd e - snd p in
    (* [comment removed for export] *)
    if (n <? MMAP_THRESHOLD) && (n <=? avail) && (m_sizeclass mr <=? size_to_class n + 1) then
      lift (set_size_rd st0 p e n (fun st1 => ret (havoc p n st1, Some p)))
    else
      let via_malloc (st1 : mstate) : M2 (mstate * optr) :=
        (* [comment removed for export] *)
        sr <-- lift (malloc st1 n) ;;
        match snd sr with
        | None => ret2 (fst sr, None)
        | Some q => st3 <-- lift (free (fst sr) (Some p)) ;; ret2 (st3, Some q)
        end in
      if (MMAP_THRESHOLD <=? n) && (48 <=? m_sizeclass mr) then
        guard2 70 (m_sizeclass mr =? 63)
          (realloc_mremap st0 g p (snd p - snd start) n
             (fun st' p' => ret2 (st', Some p')) via_malloc bail)
          bail
      else via_malloc st0
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition is_allzero {R} (st : mstate) (p : aptr) (k : bool -> M R) (bail : M R) : M R :=
  get_meta st p (fun g _ _ =>
    let mr := get_meta_rec st g in
    k ((48 <=? m_sizeclass mr) || (get_stride mr <? UNIT * size_class (m_sizeclass mr)))) bail.

(* [comment removed for export] *)
Definition calloc (st0 : mstate) (cnt sz : Z) : M (mstate * optr * bool) :=
  if negb (sz =? 0) && ((2^64 - 1) / sz <? cnt) then ret (st0, None, false)
  else
    let total := cnt * sz in
    sr <-- malloc st0 total ;;
    match snd sr with
    | None => ret (fst sr, None, false)
    | Some p => is_allzero (fst sr) p (fun az => ret (fst sr, Some p, negb az)) (ret (fst sr, Some p, true))
    end.

End CEIL.
End MallocRC.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Open Scope Z_scope.
Local Open Scope stree_scope.

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
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma brk_pages_ok_strip st lo len : brk_pages_ok (strip st) lo len = brk_pages_ok st lo len. Proof. reflexivity. Qed.

End CEIL.  (* [comment removed for export] *)
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
  get_meta_rec_strip get_group_strip group_active_idx_strip get_region_strip conc_strip live_ranges_strip @brk_pages_ok_strip
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
                   s_ctx s_regions s_shadow s_metas s_areas s_groups s_slots s_next_rid s_tick s_secret s_reserved
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
Context {Clg : Ceiling}.  (* [comment removed for export] *)
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

(* [comment removed for export] *)

(* [comment removed for export] *)
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
  (* [comment removed for export] *)
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
Context {Clg : Ceiling}.  (* [comment removed for export] *)
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

(* [comment removed for export] *)
Lemma malloc_core_ctrl n : forall o st cst, cst = strip st ->
  strel CREL ((prun pans pupd) o (malloc_core full_lay st n)) (malloc_core lay_none cst n).
Proof.
  intros o st cst ->.
  pose proof (@malloc_small_ctrl_ctrl _ _ CREL) as HS. pose proof (@alloc_meta_ctrl _ O pans pupd _ _ CREL) as HA.
  unfold malloc_core, bad_answer, ret. sync.
  all: try (split; [ solve_eq | reflexivity ]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

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
  unfold rd16. (first [ pose proof ((rd8_prun st p (fun b0 => rd8 st (aadd p 1) (fun b1 => k (b0 + 256 * b1))) o)) as dR_1; dand3 dR_1 as o1 v1 -> | destruct (rd8_prun st p (fun b0 => rd8 st (aadd p 1) (fun b1 => k (b0 + 256 * b1))) o) as (o1 & v1 & ->) ]).
  (first [ pose proof ((rd8_prun st (aadd p 1) (fun b1 => k (v1 + 256 * b1)) o1)) as dR_2; dand3 dR_2 as o2 v2 -> | destruct (rd8_prun st (aadd p 1) (fun b1 => k (v1 + 256 * b1)) o1) as (o2 & v2 & ->) ]). eauto.
Qed.

Lemma enframe_read_off_prun {R} st g idx n ctr (k : Z -> M R) o :
  exists o' off, (prun pans pupd) o (enframe_read_off st g idx n ctr k) = (prun pans pupd) o' (k off).
Proof.
  unfold enframe_read_off.
  match goal with |- exists o' off, (prun pans pupd) o (rd8 ?s ?q ?kk) = _ => (first [ pose proof ((rd8_prun s q kk o)) as dR_3; dand3 dR_3 as o1 b3 -> | destruct (rd8_prun s q kk o) as (o1 & b3 & ->) ]) end.
  destruct (negb (b3 =? 0)).
  - match goal with |- exists o' off, (prun pans pupd) o1 (rd16 ?s ?q ?kk) = _ => (first [ pose proof ((rd16_prun s q kk o1)) as dR_4; dand3 dR_4 as o2 v -> | destruct (rd16_prun s q kk o1) as (o2 & v & ->) ]) end. eauto.
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

(* [comment removed for export] *)
Theorem malloc_control st n o :
  strel MREL ((prun pans pupd) o (malloc st n)) (cmalloc (strip st) n).
Proof.
  unfold malloc, cmalloc.
  eapply strel_steq_l. { unfold prun. apply eruns_sbind. }
  eapply strel_sbind.
  { apply (malloc_core_ctrl n o (set_tick (N.succ (s_tick st)) st)). reflexivity. }
  intros [o1 [S r]] [S' r'] [HS Hr]; cbn in HS, Hr; subst r' S'.
  destruct r as [[g idx]|].
  - (first [ pose proof ((enframe_read_off_prun S g idx n (c_mmap_counter (ctx S))
               (fun off => let '(st1, p) := enframe_at S g idx n off in ret (havoc p n st1, Some p)) o1)) as dR_5; dex2 dR_5 as o2 off; rename dR_5 into E | pose proof ((enframe_read_off_prun S g idx n (c_mmap_counter (ctx S))
               (fun off => let '(st1, p) := enframe_at S g idx n off in ret (havoc p n st1, Some p)) o1)) as dR_5; dand3 dR_5 as o2 off E | destruct (enframe_read_off_prun S g idx n (c_mmap_counter (ctx S))
               (fun off => let '(st1, p) := enframe_at S g idx n off in ret (havoc p n st1, Some p)) o1) as (o2 & off & E) ]).
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

(* [comment removed for export] *)
Definition hdr_ok (st : mstate) (p : aptr) (c : cptr) : Prop :=
  exists st1 g idx,
    (forall o, (prun pans pupd) o (free_hdr st p) = SRet (o, Some (st1, g, idx)))
    /\ strip st1 = strip st
    /\ (s_slots st) !! c = Some (g, idx)
    /\ (forall o, strel (fun x y => strip (snd x) = strip y)
                        ((prun pans pupd) o (free_tail dec_hdr st1 g idx))
                        (free_tail dec_slots (strip st) g idx)).

(* [comment removed for export] *)
Theorem free_control st p c o :
  hdr_ok st p c ->
  strel FREL ((prun pans pupd) o (free st (Some p))) (cfree (strip st) (Some c)).
Proof.
  ((first [ intro dR_6; dex3 dR_6 as st1 g idx; dand4 dR_6 as Hh Hs Hc Ht | intro dR_6; dand7 dR_6 as st1 g idx Hh Hs Hc Ht | intros (st1 & g & idx & Hh & Hs & Hc & Ht) ])).
  unfold free, cfree. rewrite s_slots_strip, Hc.
  eapply strel_steq_l. { unfold prun. apply eruns_sbind. }
  unfold prun in Hh, Ht |- *. rewrite Hh. cbn [sbind fst snd].
  change (x__ <-- free_tail dec_slots (strip st) g idx;; ret (strip x__))
    with (smap strip (free_tail dec_slots (strip st) g idx)).
  apply (strel_smap_r _ _ _ _ _ (Ht o)). intros [o1 S] S' HS. exact HS.
Qed.

(* [comment removed for export] *)
Lemma free_tail_slots_control st g idx o :
  strel (fun x y => strip (snd x) = strip y)
        ((prun pans pupd) o (free_tail dec_slots st g idx)) (free_tail dec_slots (strip st) g idx).
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

(* [comment removed for export] *)

End TOP.



