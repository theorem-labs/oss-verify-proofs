(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Bool.
From Stdlib Require Lia.
From stdpp Require gmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require STree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Malloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MallocCtrl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Cnt.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_WSlot2.
Module MEX_konts.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import stdpp.gmap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MI_Tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Cnt OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WSlot2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MEX_lib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope stree_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition MAPF : Z := MAP_PRIVATE + MAP_ANON.
Definition MAPFX : Z := MAP_PRIVATE + MAP_ANON + MAP_FIXED.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition cm_fin (x : mstate * option (aptr * Z)) : M (mstate * option cptr) :=
  let (st1, r) := x in
  ret (strip st1, match r with Some (g, idx) => Some (slot_of st1 g idx) | None => None end).

Lemma cmalloc_eq cs n : cmalloc cs n = sbind (malloc_core lay_none cs n) cm_fin.
Proof. reflexivity. Qed.

Definition mc_k : mstate -> option (aptr * Z) -> M (mstate * option (aptr * Z)) := fun st1 r => ret (st1, r).
Definition mc_bail (st : mstate) : M (mstate * option (aptr * Z)) := ret (st, @None (aptr * Z)).

Lemma malloc_core_small lay st n :
  size_overflows n = false -> n < MMAP_THRESHOLD ->
  malloc_core lay st n = malloc_small_ctrl lay st n mc_k (mc_bail st).
Proof. intros H1 H2. unfold malloc_core. rewrite H1. rewrite (proj2 (Z.leb_gt _ _) H2). reflexivity. Qed.

(* [comment removed for export] *)
Definition msc_sc (st : mstate) (n : Z) : Z :=
  let sc := size_to_class n in
  match active st sc with
  | Some _ => sc
  | None =>
    if (4 <=? sc) && (sc <? 32) && negb (sc =? 6) && Z.even sc && (usage st sc =? 0) then
      let usage1 := usage st (Z.lor sc 1) in
      let usage1 := match active st (Z.lor sc 1) with
                    | None => usage1 + 3
                    | Some _ => let ar := get_meta_rec st (default (0%N,-1) (active st (Z.lor sc 1))) in
                                if (m_avail ar =? 0) && (m_freed ar =? 0) then usage1 + 3 else usage1
                    end in
      if usage1 <=? 12 then Z.lor sc 1 else sc
    else sc
  end.

Definition msc_k {R} (sc : Z) (k : mstate -> option (aptr * Z) -> M R) (bail : M R) : mstate -> Z -> M R :=
  fun st1 idx =>
    if idx <? 0 then k st1 None
    else match active st1 sc with
         | Some gp => k st1 (Some (gp, idx))
         | None => SVis (EUndef UBadPtr) (fun _ => bail)
         end.

(* [comment removed for export] *)
Lemma malloc_small_ctrl_eq {R} lay st n (k : mstate -> option (aptr * Z) -> M R) bail :
  let sc := msc_sc st n in
  match active st sc with Some gp => m_avail (get_meta_rec st gp) = 0 | None => True end ->
  malloc_small_ctrl lay st n k bail = alloc_slot lay FUEL st sc n (msc_k sc k bail) bail.
Proof.
  cbn zeta. intros H. unfold malloc_small_ctrl. change (match active st (size_to_class n) with Some _ => _ | None => _ end) with (msc_sc st n).
  destruct (active st (msc_sc st n)) as [gp|]; [| reflexivity].
  rewrite H. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition as_k2 {R} (sc : Z) (k : mstate -> Z -> M R) (bail : M R) : mstate -> optr -> M R :=
  fun st2 go =>
    match go with
    | None => k st2 (-1)
    | Some g =>
      let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
      queue (LActive sc) g st3 (fun st4 => k st4 0) bail
    end.

Definition as_k1 {R} (lay : layout_hook) (f : nat) (sc req : Z) (k : mstate -> Z -> M R) (bail : M R) : mstate -> Z -> M R :=
  fun st1 first =>
    if negb (first =? 0) then k st1 (ctz32 first)
    else alloc_group R lay (alloc_slot lay f) st1 sc req (as_k2 sc k bail) bail.

Lemma alloc_slot_S {R} lay f st sc req (k : mstate -> Z -> M R) bail :
  alloc_slot lay (S f) st sc req k bail = try_avail sc st (as_k1 lay f sc req k bail) bail.
Proof. reflexivity. Qed.

Lemma try_avail_none {R} sc st (k : mstate -> Z -> M R) bail :
  active st sc = None -> try_avail sc st k bail = k st 0.
Proof. intros H. unfold try_avail. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma try_avail_dead {R} sc st m (k : mstate -> Z -> M R) bail :
  active st sc = Some m -> m_avail (get_meta_rec st m) = 0 -> m_freed (get_meta_rec st m) = 0 ->
  m_next (get_meta_rec st m) = Some m ->
  try_avail sc st k bail = k (dequeue (LActive sc) m st) 0.
Proof.
  intros HA AV FR NX. unfold try_avail. rewrite HA, AV, FR. cbn [Z.eqb negb].
  rewrite (dequeue_self (LActive sc) m st NX). rewrite active_upd_meta.
  change (set_head (LActive sc) None st) with (set_active sc None st). rewrite active_set_active, Z.eqb_refl. reflexivity.
Qed.

Lemma as_k1_zero {R} lay f sc req (k : mstate -> Z -> M R) bail st1 :
  as_k1 lay f sc req k bail st1 0 = alloc_group R lay (alloc_slot lay f) st1 sc req (as_k2 sc k bail) bail.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AGK.
Context {R : Type}.
Variables (lay : layout_hook) (rec : mstate -> Z -> Z -> (mstate -> Z -> M R) -> M R -> M R).
Variables (sc req : Z) (k : mstate -> optr -> M R) (bail : M R).

(* [comment removed for export] *)
Definition ag_kmm (st1 : mstate) (m : aptr) (cnt needed : Z) : Z -> M R :=
  fun r =>
    if negb (mmap_answer_ok (live_ranges st1) needed r) then bad_answer bail else
    if is_err r then free_meta m st1 (fun st2 => k st2 None) bail
    else
      let '(st2, rid) := new_region RKGroup r needed st1 in
      let st3 := upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2 in
      let st4 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st3 in
      let ai := (4096 - UNIT) / (UNIT * size_class sc) - 1 in
      let ai := if cnt - 1 <? ai then cnt - 1 else ai in
      let ai := if ai <? 0 then 0 else ai in
      ag_tail lay st4 sc m (rid, 0) cnt ai k.

(* [comment removed for export] *)
Definition ag_knest (m : aptr) (cnt j : Z) : mstate -> Z -> M R :=
  fun st1 idx =>
    if idx <? 0 then free_meta m st1 (fun st2 => k st2 None) bail
    else
      match active st1 j with
      | None => SVis (EUndef UBadPtr) (fun _ => bail)
      | Some g =>
        let p := slot_of st1 g idx in
        let st2 := lh_nest lay st1 g idx j (UNIT * size_class sc) cnt in
        let st3 := upd_meta m (m_set_maplen 0) st2 in
        ag_tail lay st3 sc m p cnt (cnt - 1) k
      end.

(* [comment removed for export] *)
Definition ag_k : mstate -> optr -> M R :=
  fun st mo =>
    match mo with
    | None => k st None
    | Some m =>
      let size := UNIT * size_class sc in
      let cnt := ag_cnt1 sc (usage st sc) in
      if PGSZ / 2 <? size * cnt + UNIT then
        let nosmall := is_bouncing sc st in
        let st1 := step_seq (account_bounce sc st) in
        let usage1 := if (Z.even sc) && (sc <? 32) then usage st sc + usage st1 (sc + 1) else usage st sc in
        let '(cnt3, needed) := ag_cn3 sc req (ag_cnt2 sc cnt usage1 nosmall) usage1 nosmall in
        SVis (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) (ag_kmm st1 m cnt3 needed)
      else
        let j := size_to_class (UNIT + cnt * size - IB) in
        rec st j (UNIT + cnt * size - IB) (ag_knest m cnt j) bail
    end.

Lemma alloc_group_eq st : alloc_group R lay rec st sc req k bail = alloc_meta st ag_k bail.
Proof.
  unfold alloc_group, ag_k, ag_cn3, ag_cnt2, ag_cnt1, adj, cnt0_of, ag_kmm, ag_knest. reflexivity.
Qed.
End AGK.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AMK.
Context {R : Type}.
Variables (k : mstate -> optr -> M R) (bail : M R).

(* [comment removed for export] *)
Definition am_kp (st : mstate) (p : aptr) : Z -> M R :=
  fun r =>
    if negb (mprotect_answer_ok r) then bad_answer bail else
    if (r =? 0) || (r =? TWO64 - ENOSYS) then am_carve st p k bail else k st None.

Lemma am_finish_prot st p :
  c_avail_meta_areas (ctx st) = Some p -> snd p mod PGSZ = 0 ->
  am_finish st true k bail = SVis (EMprotect (conc st p) PGSZ PROT_RW) (am_kp st p).
Proof. intros H1 H2. unfold am_finish. rewrite H1, H2. reflexivity. Qed.

Lemma am_finish_noprot st p :
  c_avail_meta_areas (ctx st) = Some p -> am_finish st false k bail = am_carve st p k bail.
Proof. intros H1. unfold am_finish. rewrite H1. destruct (negb (snd p mod PGSZ =? 0)); reflexivity. Qed.

(* [comment removed for export] *)
Definition am_kb (st : mstate) (nu : bool) (n : Z) : Z -> M R :=
  fun r =>
    if negb (mmap_answer_ok (live_ranges st) (n * PGSZ) r) then bad_answer bail else
    if is_err r then k st None else
    let '(st1, rid) := new_region RKMeta r (n * PGSZ) st in
    let st2 := upd_ctx (fun c => set_meta_alloc_shift (c_meta_alloc_shift c + 1)
                                  (set_avail_meta_area_count (n - 1)
                                  (set_avail_meta_areas (Some (rid, PGSZ)) c))) st1 in
    am_finish st2 nu k bail.

Lemma am_after_brk_mmap st nu :
  c_avail_meta_area_count (ctx st) = 0 ->
  let n := Z.shiftl 2 (c_meta_alloc_shift (ctx st)) in
  am_after_brk st nu k bail = SVis (EMmap 0 (n * PGSZ) PROT_NONE (MAP_PRIVATE + MAP_ANON)) (am_kb st nu n).
Proof. intros H. unfold am_after_brk. rewrite H. reflexivity. Qed.

Lemma am_after_brk_have st nu :
  (c_avail_meta_area_count (ctx st) =? 0) = false -> am_after_brk st nu k bail = am_finish st nu k bail.
Proof. intros H. unfold am_after_brk. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Definition am_k3 (st : mstate) (base : Z) : Z -> M R :=
  fun rg =>
    if negb (mmap_fixed_answer_ok base rg) then bad_answer bail else
    let '(st1, rid) := new_region RKBrk base (2 * PGSZ) st in
    let st2 := upd_ctx (fun c => set_avail_meta_area_count 1
                                  (set_avail_meta_areas (Some (rid, PGSZ))
                                  (set_brk (BrkLive rid (2 * PGSZ)) c))) st1 in
    am_after_brk st2 false k bail.

Definition am_k2 (st : mstate) (cur : Z) : Z -> M R :=
  fun r =>
    let base := round_up_pg cur in
    let new := base + 2 * PGSZ in
    if negb (brk_answer_ok cur new r) then bad_answer bail else
    if negb (r =? new) then am_after_brk (upd_ctx (set_brk BrkDead) st) true k bail
    else if negb (brk_pages_ok st base (2 * PGSZ)) then bad_answer bail
    else SVis (EMmap base PGSZ PROT_NONE (MAP_PRIVATE + MAP_ANON + MAP_FIXED)) (am_k3 st base).

Definition am_k1 (st : mstate) : Z -> M R :=
  fun cur =>
    if negb (brk0_answer_ok cur) then bad_answer bail else
    SVis (EBrk (round_up_pg cur + 2 * PGSZ)) (am_k2 st cur).

Lemma alloc_meta_untried st :
  c_free_meta_head (ctx st) = None -> c_avail_meta_count (ctx st) = 0 ->
  c_avail_meta_area_count (ctx st) = 0 -> c_brk (ctx st) = BrkUntried ->
  alloc_meta st k bail = SVis (EBrk 0) (am_k1 (am_init st)).
Proof.
  intros H1 H2 H3 H4. unfold alloc_meta. change (if c_init_done (ctx st) =? 0 then _ else st) with (am_init st).
  destruct (am_init_fields st) as (F1 & F2 & F3). rewrite F1, H1, F2, H2. cbn [Z.eqb negb].
  assert (F4 : c_avail_meta_area_count (ctx (am_init st)) = 0) by (unfold am_init; destruct (c_init_done (ctx st) =? 0); exact H3).
  assert (F5 : c_brk (ctx (am_init st)) = BrkUntried) by (unfold am_init; destruct (c_init_done (ctx st) =? 0); exact H4).
  rewrite F4, F5. reflexivity.
Qed.
End AMK.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition am_carve_post (st : mstate) (p : aptr) : mstate * aptr :=
  let st1 := upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096))
                                (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st in
  let st2 := match c_meta_area_tail (ctx st1) with
             | Some tl => set_areas (<[tl := match (s_areas st1) !! tl with
                                              | Some a => mkArea (a_check a) (Some p) (a_nslots a)
                                              | None => mkArea 0 (Some p) 0 end]> (s_areas st1)) st1
             | None => upd_ctx (set_meta_area_head (Some p)) st1
             end in
  let st3 := upd_ctx (set_meta_area_tail (Some p)) st2 in
  let old := default (mkArea 0 None 0) ((s_areas st3) !! p) in
  let st4 := set_areas (<[p := mkArea (c_secret (ctx st3)) (a_next old) NSLOTS]> (s_areas st3)) st3 in
  let st5 := upd_ctx (fun c => set_avail_meta (Some (aadd p AREA_HDR)) (set_avail_meta_count NSLOTS c)) st4 in
  let m := aadd p AREA_HDR in
  (upd_meta m (fun r => m_set_prev None (m_set_next None r))
     (upd_ctx (fun c => set_avail_meta (Some (aadd m META_SIZE)) (set_avail_meta_count (c_avail_meta_count c - 1) c)) st5), m).

Lemma am_carve_eq {R} st p (k : mstate -> optr -> M R) bail :
  am_carve st p k bail = k (fst (am_carve_post st p)) (Some (snd (am_carve_post st p))).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition ag_tail_post (lay : layout_hook) (st : mstate) (sc : Z) (m : aptr) (p : aptr) (cnt active_idx : Z) : mstate :=
  let st := lh_hdr lay st p in
  let st1 := set_usage sc (usage st sc + cnt) st in
  let avail := mask_upto active_idx in
  let freed := mask_upto (cnt - 1) - avail in
  let st2 := upd_meta m (fun r =>
               m_set_sizeclass sc (m_set_freeable 1 (m_set_last_idx (cnt - 1)
               (m_set_mem (Some p) (m_set_freed freed (m_set_avail avail r)))))) st1 in
  let st3 := put_group p (Some m) active_idx st2 in
  add_slots m p (get_stride (get_meta_rec st3 m)) cnt st3.

Lemma ag_tail_eq {R} lay st sc m p cnt ai (k : mstate -> optr -> M R) :
  ag_tail lay st sc m p cnt ai k = k (ag_tail_post lay st sc m p cnt ai) (Some m).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition ag_mm_post (lay : layout_hook) (sc : Z) (m : aptr) (cnt needed : Z) (st1 : mstate) (r : Z) : mstate :=
  let '(st2, rid) := new_region RKGroup r needed st1 in
  let st3 := upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2 in
  let st4 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st3 in
  let ai := (4096 - UNIT) / (UNIT * size_class sc) - 1 in
  let ai := if cnt - 1 <? ai then cnt - 1 else ai in
  let ai := if ai <? 0 then 0 else ai in
  ag_tail_post lay st4 sc m (rid, 0) cnt ai.

Lemma ag_kmm_ok {R} lay sc (k : mstate -> optr -> M R) bail st1 m cnt needed r :
  mmap_answer_ok (live_ranges st1) needed r = true -> is_err r = false ->
  ag_kmm lay sc k bail st1 m cnt needed r = k (ag_mm_post lay sc m cnt needed st1 r) (Some m).
Proof. intros H1 H2. unfold ag_kmm. rewrite H1, H2. reflexivity. Qed.

Lemma ag_kmm_err {R} lay sc (k : mstate -> optr -> M R) bail st1 m cnt needed r :
  mmap_answer_ok (live_ranges st1) needed r = true -> is_err r = true ->
  ag_kmm lay sc k bail st1 m cnt needed r = k (fm_post m st1) None.
Proof. intros H1 H2. unfold ag_kmm. rewrite H1, H2. cbn [negb]. apply free_meta_eq. Qed.

Lemma ag_kmm_bad {R} lay sc (k : mstate -> optr -> M R) bail st1 m cnt needed r :
  mmap_answer_ok (live_ranges st1) needed r = false -> rejects (ag_kmm lay sc k bail st1 m cnt needed r).
Proof. intros H1. unfold ag_kmm. rewrite H1. exact I. Qed.

(* [comment removed for export] *)
Definition as_k2_post (sc : Z) (g : aptr) (st2 : mstate) : mstate :=
  q_post (LActive sc) g (upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2).

Lemma as_k2_some {R} sc (k : mstate -> Z -> M R) bail st2 g :
  m_next (get_meta_rec st2 g) = None -> m_prev (get_meta_rec st2 g) = None ->
  as_k2 sc k bail st2 (Some g) = k (as_k2_post sc g st2) 0.
Proof.
  intros HN HP. unfold as_k2, as_k2_post. apply queue_eq; rewrite get_meta_rec_upd_same; cbn; assumption.
Qed.

Lemma as_k2_none {R} sc (k : mstate -> Z -> M R) bail st2 : as_k2 sc k bail st2 None = k st2 (-1).
Proof. reflexivity. Qed.

Lemma msc_k_zero {R} sc (k : mstate -> option (aptr * Z) -> M R) bail st gp :
  active st sc = Some gp -> msc_k sc k bail st 0 = k st (Some (gp, 0)).
Proof. intros H. unfold msc_k. rewrite H. reflexivity. Qed.

Lemma msc_k_neg {R} sc (k : mstate -> option (aptr * Z) -> M R) bail st :
  msc_k sc k bail st (-1) = k st None.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma get_head_q_post_empty h g st : get_head st h = None -> get_head (q_post h g st) h = Some g.
Proof. intros H. unfold q_post. rewrite H. apply get_head_set_head. Qed.

Lemma active_as_k2_post sc g st2 : active st2 sc = None -> active (as_k2_post sc g st2) sc = Some g.
Proof.
  intros H. unfold as_k2_post. change (active ?s sc) with (get_head s (LActive sc)).
  apply get_head_q_post_empty. cbn. rewrite active_upd_meta. exact H.
Qed.


End CeilWrap.
End MEX_konts.

(* [comment removed for export] *)
Module MEX_m0.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import stdpp.gmap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MI_Tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Cnt OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WSlot2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MEX_lib MEX_konts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition cs0 (resv : list (Z * Z)) : mstate := strip (minit 0 resv).

(* [comment removed for export] *)
Inductive m0var : Type :=
| VA (cur : Z)     (* [comment removed for export] *)
| VB (am : Z).     (* [comment removed for export] *)

Section M0.
Variable resv : list (Z * Z).
Let st0 := cs0 resv.
Let bail0 : M (mstate * option (aptr * Z)) := mc_bail st0.
Let K1 := msc_k 44 mc_k bail0.
Let K2 := as_k2 44 K1 bail0.
Let AGK := ag_k lay_none (alloc_slot lay_none 63) 44 65536 K2 bail0.
(* [comment removed for export] *)
Definition m0 : aptr := (0%N, 4120).

Definition m0_st1 : mstate := am_init st0.

(* [comment removed for export] *)
Definition M0c : M (mstate * option (aptr * Z)) := malloc_core lay_none st0 65536.

Lemma msc_sc_0 : msc_sc st0 65536 = 44.
Proof. reflexivity. Qed.

Lemma M0c_eq : M0c = SVis (EBrk 0) (am_k1 AGK bail0 m0_st1).
Proof.
  unfold M0c. rewrite (malloc_core_small lay_none st0 65536 eq_refl eq_refl).
  rewrite (malloc_small_ctrl_eq lay_none st0 65536 mc_k bail0) by (rewrite msc_sc_0; exact I). rewrite msc_sc_0.
  unfold FUEL. rewrite alloc_slot_S, (try_avail_none 44 st0) by reflexivity. rewrite as_k1_zero, alloc_group_eq.
  apply alloc_meta_untried; reflexivity.
Qed.

(* [comment removed for export] *)
Definition m0_st2 (v : m0var) : mstate :=
  match v with
  | VA cur =>
      upd_ctx (fun c => set_avail_meta_area_count 1 (set_avail_meta_areas (Some (0%N, PGSZ)) (set_brk (BrkLive 0%N (2 * PGSZ)) c)))
              (fst (new_region RKBrk (round_up_pg cur) (2 * PGSZ) m0_st1))
  | VB am =>
      upd_ctx (fun c => set_meta_alloc_shift (c_meta_alloc_shift c + 1)
                          (set_avail_meta_area_count (2 - 1) (set_avail_meta_areas (Some (0%N, PGSZ)) c)))
              (fst (new_region RKMeta am (2 * PGSZ) (upd_ctx (set_brk BrkDead) m0_st1)))
  end.

(* [comment removed for export] *)
Definition m0_st6 (v : m0var) : mstate := fst (am_carve_post (m0_st2 v) (0%N, PGSZ)).
Definition m0_st7 (v : m0var) : mstate := step_seq (account_bounce 44 (m0_st6 v)).
(* [comment removed for export] *)
Definition m0_pre (v : m0var) (r : Z) : mstate := as_k2_post 44 m0 (ag_mm_post lay_none 44 m0 1 69632 (m0_st7 v) r).
Definition m0_post (v : m0var) (r : Z) : mstate := strip (m0_pre v r).
(* [comment removed for export] *)
Definition m0_fail (v : m0var) : mstate := strip (fm_post m0 (m0_st7 v)).

(* [comment removed for export] *)
Lemma M0c_1 cur : brk0_answer_ok cur = true ->
  tsub M0c cur = SVis (EBrk (round_up_pg cur + 2 * PGSZ)) (am_k2 AGK bail0 m0_st1 cur).
Proof. intros H. rewrite M0c_eq. cbn [tsub]. unfold am_k1. rewrite H. reflexivity. Qed.

Lemma M0c_1_bad cur : brk0_answer_ok cur = false -> rejects (tsub M0c cur).
Proof. intros H. rewrite M0c_eq. cbn [tsub]. unfold am_k1. rewrite H. exact I. Qed.

(* [comment removed for export] *)
Lemma brk0_ok_facts cur : brk0_answer_ok cur = true -> 0 < cur < TWO64 /\ cur mod PGSZ = 0 /\ round_up_pg cur = cur.
Proof.
  unfold brk0_answer_ok. intros H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.ltb_lt in H1. apply Z.ltb_lt in H3. apply Z.eqb_eq in H2.
  split; [lia|]. split; [exact H2|].
  unfold round_up_pg, PGSZ in *. change (4096 - 1) with (Z.pred (2 ^ 12)). rewrite <- Z.ones_equiv, Z.land_ones by lia.
  change (2 ^ 12) with 4096. rewrite Z.mod_opp_l_z; lia.
Qed.

Lemma M0c_2_bad cur a : brk0_answer_ok cur = true ->
  brk_answer_ok cur (round_up_pg cur + 2 * PGSZ) a = false -> rejects (tsubs M0c [cur; a]).
Proof. intros H1 H2. cbn [tsubs]. rewrite (M0c_1 cur H1). cbn [tsub]. unfold am_k2. rewrite H2. exact I. Qed.

(* [comment removed for export] *)
Lemma M0c_2A cur : brk0_answer_ok cur = true ->
  brk_pages_ok m0_st1 (round_up_pg cur) (2 * PGSZ) = true ->
  tsubs M0c [cur; round_up_pg cur + 2 * PGSZ] =
    SVis (EMmap (round_up_pg cur) PGSZ PROT_NONE (MAP_PRIVATE + MAP_ANON + MAP_FIXED)) (am_k3 AGK bail0 m0_st1 (round_up_pg cur)).
Proof.
  intros H1 HP. cbn [tsubs]. rewrite (M0c_1 cur H1). cbn [tsub]. unfold am_k2.
  unfold brk_answer_ok. rewrite Z.eqb_refl. cbn [orb negb]. rewrite HP. reflexivity.
Qed.

Lemma M0c_2A_bad cur : brk0_answer_ok cur = true ->
  brk_pages_ok m0_st1 (round_up_pg cur) (2 * PGSZ) = false ->
  rejects (tsubs M0c [cur; round_up_pg cur + 2 * PGSZ]).
Proof.
  intros H1 HP. cbn [tsubs]. rewrite (M0c_1 cur H1). cbn [tsub]. unfold am_k2.
  unfold brk_answer_ok. rewrite Z.eqb_refl. cbn [orb negb]. rewrite HP. exact I.
Qed.

(* [comment removed for export] *)
Lemma M0c_2B cur : brk0_answer_ok cur = true ->
  tsubs M0c [cur; cur] = SVis (EMmap 0 8192 PROT_NONE (MAP_PRIVATE + MAP_ANON)) (am_kb AGK bail0 (upd_ctx (set_brk BrkDead) m0_st1) true 2).
Proof.
  intros H1. pose proof (brk0_ok_facts cur H1) as (B1 & B2 & B3).
  cbn [tsubs]. rewrite (M0c_1 cur H1). cbn [tsub]. unfold am_k2.
  unfold brk_answer_ok. rewrite B3. replace (cur =? cur + 2 * PGSZ) with false by (symmetry; apply Z.eqb_neq; unfold PGSZ; lia).
  rewrite Z.eqb_refl. cbn [orb negb]. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ag_k_44 {R} rec (k : mstate -> optr -> M R) bail st m :
  usage st 44 = 0 ->
  ag_k lay_none rec 44 65536 k bail st (Some m) =
    SVis (EMmap 0 69632 PROT_RW (MAP_PRIVATE + MAP_ANON)) (ag_kmm lay_none 44 k bail (step_seq (account_bounce 44 st)) m 1 69632).
Proof.
  intros HU. unfold ag_k. rewrite HU. change (ag_cnt1 44 0) with 7.
  change (PGSZ / 2 <? UNIT * size_class 44 * 7 + UNIT) with true. cbv iota.
  unfold is_bouncing. change (sc_in_seq_range 44) with false. cbn [andb].
  change (Z.even 44 && (44 <? 32)) with false. cbv iota.
  change (ag_cn3 44 65536 (ag_cnt2 44 7 0 false) 0 false) with (1, 69632). reflexivity.
Qed.

Lemma AGK_st6 v : AGK (m0_st6 v) (Some m0) = SVis (EMmap 0 69632 PROT_RW (MAP_PRIVATE + MAP_ANON)) (ag_kmm lay_none 44 K2 bail0 (m0_st7 v) m0 1 69632).
Proof. unfold AGK, m0_st7. apply ag_k_44. destruct v; reflexivity. Qed.

Lemma M0c_3A cur rg : brk0_answer_ok cur = true ->
  brk_pages_ok m0_st1 (round_up_pg cur) (2 * PGSZ) = true ->
  mmap_fixed_answer_ok (round_up_pg cur) rg = true ->
  tsubs M0c [cur; round_up_pg cur + 2 * PGSZ; rg] =
    SVis (EMmap 0 69632 PROT_RW (MAP_PRIVATE + MAP_ANON)) (ag_kmm lay_none 44 K2 bail0 (m0_st7 (VA cur)) m0 1 69632).
Proof.
  intros H1 HP HG. change (tsubs M0c [cur; round_up_pg cur + 2 * PGSZ; rg]) with (tsub (tsubs M0c [cur; round_up_pg cur + 2 * PGSZ]) rg).
  rewrite (M0c_2A cur H1 HP). cbn [tsub]. unfold am_k3. rewrite HG. cbn [negb].
  change (am_after_brk (m0_st2 (VA cur)) false AGK bail0 = SVis (EMmap 0 69632 PROT_RW (MAP_PRIVATE + MAP_ANON)) (ag_kmm lay_none 44 K2 bail0 (m0_st7 (VA cur)) m0 1 69632)).
  rewrite am_after_brk_have by reflexivity. rewrite (am_finish_noprot AGK bail0 _ (0%N, PGSZ)) by reflexivity.
  rewrite am_carve_eq. change (fst _) with (m0_st6 (VA cur)). change (snd _) with m0. apply AGK_st6.
Qed.

Lemma M0c_3A_bad cur rg : brk0_answer_ok cur = true ->
  brk_pages_ok m0_st1 (round_up_pg cur) (2 * PGSZ) = true ->
  mmap_fixed_answer_ok (round_up_pg cur) rg = false ->
  rejects (tsubs M0c [cur; round_up_pg cur + 2 * PGSZ; rg]).
Proof.
  intros H1 HP HG. change (tsubs M0c [cur; round_up_pg cur + 2 * PGSZ; rg]) with (tsub (tsubs M0c [cur; round_up_pg cur + 2 * PGSZ]) rg).
  rewrite (M0c_2A cur H1 HP). cbn [tsub]. unfold am_k3. rewrite HG. exact I.
Qed.

(* [comment removed for export] *)
Lemma live_ranges_brkdead : live_ranges (upd_ctx (set_brk BrkDead) m0_st1) = resv ++ [].
Proof. reflexivity. Qed.

Lemma M0c_3B_err cur am : brk0_answer_ok cur = true ->
  mmap_answer_ok (resv ++ []) 8192 am = true -> is_err am = true ->
  tsubs M0c [cur; cur; am] = ret (upd_ctx (set_brk BrkDead) m0_st1, None).
Proof.
  intros H1 HV HE. change (tsubs M0c [cur; cur; am]) with (tsub (tsubs M0c [cur; cur]) am).
  rewrite (M0c_2B cur H1). cbn [tsub]. unfold am_kb. rewrite live_ranges_brkdead.
  change (2 * PGSZ) with 8192. rewrite HV, HE. reflexivity.
Qed.

Lemma M0c_3B_bad cur am : brk0_answer_ok cur = true ->
  mmap_answer_ok (resv ++ []) 8192 am = false -> rejects (tsubs M0c [cur; cur; am]).
Proof.
  intros H1 HV. change (tsubs M0c [cur; cur; am]) with (tsub (tsubs M0c [cur; cur]) am).
  rewrite (M0c_2B cur H1). cbn [tsub]. unfold am_kb. rewrite live_ranges_brkdead.
  change (2 * PGSZ) with 8192. rewrite HV. exact I.
Qed.

Lemma M0c_3B cur am : brk0_answer_ok cur = true ->
  mmap_answer_ok (resv ++ []) 8192 am = true -> is_err am = false ->
  tsubs M0c [cur; cur; am] = SVis (EMprotect (am + 4096) PGSZ PROT_RW) (am_kp AGK bail0 (m0_st2 (VB am)) (0%N, PGSZ)).
Proof.
  intros H1 HV HE. change (tsubs M0c [cur; cur; am]) with (tsub (tsubs M0c [cur; cur]) am).
  rewrite (M0c_2B cur H1). cbn [tsub]. unfold am_kb. rewrite live_ranges_brkdead.
  change (2 * PGSZ) with 8192. rewrite HV, HE. cbn [negb].
  change (am_finish (m0_st2 (VB am)) true AGK bail0 = SVis (EMprotect (am + 4096) PGSZ PROT_RW) (am_kp AGK bail0 (m0_st2 (VB am)) (0%N, PGSZ))).
  rewrite (am_finish_prot AGK bail0 _ (0%N, PGSZ)) by reflexivity. reflexivity.
Qed.

Lemma M0c_4B cur am mp : brk0_answer_ok cur = true ->
  mmap_answer_ok (resv ++ []) 8192 am = true -> is_err am = false ->
  mprotect_answer_ok mp = true -> (mp = 0 \/ mp = TWO64 - ENOSYS) ->
  tsubs M0c [cur; cur; am; mp] =
    SVis (EMmap 0 69632 PROT_RW (MAP_PRIVATE + MAP_ANON)) (ag_kmm lay_none 44 K2 bail0 (m0_st7 (VB am)) m0 1 69632).
Proof.
  intros H1 HV HE HM HM2. change (tsubs M0c [cur; cur; am; mp]) with (tsub (tsubs M0c [cur; cur; am]) mp).
  rewrite (M0c_3B cur am H1 HV HE). cbn [tsub]. unfold am_kp. rewrite HM. cbn [negb].
  replace ((mp =? 0) || (mp =? TWO64 - ENOSYS)) with true.
  2:{ symmetry. apply orb_true_iff. destruct HM2 as [-> | ->]; [left| right]; apply Z.eqb_refl. }
  rewrite am_carve_eq. change (fst _) with (m0_st6 (VB am)). change (snd _) with m0. apply AGK_st6.
Qed.

Lemma M0c_4B_fail cur am mp : brk0_answer_ok cur = true ->
  mmap_answer_ok (resv ++ []) 8192 am = true -> is_err am = false ->
  mprotect_answer_ok mp = true -> mp <> 0 -> mp <> TWO64 - ENOSYS ->
  tsubs M0c [cur; cur; am; mp] = ret (m0_st2 (VB am), None).
Proof.
  intros H1 HV HE HM N1 N2. change (tsubs M0c [cur; cur; am; mp]) with (tsub (tsubs M0c [cur; cur; am]) mp).
  rewrite (M0c_3B cur am H1 HV HE). cbn [tsub]. unfold am_kp. rewrite HM. cbn [negb].
  rewrite (proj2 (Z.eqb_neq _ _) N1), (proj2 (Z.eqb_neq _ _) N2). reflexivity.
Qed.

Lemma M0c_4B_bad cur am mp : brk0_answer_ok cur = true ->
  mmap_answer_ok (resv ++ []) 8192 am = true -> is_err am = false ->
  mprotect_answer_ok mp = false -> rejects (tsubs M0c [cur; cur; am; mp]).
Proof.
  intros H1 HV HE HM. change (tsubs M0c [cur; cur; am; mp]) with (tsub (tsubs M0c [cur; cur; am]) mp).
  rewrite (M0c_3B cur am H1 HV HE). cbn [tsub]. unfold am_kp. rewrite HM. exact I.
Qed.

(* [comment removed for export] *)
Lemma live_ranges_st7 v :
  live_ranges (m0_st7 v) = resv ++ [match v with VA cur => (round_up_pg cur + PGSZ, 4096) | VB am => (am, 8192) end].
Proof. destruct v; reflexivity. Qed.

Lemma ag_kmm_m0_err v r :
  mmap_answer_ok (live_ranges (m0_st7 v)) 69632 r = true -> is_err r = true ->
  ag_kmm lay_none 44 K2 bail0 (m0_st7 v) m0 1 69632 r = ret (fm_post m0 (m0_st7 v), None).
Proof. intros HV HE. etransitivity. { exact (ag_kmm_err lay_none 44 K2 bail0 (m0_st7 v) m0 1 69632 r HV HE). } unfold K2, K1. cbn [as_k2 msc_k Z.ltb mc_k]. reflexivity. Qed.

Lemma ag_kmm_m0_ok v r :
  mmap_answer_ok (live_ranges (m0_st7 v)) 69632 r = true -> is_err r = false ->
  ag_kmm lay_none 44 K2 bail0 (m0_st7 v) m0 1 69632 r = ret (m0_pre v r, Some (m0, 0)).
Proof.
  intros HV HE.
  etransitivity. { exact (ag_kmm_ok lay_none 44 K2 bail0 (m0_st7 v) m0 1 69632 r HV HE). }
  unfold K2. etransitivity. { apply as_k2_some; destruct v; reflexivity. }
  unfold K1. etransitivity. { apply (msc_k_zero 44 mc_k bail0 _ m0). destruct v; reflexivity. }
  unfold mc_k, m0_pre. reflexivity.
Qed.

Lemma ag_kmm_m0_bad v r :
  mmap_answer_ok (live_ranges (m0_st7 v)) 69632 r = false ->
  rejects (ag_kmm lay_none 44 K2 bail0 (m0_st7 v) m0 1 69632 r).
Proof. intros HV. apply ag_kmm_bad. exact HV. Qed.

Lemma slot_of_m0_pre v r : slot_of (m0_pre v r) m0 0 = (1%N, 16).
Proof. destruct v; reflexivity. Qed.

End M0.


End CeilWrap.
End MEX_m0.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_defs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MI_Tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MI_Kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_defs.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MEX_lib.
Export MEX_konts.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Export MEX_defs.
Export MEX_m0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
Definition ENOMEM_ans : Z := 2 ^ 64 - 12.

Lemma ENOMEM_ans_err : is_err ENOMEM_ans = true.
Proof. reflexivity. Qed.
Lemma ENOMEM_ans_ok live len : mmap_answer_ok live len ENOMEM_ans = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition one_mmap_site (cs : mstate) (n lo hi : Z) : Prop :=
  exists len k,
    cmalloc cs n = SVis (EMmap 0 len PROT_RW (MAP_PRIVATE + MAP_ANON)) k
    /\ lo <= len <= hi
    /\ (forall r, mmap_answer_ok (live_ranges cs) len r = false -> rejects (k r))
    /\ (forall r, mmap_answer_ok (live_ranges cs) len r = true -> is_err r = true -> exists csf, k r = SRet (csf, None))
    /\ (exists csf, k ENOMEM_ans = SRet (csf, None))
    /\ (forall r, ~ rejects (k r) -> is_err r = false -> exists cs' c, k r = SRet (cs', Some c)).

Definition big_site (cs : mstate) (n : Z) : Prop := one_mmap_site cs n (n + 20) (n + 20).
Definition small_site (cs : mstate) (n : Z) : Prop := one_mmap_site cs n 4096 (2 ^ 20).

(* [comment removed for export] *)
Definition big_site_stmt : Prop :=
  forall cs D fl lo n, RP cs D fl lo -> MMAP_THRESHOLD <= n <= 2 ^ 26 -> big_site cs n.

(* [comment removed for export] *)
Definition small_site_stmt : Prop :=
  forall cs D fl lo n, RP cs D fl lo -> 0 <= n < MMAP_THRESHOLD -> small_site cs n.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition d0 (r : Z) : dblk := mkDB 1%N r 69632 m0 44.

(* [comment removed for export] *)
Definition m0_intro_stmt : Prop :=
  forall resv ans cs' c,
    follow (cmalloc (cs0 resv) 65536) ans = Some (cs', Some c) ->
    exists v r, cs' = m0_post resv v r /\ c = (1%N, 16) /\ is_err r = false /\ RP1 cs' (d0 r).

(* [comment removed for export] *)
Definition big_follow_stmt : Prop :=
  forall cs d n ans cs' res,
    RP1 cs d -> MMAP_THRESHOLD <= n <= 2 ^ 26 ->
    follow (cmalloc cs n) ans = Some (cs', res) ->
    match res with
    | None => cs' = cs
    | Some c => exists dnew,
        RP2 cs' d dnew /\ c = db_slot dnew /\ db_sc dnew = 63 /\ db_len dnew = n + 20
        /\ db_rid dnew = s_next_rid cs /\ (exists r rest, ans = r :: rest /\ db_base dnew = r)
        /\ s_regions cs' !! db_rid dnew = Some (mkRegion RKGroup (db_base dnew) (n + 20))
    end.

(* [comment removed for export] *)
Definition free_site_stmt : Prop :=
  forall cs dold dnew, RP2 cs dold dnew ->
    exists k cs',
      cfree cs (Some (db_slot dold)) = SVis (EMunmap (db_base dold) (db_ml dold * 4096)) k
      /\ db_ml dold * 4096 = round_up_pg (db_len dold)
      /\ s_regions cs !! db_rid dold = Some (mkRegion RKGroup (db_base dold) (db_len dold))
      /\ (forall ru, munmap_answer_ok ru = true -> k ru = SRet cs')
      /\ (forall ru, munmap_answer_ok ru = false -> rejects (k ru))
      /\ RP1 cs' dnew /\ s_regions cs' !! db_rid dold = None
      /\ (forall rid, rid <> db_rid dold -> s_regions cs' !! rid = s_regions cs !! rid).

Definition free_follow_stmt : Prop :=
  forall cs dold dnew ans cs', RP2 cs dold dnew ->
    follow (cfree cs (Some (db_slot dold))) ans = Some cs' -> RP1 cs' dnew.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rp_bounds_stmt : Prop :=
  forall cs D fl lo, RP cs D fl lo ->
    (forall rid r, s_regions cs !! rid = Some r ->
       (rid = 0%N /\ r_len r = 2 * PGSZ /\ r_kind r <> RKGroup)
       \/ (exists d, In d D /\ rid = db_rid d /\ r = mkRegion RKGroup (db_base d) (db_len d)))
    /\ (forall d, In d D -> 0 < db_len d <= 2 ^ 26 + 20)
    /\ (length D <= 2)%nat
    /\ (size (s_regions cs) <= 3)%nat.


End CeilWrap.
