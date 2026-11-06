(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import STree Malloc KInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition MR (st : mstate) (m : aptr) : meta := get_meta_rec st m.
Definition cnt_of (r : meta) : Z := m_last_idx r + 1.

Definition gbase (r : meta) : aptr := default (0%N, 0) (m_mem r).

Definition sstart (r : meta) (i : Z) : Z := snd (gbase r) + UNIT + get_stride r * i.
Definition gend (r : meta) : Z := sstart r (cnt_of r).

Lemma slot_start'_sstart r i : slot_start' r i = (fst (gbase r), sstart r i).
Proof. unfold slot_start', sstart, gbase, aadd. destruct (m_mem r) as [[? ?]|]; cbn; f_equal; lia. Qed.

Definition hosts (st : mstate) (b m : aptr) : Prop :=
  exists ai, s_groups st !! b = Some (mkGhdr (Some m) ai).
Definition live_group (st : mstate) (m : aptr) : Prop := exists b, hosts st b m.

Definition blk : Type := (cptr * Z * Z)%type.
Definition bslot (b : blk) : cptr := fst (fst b).
Definition boff (b : blk) : Z := snd (fst b).
Definition bsize (b : blk) : Z := snd b.

Definition bptr_of (b : blk) : aptr := aadd (bslot b) (UNIT * boff b).

Fixpoint bl_remove (c : cptr) (l : list blk) : list blk :=
  match l with
  | [] => []
  | b :: l' => if aptr_eqb (bslot b) c then l' else b :: bl_remove c l'
  end.

Definition tbit (m i : Z) : bool := Z.testbit m i.

Definition zsum (l : list Z) : Z := fold_right Z.add 0 l.

Definition gcnt (st : mstate) (sc : Z) : Z :=
  zsum (map (fun bh : aptr * ghdr =>
               match g_meta (snd bh) with
               | Some m => if m_sizeclass (MR st m) =? sc then cnt_of (MR st m) else 0
               | None => 0
               end) (map_to_list (s_groups st))).

Definition frontier (st : mstate) (rid : N) (r : region) : Z :=
  match c_avail_meta_areas (s_ctx st) with
  | Some (rid0, off0) => if (rid0 =? rid)%N then off0 else r_len r
  | None => r_len r
  end.

Definition is_metakind (r : region) : Prop := r_kind r = RKBrk \/ r_kind r = RKMeta.

Definition mslot (a : aptr) (k : Z) : aptr := aadd a (AREA_HDR + META_SIZE * k).

Fixpoint linked (st : mstate) (l : list aptr) : Prop :=
  match l with
  | x :: ((y :: _) as t) => m_next (MR st x) = Some y /\ m_prev (MR st y) = Some x /\ linked st t
  | _ => True
  end.
Definition dll (st : mstate) (l : list aptr) : Prop :=
  match l with [] => True | a :: _ => linked st (l ++ [a]) end.
Definition head_of (l : list aptr) : optr := match l with [] => None | m :: _ => Some m end.

Record extras : Type := mkX {
  x_idle : list aptr;
  x_zomb : list aptr;
  x_pend : option aptr;
  x_orph : option N;
  x_fresh : option aptr
}.
Definition x0 : extras := mkX [] [] None None None.

Definition one5 (A B C D E : Prop) : Prop :=
  (A \/ B \/ C \/ D \/ E)
  /\ ~ (A /\ B) /\ ~ (A /\ C) /\ ~ (A /\ D) /\ ~ (A /\ E)
  /\ ~ (B /\ C) /\ ~ (B /\ D) /\ ~ (B /\ E)
  /\ ~ (C /\ D) /\ ~ (C /\ E) /\ ~ (D /\ E).

Section INV.
Variable X : extras.
Variable st : mstate.
Variable L : mled.
Variable BL : list blk.
Variable LS : lhead -> list aptr.
Let cx := s_ctx st.
Let R := MR st.
Definition in_list (m : aptr) : Prop := exists h, In m (LS h).

Record inv_R : Prop := mkIR {
  ir_ids : forall rid r, s_regions st !! rid = Some r -> (rid < s_next_rid st)%N;
  ir_shape : forall rid r, s_regions st !! rid = Some r ->
      0 < r_base r /\ r_base r mod PGSZ = 0 /\ 0 < r_len r /\ r_len r < LEN_MAX
      /\ r_base r + round_up_pg (r_len r) <= MCEIL
      /\ (is_metakind r -> r_len r mod PGSZ = 0 /\ 2 * PGSZ <= r_len r);
  ir_disj : forall rid1 rid2 r1 r2, s_regions st !! rid1 = Some r1 -> s_regions st !! rid2 = Some r2 -> rid1 <> rid2 ->
      let '(b1, l1) := region_live_range r1 in let '(b2, l2) := region_live_range r2 in
      b1 + l1 <= b2 \/ b2 + l2 <= b1;
  ir_resv : ld_resv L = s_reserved st;
  ir_groups : Permutation (ld_groups L)
      (map (fun kr => (r_base (snd kr), r_len (snd kr)))
           (List.filter (fun kr => match r_kind (snd kr) with RKGroup => true | _ => false end) (map_to_list (s_regions st))));
  ir_metas : Permutation (ld_metas L)
      (map (fun kr => (r_base (snd kr), r_len (snd kr), frontier st (fst kr) (snd kr) / PGSZ - 1))
           (List.filter (fun kr => match r_kind (snd kr) with RKMeta => true | _ => false end) (map_to_list (s_regions st))));
  ir_metalen : forall rid r, s_regions st !! rid = Some r -> r_kind r = RKMeta ->
      (exists j, 1 <= j /\ r_len r = 2^j * PGSZ)
      /\ PGSZ <= frontier st rid r <= r_len r /\ frontier st rid r mod PGSZ = 0;
  ir_brkfront : forall rid r, s_regions st !! rid = Some r -> r_kind r = RKBrk -> frontier st rid r = r_len r;
  ir_shift : 0 <= c_meta_alloc_shift cx /\
      (c_meta_alloc_shift cx = 0 \/
       exists rid r, s_regions st !! rid = Some r /\ r_kind r = RKMeta /\ r_len r = 2^(c_meta_alloc_shift cx) * PGSZ);
  ir_brkreg : forall b l, ld_brkreg L = Some (b, l) <->
      exists rid r, s_regions st !! rid = Some r /\ r_kind r = RKBrk /\ r_base r = b /\ r_len r = l;
  ir_brk1 : forall rid1 rid2 r1 r2, s_regions st !! rid1 = Some r1 -> s_regions st !! rid2 = Some r2 ->
      r_kind r1 = RKBrk -> r_kind r2 = RKBrk -> rid1 = rid2;
  ir_brk : match c_brk cx with
      | BrkUntried => ld_brk L = BPUntried /\ forall rid r, s_regions st !! rid = Some r -> r_kind r <> RKBrk
      | BrkLive rid off => ld_brk L = BPLive /\
          exists r, s_regions st !! rid = Some r /\ r_kind r = RKBrk /\ r_len r = off
      | BrkDead => ld_brk L = BPDead
      end;

  ir_cursor : 0 <= c_avail_meta_area_count cx /\
      (0 < c_avail_meta_area_count cx -> c_avail_meta_areas cx <> None) /\
      (forall rid off, c_avail_meta_areas cx = Some (rid, off) ->
       exists r, s_regions st !! rid = Some r /\ is_metakind r /\ PGSZ <= off /\ off mod PGSZ = 0
         /\ off + c_avail_meta_area_count cx * PGSZ = r_len r
         /\ (0 < c_avail_meta_area_count cx -> r_kind r = RKMeta));

  ir_orph : forall rid, x_orph X = Some rid ->
      exists r, s_regions st !! rid = Some r /\ r_kind r = RKGroup /\ forall b, fst b = rid -> s_groups st !! b = None
}.

Record inv_A : Prop := mkIA {
  ia_ctx : 0 <= c_mmap_counter cx < 2^32 /\ 0 <= c_seq cx < 256
      /\ (forall i v, c_bounces cx !! i = Some v -> 0 <= i < 32 /\ 0 <= v < 256)
      /\ (forall i v, c_unmap_seq cx !! i = Some v -> 0 <= i < 32 /\ 0 <= v < 256);
  ia_secret : 0 <= s_secret st < 2^64 /\
      ((c_init_done cx = 0 /\ c_secret cx = 0 /\ s_areas st = ∅) \/ (c_init_done cx = 1 /\ c_secret cx = s_secret st));

  ia_areas : forall a ar, s_areas st !! a = Some ar ->
      (exists r, s_regions st !! (fst a) = Some r /\ is_metakind r /\ snd a mod PGSZ = 0 /\ PGSZ <= snd a
                 /\ snd a + PGSZ <= frontier st (fst a) r)
      /\ a_check ar = c_secret cx /\ a_nslots ar = NSLOTS
      /\ (forall a', a_next ar = Some a' -> s_areas st !! a' <> None);
  ia_head : forall h, c_meta_area_head cx = Some h -> s_areas st !! h <> None;
  ia_tail : forall t, c_meta_area_tail cx = Some t -> s_areas st !! t <> None;
  ia_tail0 : c_meta_area_tail cx = None -> s_areas st = ∅ /\ c_avail_meta_count cx = 0;

  ia_metas : forall m mr, s_metas st !! m = Some mr ->
      exists a ar k, s_areas st !! a = Some ar /\ 0 <= k < NSLOTS /\ m = mslot a k;

  ia_avail : 0 <= c_avail_meta_count cx <= NSLOTS /\
      (0 < c_avail_meta_count cx ->
       exists a, c_meta_area_tail cx = Some a /\
         c_avail_meta cx = Some (mslot a (NSLOTS - c_avail_meta_count cx)) /\
         forall k, NSLOTS - c_avail_meta_count cx <= k < NSLOTS -> s_metas st !! (mslot a k) = None);
  ia_availptr : forall q, c_avail_meta cx = Some q ->
      exists r, s_regions st !! (fst q) = Some r /\ is_metakind r;

  ia_usage : forall sc, 0 <= sc < 48 -> usage st sc = gcnt st sc;
  ia_usage_keys : forall sc v, c_usage cx !! sc = Some v -> 0 <= sc < 48;
  ia_active_keys : forall sc g, c_active cx !! sc = Some g -> 0 <= sc < 48
}.

Record inv_M : Prop := mkIM {
  im_zero : forall m, m_mem (R m) = None ->
      R m = mkMeta (m_prev (R m)) (m_next (R m)) None 0 0 0 0 0 0;
  im_group : forall m b, m_mem (R m) = Some b -> hosts st b m \/ In m (x_zomb X);
  im_hdr : forall b h, s_groups st !! b = Some h ->
      exists m, g_meta h = Some m /\ m_mem (R m) = Some b /\ 0 <= g_active_idx h <= m_last_idx (R m);
  im_idle : forall m, In m (x_idle X) -> s_metas st !! m = Some meta0 /\ ~ in_list m;
  im_zomb : forall z, In z (x_zomb X) ->
      ~ in_list z /\ m_next (R z) = None /\ m_prev (R z) = None /\
      exists b, m_mem (R z) = Some b /\ s_groups st !! b = None
}.

Record inv_L : Prop := mkIL {
  il_head : forall h, get_head st h = head_of (LS h);
  il_dll : forall h, dll st (LS h);
  il_nodup : forall h, NoDup (LS h);
  il_disj : forall h1 h2 m, In m (LS h1) -> In m (LS h2) -> h1 = h2;
  il_link : forall m, (in_list m <-> m_next (R m) <> None) /\ (m_next (R m) = None -> m_prev (R m) = None);
  il_free : forall m, In m (LS LFree) -> R m = mkMeta (m_prev (R m)) (m_next (R m)) None 0 0 0 0 0 0;
  il_active : forall sc m, In m (LS (LActive sc)) -> 0 <= sc < 48 /\ live_group st m /\ m_sizeclass (R m) = sc;

  il_keys : forall h, LS h <> [] -> match h with LFree => True | LActive sc => 0 <= sc < 48 end
}.

Record group_ok (m b : aptr) (ai : Z) : Prop := mkG {
  g_present : s_metas st !! m <> None;
  g_li : 0 <= m_last_idx (R m) <= 31;
  g_ai : 0 <= ai <= m_last_idx (R m);
  g_sc : (0 <= m_sizeclass (R m) < 48 /\ m_maplen (R m) <= 256)
         \/ (m_sizeclass (R m) = 63 /\ m_last_idx (R m) = 0 /\ m_maplen (R m) <> 0 /\ ~ in_list m);
  g_freeable : m_freeable (R m) = 1;
  g_maplen : 0 <= m_maplen (R m);
  g_masks : 0 <= m_avail (R m) /\ 0 <= m_freed (R m)
      /\ (forall i, 0 <= i -> tbit (m_avail (R m)) i = true -> i <= ai)
      /\ (forall i, 0 <= i -> tbit (m_freed (R m)) i = true -> i <= m_last_idx (R m))
      /\ (forall i, 0 <= i -> tbit (m_avail (R m)) i = true -> tbit (m_freed (R m)) i = true -> False)
      /\ (forall i, ai < i <= m_last_idx (R m) -> tbit (m_freed (R m)) i = true);

  g_partial : x_fresh X <> Some m -> ai < m_last_idx (R m) -> In m (LS (LActive (m_sizeclass (R m))));
  g_unlisted : x_fresh X <> Some m -> m_sizeclass (R m) < 48 -> ~ in_list m -> m_avail (R m) = 0 /\ m_freed (R m) = 0;
  g_rest : x_fresh X <> Some m -> forall sc, In m (LS (LActive sc)) -> Some m <> head_of (LS (LActive sc)) ->
      m_avail (R m) = 0 /\ m_freed (R m) <> 0;

  g_stride : m_sizeclass (R m) < 48 ->
      (get_stride (R m) <= UNIT * size_class (m_sizeclass (R m)) \/ 28 <= m_sizeclass (R m))
      /\ (m_last_idx (R m) = 0 -> m_maplen (R m) <> 0 /\ 27 <= m_sizeclass (R m))
      /\ get_stride (R m) * cnt_of (R m) < 2^20;
  g_under : x_fresh X <> Some m -> m_sizeclass (R m) < 48 -> get_stride (R m) < UNIT * size_class (m_sizeclass (R m)) ->
      m_avail (R m) = 0 /\ m_freed (R m) = 0;
  g_align : 0 <= snd b /\ snd b mod UNIT = 0;

  g_top : m_maplen (R m) <> 0 ->
      snd b = 0 /\ exists r, s_regions st !! (fst b) = Some r /\ r_kind r = RKGroup
        /\ m_maplen (R m) * 4096 = round_up_pg (r_len r) /\ gend (R m) <= m_maplen (R m) * 4096;
  g_nest : m_maplen (R m) = 0 ->
      exists p i, s_slots st !! b = Some (p, i) /\ fst (gbase (R p)) = fst b
        /\ gend (R m) <= sstart (R p) i + get_stride (R p)
        /\ m_sizeclass (R m) < m_sizeclass (R p) < 48
        /\ get_stride (R p) = UNIT * size_class (m_sizeclass (R p));

  g_full0 : m_sizeclass (R m) = 0 -> ai = m_last_idx (R m)
}.

Record inv_G : Prop := mkIG {
  ig_ok : forall m b ai, s_groups st !! b = Some (mkGhdr (Some m) ai) -> group_ok m b ai;
  ig_nometa : forall b ai, s_groups st !! b = Some (mkGhdr None ai) -> False;
  ig_onepartial : forall m1 m2 b1 b2 ai1 ai2,
      s_groups st !! b1 = Some (mkGhdr (Some m1) ai1) -> s_groups st !! b2 = Some (mkGhdr (Some m2) ai2) ->
      ai1 < m_last_idx (R m1) -> ai2 < m_last_idx (R m2) -> m_sizeclass (R m1) = m_sizeclass (R m2) -> m1 = m2;

  ig_top : forall rid r, s_regions st !! rid = Some r -> r_kind r = RKGroup -> x_orph X <> Some rid ->
      exists m, hosts st (rid, 0) m /\ m_maplen (R m) <> 0;

  ig_region : forall b h, s_groups st !! b = Some h -> exists r, s_regions st !! (fst b) = Some r /\ r_kind r = RKGroup

}.

Record inv_S : Prop := mkIS {
  is_valid : forall s m i, s_slots st !! s = Some (m, i) ->
      live_group st m /\ 0 <= i <= m_last_idx (R m) /\ s = slot_start' (R m) i;
  is_total : forall b m i, hosts st b m -> 0 <= i <= m_last_idx (R m) ->
      s_slots st !! (slot_start' (R m) i) = Some (m, i);
  is_part : forall b m ai i, s_groups st !! b = Some (mkGhdr (Some m) ai) -> 0 <= i <= m_last_idx (R m) ->
      let s := slot_start' (R m) i in
      one5 (tbit (m_avail (R m)) i = true)
           (tbit (m_freed (R m)) i = true)
           (In s (map bslot BL))
           (s_groups st !! s <> None)
           (x_pend X = Some s);
  is_pend : forall s, x_pend X = Some s -> s_slots st !! s <> None;

  is_nodup : NoDup (map bslot BL);
  is_blocks : forall k, In k BL ->
      exists m i, s_slots st !! (bslot k) = Some (m, i)
        /\ 0 <= boff k <= 255 /\ 0 <= bsize k /\ UNIT * boff k + bsize k <= get_stride (R m) - IB
}.

Definition SHd (rid : N) : shadow := get_shadow st rid.
Definition known (p : aptr) (v : Z) : Prop := cell_read (SHd (fst p)) (snd p) = Known v.
Definition unknown (p : aptr) : Prop := exists h, cell_read (SHd (fst p)) (snd p) = Unknown h.
Definition byte_of (x : Z) (k : Z) : Z := Z.land (Z.shiftr x (8 * k)) 255.

Record inv_SH : Prop := mkISH {
  ish_dom : forall rid sh, s_shadow st !! rid = Some sh -> exists r, s_regions st !! rid = Some r /\ r_kind r = RKGroup;
  ish_ticks : forall rid sh, s_shadow st !! rid = Some sh ->
      (forall o v t, r_cells sh !! o = Some (v, t) -> 0 <= v < 256 /\ (t <= s_tick st)%N)
      /\ (forall u hl ch, r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= s_tick st)%N)
      /\ (forall pg t, r_havp sh !! pg = Some t -> (t <= s_tick st)%N);

  ish_hdr0 : forall b m i, hosts st b m -> 0 <= i <= cnt_of (R m) -> known (fst b, sstart (R m) i - IB) 0;

  ish_ghdr : forall b m o, hosts st b m -> 0 <= o < 12 -> unknown (fst b, snd b + o);

  ish_nest : forall b m p i, hosts st b m -> m_maplen (R m) = 0 -> s_slots st !! b = Some (p, i) ->
      let q := (snd b - snd (gbase (R p)) - UNIT) / UNIT in
      (exists v3, known (fst b, snd b - 3) v3 /\ Z.land v3 31 = i /\ 0 <= v3 < 256)
      /\ known (fst b, snd b - 2) (byte_of q 0) /\ known (fst b, snd b - 1) (byte_of q 1) /\ 0 <= q < 2^16;

  ish_blk : forall k m i, In k BL -> s_slots st !! (bslot k) = Some (m, i) ->
      let rid := fst (bslot k) in
      let p := snd (bslot k) + UNIT * boff k in
      let e := snd (bslot k) + get_stride (R m) - IB in
      let res := e - p - bsize k in
      let q := (p - snd (gbase (R m)) - UNIT) / UNIT in
      known (rid, p - 4) 0
      /\ known (rid, p - 3) (i + 32 * Z.min res 5)
      /\ known (rid, p - 2) (byte_of q 0) /\ known (rid, p - 1) (byte_of q 1) /\ 0 <= q < 2^16
      /\ (5 <= res -> known (rid, e - 4) (byte_of res 0) /\ known (rid, e - 3) (byte_of res 1)
                    /\ known (rid, e - 2) (byte_of res 2) /\ known (rid, e - 1) (byte_of res 3)
                    /\ known (rid, e - 5) 0 /\ res < 2^32)
      /\ (0 < res -> known (rid, e - res) 0)
      /\ (forall a, p <= a < p + bsize k -> unknown (rid, a))
}.

Definition INVL : Prop := inv_R /\ inv_A /\ inv_M /\ inv_L /\ inv_G /\ inv_S /\ inv_SH.
End INV.

Definition INV (X : extras) (st : mstate) (L : mled) (BL : list blk) : Prop :=
  exists LS, INVL X st L BL LS.

Definition FINV (st : mstate) (L : mled) (BL : list blk) : Prop := INV x0 st L BL.
