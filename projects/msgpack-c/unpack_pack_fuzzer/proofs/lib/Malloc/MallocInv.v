(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import STree Malloc KInv.
Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Local Open Scope Z_scope.

Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Definition MR (cs : mstate) (m : aptr) : meta := get_meta_rec cs m.
Definition cnt_of (r : meta) : Z := m_last_idx r + 1.
Definition stride_of (r : meta) : Z := get_stride r.

Definition gbase (r : meta) : aptr := default (0%N, 0) (m_mem r).

Definition sstart (r : meta) (i : Z) : Z := snd (gbase r) + UNIT + stride_of r * i.
Definition gend (r : meta) : Z := snd (gbase r) + UNIT + stride_of r * cnt_of r.

Lemma sstart_slot_start' : forall r i, slot_start' r i = (fst (gbase r), sstart r i).
Proof. intros r i. unfold slot_start', sstart, gbase, stride_of, aadd. destruct (m_mem r) as [[? ?]|]; cbn; f_equal; lia. Qed.

Definition is_gmeta (cs : mstate) (m : aptr) : Prop := exists g, m_mem (MR cs m) = Some g.

Definition hosts (cs : mstate) (b : aptr) (m : aptr) : Prop :=
  exists ai, s_groups cs !! b = Some (mkGhdr (Some m) ai).

Definition frontier (cs : mstate) (rid : N) (r : region) : Z :=
  match c_avail_meta_areas (s_ctx cs) with
  | Some (rid0, off0) => if (rid0 =? rid)%N then off0 else r_len r
  | None => r_len r
  end.

Definition meta_loc (cs : mstate) (m : aptr) : Prop :=
  exists r poff j, s_regions cs !! (fst m) = Some r /\ (r_kind r = RKBrk \/ r_kind r = RKMeta)
    /\ poff mod PGSZ = 0 /\ PGSZ <= poff /\ poff + PGSZ <= frontier cs (fst m) r
    /\ 0 <= j < NSLOTS /\ snd m = poff + AREA_HDR + META_SIZE * j.

Definition znth {A} (d : A) (l : list A) (k : Z) : A := nth (Z.to_nat k) l d.
Definition dll (cs : mstate) (l : list aptr) : Prop :=
  let n := Z.of_nat (length l) in
  forall k, 0 <= k < n ->
    m_next (MR cs (znth (0%N,0) l k)) = Some (znth (0%N,0) l ((k + 1) mod n))
    /\ m_prev (MR cs (znth (0%N,0) l k)) = Some (znth (0%N,0) l ((k - 1) mod n)).

Definition head_of (l : list aptr) : optr := match l with [] => None | m :: _ => Some m end.

Definition partial (r : meta) (ai : Z) : Prop := ai < m_last_idx r.

Definition testbit (m i : Z) : bool := Z.testbit m i.

Section MINV.
Variable cs : mstate.
Variable L : mled.
Variable LS : lhead -> list aptr.
Let cx := s_ctx cs.
Let MRc := MR cs.

Record minv_regions : Prop := mkIR {
  ir_ids : forall rid r, s_regions cs !! rid = Some r -> (rid < s_next_rid cs)%N;
  ir_shape : forall rid r, s_regions cs !! rid = Some r ->
      0 < r_base r /\ r_base r mod PGSZ = 0 /\ 0 < r_len r /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling;
  ir_resv : ld_resv L = s_reserved cs;
  ir_groups : Permutation (ld_groups L)
      (map (fun kr => (r_base (snd kr), r_len (snd kr))) (List.filter (fun kr => match r_kind (snd kr) with RKGroup => true | _ => false end) (map_to_list (s_regions cs))));
  ir_metas : Permutation (ld_metas L)
      (map (fun kr => (r_base (snd kr), r_len (snd kr), frontier cs (fst kr) (snd kr) / PGSZ - 1))
           (List.filter (fun kr => match r_kind (snd kr) with RKMeta => true | _ => false end) (map_to_list (s_regions cs))));
  ir_metalen : forall rid r, s_regions cs !! rid = Some r -> r_kind r = RKMeta ->
      exists j, 0 <= j /\ r_len r = 2^j * PGSZ /\ PGSZ <= frontier cs rid r <= r_len r /\ frontier cs rid r mod PGSZ = 0;
  ir_shift : 0 <= c_meta_alloc_shift cx /\
      (c_meta_alloc_shift cx = 0 \/ exists rid r, s_regions cs !! rid = Some r /\ r_kind r = RKMeta /\ r_len r = 2^(c_meta_alloc_shift cx) * PGSZ);
  ir_brkreg : forall b l, ld_brkreg L = Some (b, l) <->
      exists rid r, s_regions cs !! rid = Some r /\ r_kind r = RKBrk /\ r_base r = b /\ r_len r = l;
  ir_brk1 : forall rid1 rid2 r1 r2, s_regions cs !! rid1 = Some r1 -> s_regions cs !! rid2 = Some r2 ->
      r_kind r1 = RKBrk -> r_kind r2 = RKBrk -> rid1 = rid2;
  ir_brk : match c_brk cx with
      | BrkUntried => ld_brk L = BPUntried /\ ld_brkreg L = None
      | BrkLive rid off => ld_brk L = BPLive /\ exists r, s_regions cs !! rid = Some r /\ r_kind r = RKBrk /\ r_len r = off
            /\ PGSZ < off /\ off mod PGSZ = 0 /\ frontier cs rid r = off
      | BrkDead => ld_brk L = BPDead /\ forall rid r, s_regions cs !! rid = Some r -> r_kind r = RKBrk -> frontier cs rid r = r_len r
      end;

  ir_cursor : 0 <= c_avail_meta_area_count cx /\
      (0 < c_avail_meta_area_count cx ->
       exists rid off r, c_avail_meta_areas cx = Some (rid, off) /\ s_regions cs !! rid = Some r /\ r_kind r = RKMeta
         /\ off + c_avail_meta_area_count cx * PGSZ = r_len r) /\
      (forall rid off, c_avail_meta_areas cx = Some (rid, off) ->
       exists r, s_regions cs !! rid = Some r /\ (r_kind r = RKBrk \/ r_kind r = RKMeta) /\ PGSZ <= off <= r_len r /\ off mod PGSZ = 0)
}.

Record minv_metas : Prop := mkIM {
  im_loc : forall m r, s_metas cs !! m = Some r -> meta_loc cs m;

  im_avail : 0 <= c_avail_meta_count cx <= NSLOTS /\
      (0 < c_avail_meta_count cx ->
       exists a, c_meta_area_tail cx = Some a /\ meta_loc cs (aadd a (AREA_HDR + META_SIZE * 0)) /\ snd a mod PGSZ = 0 /\
         c_avail_meta cx = Some (aadd a (AREA_HDR + META_SIZE * (NSLOTS - c_avail_meta_count cx))) /\
         forall j, NSLOTS - c_avail_meta_count cx <= j < NSLOTS -> s_metas cs !! (aadd a (AREA_HDR + META_SIZE * j)) = None);

  im_status : forall m, m_mem (MRc m) = None ->
      MRc m = mkMeta (m_prev (MRc m)) (m_next (MRc m)) None 0 0 0 0 0 0;

  im_group : forall m g, m_mem (MRc m) = Some g -> exists ai, s_groups cs !! g = Some (mkGhdr (Some m) ai) /\ s_metas cs !! m <> None;
  im_hdr : forall g h, s_groups cs !! g = Some h ->
      exists m, g_meta h = Some m /\ m_mem (MRc m) = Some g /\ 0 <= g_active_idx h <= m_last_idx (MRc m)
}.

Definition in_list (m : aptr) : Prop := exists h, In m (LS h).
Record minv_lists : Prop := mkIL {
  il_head : forall h, get_head cs h = head_of (LS h);
  il_dll : forall h, dll cs (LS h);
  il_nodup : forall h, List.NoDup (LS h);
  il_disj : forall h1 h2 m, In m (LS h1) -> In m (LS h2) -> h1 = h2;
  il_link : forall m, (in_list m <-> m_next (MRc m) <> None) /\ (m_next (MRc m) = None -> m_prev (MRc m) = None);
  il_free : forall m, In m (LS LFree) -> m_mem (MRc m) = None /\ s_metas cs !! m <> None;
  il_active : forall sc m, In m (LS (LActive sc)) -> 0 <= sc < 48 /\ is_gmeta cs m /\ m_sizeclass (MRc m) = sc;
  il_rest : forall sc m, In m (LS (LActive sc)) -> Some m <> head_of (LS (LActive sc)) ->
      m_avail (MRc m) = 0 /\ m_freed (MRc m) <> 0;
  il_keys : forall sc, LS (LActive sc) <> [] -> 0 <= sc < 48
}.

Record group_ok (m : aptr) (g : aptr) (ai : Z) : Prop := mkG {
  g_li : 0 <= m_last_idx (MRc m) <= 31;
  g_ai : 0 <= ai <= m_last_idx (MRc m);
  g_sc : (0 <= m_sizeclass (MRc m) < 48) \/ (m_sizeclass (MRc m) = 63 /\ m_last_idx (MRc m) = 0 /\ m_maplen (MRc m) <> 0);
  g_freeable : m_freeable (MRc m) = 1;
  g_maplen : 0 <= m_maplen (MRc m);
  g_stride : UNIT <= stride_of (MRc m) /\ stride_of (MRc m) mod UNIT = 0;
  g_masks : 0 <= m_avail (MRc m) /\ 0 <= m_freed (MRc m) /\
      (forall b, 0 <= b -> testbit (m_avail (MRc m)) b = true -> b <= ai) /\
      (forall b, 0 <= b -> testbit (m_freed (MRc m)) b = true -> b <= m_last_idx (MRc m)) /\
      (forall b, 0 <= b -> testbit (m_avail (MRc m)) b = true -> testbit (m_freed (MRc m)) b = true -> False) /\
      (forall b, ai < b <= m_last_idx (MRc m) -> testbit (m_freed (MRc m)) b = true);

  g_listed63 : m_sizeclass (MRc m) = 63 -> ~ in_list m;
  g_partial : partial (MRc m) ai -> In m (LS (LActive (m_sizeclass (MRc m))));
  g_under : stride_of (MRc m) < UNIT * size_class (m_sizeclass (MRc m)) -> m_sizeclass (MRc m) < 48 ->
      m_last_idx (MRc m) = 0 /\ testbit (m_avail (MRc m)) 0 = false /\ testbit (m_freed (MRc m)) 0 = false;

  g_top : m_maplen (MRc m) <> 0 ->
      snd g = 0 /\ exists r, s_regions cs !! (fst g) = Some r /\ r_kind r = RKGroup /\
        m_maplen (MRc m) * 4096 = round_up_pg (r_len r) /\ gend (MRc m) <= m_maplen (MRc m) * 4096;
  g_nest : m_maplen (MRc m) = 0 ->
      exists p i, s_slots cs !! g = Some (p, i) /\ gend (MRc m) - snd g <= stride_of (MRc p) - IB /\
        m_sizeclass (MRc m) < m_sizeclass (MRc p) < 48
}.

Record minv_groups : Prop := mkIG {
  ig_ok : forall m g ai, s_groups cs !! g = Some (mkGhdr (Some m) ai) -> group_ok m g ai;
  ig_onepartial : forall m1 m2 g1 g2 ai1 ai2,
      s_groups cs !! g1 = Some (mkGhdr (Some m1) ai1) -> s_groups cs !! g2 = Some (mkGhdr (Some m2) ai2) ->
      partial (MRc m1) ai1 -> partial (MRc m2) ai2 -> m_sizeclass (MRc m1) = m_sizeclass (MRc m2) -> m1 = m2;
  ig_top : forall rid r, s_regions cs !! rid = Some r -> r_kind r = RKGroup -> exists m, hosts cs (rid, 0) m
}.

Record minv_slots : Prop := mkIS {
  is_valid : forall s m i, s_slots cs !! s = Some (m, i) ->
      is_gmeta cs m /\ 0 <= i <= m_last_idx (MRc m) /\ s = slot_start' (MRc m) i;
  is_total : forall m g i, m_mem (MRc m) = Some g -> 0 <= i <= m_last_idx (MRc m) ->
      s_slots cs !! (slot_start' (MRc m) i) = Some (m, i);

  is_part : forall m g ai i, s_groups cs !! g = Some (mkGhdr (Some m) ai) -> 0 <= i <= m_last_idx (MRc m) ->
      let s := slot_start' (MRc m) i in
      let A := testbit (m_avail (MRc m)) i = true in
      let F := testbit (m_freed (MRc m)) i = true in
      let U := In s (ld_live L) in
      let H := s_groups cs !! s <> None in
      (A \/ F \/ U \/ H) /\ ~ (A /\ F) /\ ~ (A /\ U) /\ ~ (A /\ H) /\ ~ (F /\ U) /\ ~ (F /\ H) /\ ~ (U /\ H);
  is_live : forall c, In c (ld_live L) -> s_slots cs !! c <> None;
  is_live_nodup : List.NoDup (ld_live L);
  is_hosted : forall b h, s_groups cs !! b = Some h -> snd b = 0 \/ s_slots cs !! b <> None
}.

Definition span_in (r1 r2 : meta) : Prop :=
  fst (gbase r1) = fst (gbase r2) /\ snd (gbase r2) <= snd (gbase r1) /\ gend r1 <= gend r2.
Definition nest_in (m1 m2 : aptr) : Prop :=
  exists i b, 0 <= i <= m_last_idx (MRc m2) /\ fst (gbase (MRc m1)) = fst (gbase (MRc m2)) /\
    sstart (MRc m2) i <= snd (gbase (MRc m1)) /\ gend (MRc m1) <= sstart (MRc m2) i + stride_of (MRc m2) /\
    hosts cs (fst (gbase (MRc m2)), sstart (MRc m2) i) b /\ span_in (MRc m1) (MRc b).
Record minv_geom : Prop := mkIGe {
  ige_lam : forall m1 m2, is_gmeta cs m1 -> is_gmeta cs m2 -> m1 <> m2 ->
      fst (gbase (MRc m1)) = fst (gbase (MRc m2)) ->
      gend (MRc m1) <= snd (gbase (MRc m2)) \/ gend (MRc m2) <= snd (gbase (MRc m1)) \/ nest_in m1 m2 \/ nest_in m2 m1;
  ige_intop : forall m, is_gmeta cs m -> exists t, hosts cs (fst (gbase (MRc m)), 0) t /\ span_in (MRc m) (MRc t)
}.

Definition MINVL : Prop :=
  minv_regions /\ minv_metas /\ minv_lists /\ minv_groups /\ minv_slots /\ minv_geom
  /\ c_free_meta_head cx = head_of (LS LFree) /\ (forall sc, active cs sc = head_of (LS (LActive sc))).
End MINV.

Definition MINV (cs : mstate) (L : mled) : Prop := exists LS, MINVL cs L LS.

End CEIL.
