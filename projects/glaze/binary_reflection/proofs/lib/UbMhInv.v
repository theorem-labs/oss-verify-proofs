(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition znth (l : list Z) (k : Z) : Z := nth (Z.to_nat k) l 0.
Definition zlen (l : list Z) : Z := Z.of_nat (length l).
Definition head_of (l : list Z) : Z := match l with [] => 0 | m :: _ => m end.

Section WithState.
Context {RN : mh_run}.
Variable st : mst.
Variable L : list (Z * Z).

Let cx := s_ctx st.
Let MRc := s_meta st.
Let areas := s_areas st.
Let groups := s_groups st.
Let regions := s_regions st.

#[local] Notation gW m := (g_W st m).
#[local] Notation gmem m := (g_mem st m).
#[local] Notation glast m := (g_lastidx st m).
#[local] Notation gcnt m := (g_cnt st m).
#[local] Notation gsc m := (g_sc st m).
#[local] Notation gml m := (g_maplen st m).
#[local] Notation gstride m := (g_stride st m).
#[local] Notation gss m i := (g_slot_start st m i).
#[local] Notation gse m i := (g_slot_end st m i).
#[local] Notation gai m := (s_ai st m).
#[local] Notation gslot m i := (s_slot st m i).
#[local] Notation gav m := (mr_avail (s_meta st m)).
#[local] Notation gfr m := (mr_freed (s_meta st m)).

(* [comment removed for export] *)
Definition metaU (m : Z) : Prop := is_meta_of areas m.
Definition in_alist (m : Z) : Prop := exists sc, 0 <= sc < 48 /\ In m (s_alist st sc).
Definition in_flist (m : Z) : Prop := In m (s_flist st).
Definition listed (m : Z) : Prop := in_flist m \/ in_alist m.
Definition is_group (m : Z) : Prop := In m groups.

(* [comment removed for export] *)
Definition fresh (m : Z) : Prop :=
  c_avail_cnt cx > 0 /\ exists k, NSLOTS - c_avail_cnt cx <= k < NSLOTS /\ m = meta_addr (last areas 0) k.

(* [comment removed for export] *)
Definition dll (l : list Z) : Prop :=
  forall k, 0 <= k < zlen l ->
    mr_next (MRc (znth l k)) = znth l ((k + 1) mod zlen l) /\
    mr_prev (MRc (znth l k)) = znth l ((k - 1) mod zlen l).

(* [comment removed for export] *)
Definition inband (m p : Z) : Z := (p - gmem m - UNIT) / UNIT.

(* [comment removed for export] *)
Definition ptr_ok (m i p : Z) : Prop :=
  p mod 16 = 0 /\ gmem m + UNIT <= p /\ (p - gmem m - UNIT) mod UNIT = 0 /\
  0 <= inband m p < 2 ^ 16 /\
  (gsc m < 48 -> size_class (gsc m) * i <= inband m p < size_class (gsc m) * (i + 1)) /\
  (gml m <> 0 -> inband m p <= gml m * 256 - 1).

(* [comment removed for export] *)
Definition gspan (m : Z) : Z := g_span_end st m.
(* [comment removed for export] *)
Definition endb_own (m : Z) : Prop :=
  match s_kind st m with GTop => True | GNest hm j _ => gspan m - 1 < gse hm j end.
(* [comment removed for export] *)
Definition slot_ptr (m k : Z) : option Z :=
  match gslot m k with SUser p _ _ _ => Some p | SHost _ off => Some (gss m k + 16 * off) | SJunk off => Some (gss m k + 16 * off) | _ => None end.
(* [comment removed for export] *)
Definition gcell (m a : Z) : Prop :=
     (gmem m <= a < gmem m + 12)   (* [comment removed for export] *)
  \/ (exists k, 0 <= k <= gcnt m /\ a = gss m k - 4 /\ (k < gcnt m \/ endb_own m))
  \/ (exists k q, 0 <= k <= glast m /\ slot_ptr m k = Some q /\ q - 4 <= a < q)
  \/ (exists k p n off res, 0 <= k <= glast m /\ gslot m k = SUser p n off res /\
        ((0 < res /\ a = p + n) \/ (5 <= res /\ gse m k - 5 <= a < gse m k))).
(* [comment removed for export] *)
Definition appb (a : Z) : Prop :=
  exists m k p n off res, is_group m /\ 0 <= k <= glast m /\ gslot m k = SUser p n off res /\ p <= a < p + n.
(* [comment removed for export] *)
Definition garbage (m k a : Z) : Prop :=
  0 <= k <= glast m /\
  match gslot m k with
  | SAvail | SFreed => gss m k - 3 <= a < gse m k
  | SUser p n off res => (gss m k - 3 <= a < p - 4) \/ (p + n < a /\ a < gse m k - 5) \/ (p + n < a /\ res < 5 /\ a < gse m k)
  | SHost c off => (gss m k - 3 <= a < gss m k + 16 * off - 4) \/ (gspan c <= a < gse m k)
  | SJunk off => (gss m k - 3 <= a < gss m k + 16 * off - 4) \/ (gss m k + 16 * off <= a < gse m k)
  end.
(* [comment removed for export] *)
Definition areab (a : Z) : Prop := exists ar, In ar areas /\ ar <= a < ar + 4096.

(* [comment removed for export] *)
Fixpoint nest_depth_le (fuel : nat) (m : Z) : Prop :=
  match s_kind st m with
  | GTop => True
  | GNest hm _ _ => match fuel with O => False | S f => nest_depth_le f hm end
  end.
(* [comment removed for export] *)
Definition dbound (s : Z) : nat := Z.to_nat (Z.log2 (2064 / (s + 16))).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record wf_ctx : Prop := WFC {
  wc_secret : 0 <= c_secret cx < 2 ^ 64;
  wc_ctr : 0 <= c_mmap_ctr cx < 2 ^ 32;
  wc_fhead : c_free_head cx = head_of (s_flist st);
  wc_active : forall sc, 0 <= sc < 48 -> c_active cx sc = head_of (s_alist st sc);
  wc_acnt : 0 <= c_avail_cnt cx <= NSLOTS - 1;
  wc_ameta : c_avail_cnt cx > 0 -> areas <> [] /\ c_avail_meta cx = meta_addr (last areas 0) (NSLOTS - c_avail_cnt cx);
  wc_areacnt : 0 <= c_area_cnt cx;
  wc_cursor : c_area_cnt cx > 0 ->
      exists b len e, In (RG b len (RMeta e)) regions /\ 0 <= e /\
        c_cursor cx = b + 4096 * (1 + e) /\ c_cursor cx + 4096 * c_area_cnt cx = b + len;
  wc_shift : 0 <= c_shift cx /\ c_shift cx <= Z.of_nat (length areas) + 1 /\
             (c_area_cnt cx = 0 -> c_shift cx <= Z.of_nat (length areas));
     (* [comment removed for export] *)
  wc_head : c_area_head cx = head_of areas;
  wc_tail : c_area_tail cx = last areas 0;
  wc_brk : match s_brk st with
           | BrkUntried => c_brk cx = 0
           | BrkLive b0 b _ => c_brk cx = b /\ b0 mod 4096 = 0 /\ b mod 4096 = 0 /\ IMG_HI <= b0 /\ b0 + 8192 <= b /\ b <= CEIL
           | BrkDead _ => c_brk cx = 2 ^ 64 - 1
           end;
  wc_usage : forall sc, 0 <= c_usage cx sc < 2 ^ 64;
  wc_useq : forall i, 0 <= c_unmap_seq cx i < 256;
  wc_bnc : forall i, 0 <= c_bounces cx i < 256;
  wc_seq : 0 <= c_seq cx < 256;
  wc_canary : 0 <= s_canary st < 2 ^ 64;
  wc_errno : 0 <= s_errno st < 2 ^ 32;
  (* [comment removed for export] *)
  wc_shacc : 2 ^ (c_shift cx + 1) <= Z.of_nat (length areas) + c_area_cnt cx + c_shift cx + 2
}.

Record wf_areas : Prop := WFA {
  wa_rng : forall a, In a areas -> a mod 4096 = 0 /\ HEAPLO <= a /\ a + 4096 <= CEIL;
  wa_nodup : NoDup areas;
  wa_cnt : Z.of_nat (length areas) <= AREAMAX;
  (* [comment removed for export] *)
  wa_inreg : forall a, In a areas ->
      (exists b len, In (RG b len RBrk) regions /\ b <= a /\ a + 4096 <= b + len /\
                     match guard_of (s_brk st) with Some b0 => b0 + 4096 <= a | None => True end)
      \/ (exists b len e, In (RG b len (RMeta e)) regions /\ b + 4096 <= a /\ a + 4096 <= b + 4096 * (1 + e))
}.

Record wf_lists : Prop := WFL {
  wl_fdll : dll (s_flist st);
  wl_fnodup : NoDup (s_flist st);
  wl_fU : forall m, in_flist m -> metaU m /\ ~ is_group m /\ ~ fresh m /\
            mr_mem (MRc m) = 0 /\ mr_avail (MRc m) = 0 /\ mr_freed (MRc m) = 0 /\ mr_W (MRc m) = 0;
  wl_adll : forall sc, 0 <= sc < 48 -> dll (s_alist st sc);
  wl_anodup : forall sc, NoDup (s_alist st sc);
  wl_aU : forall sc m, In m (s_alist st sc) -> 0 <= sc < 48 /\ is_group m /\ gsc m = sc;
  wl_anil : forall sc, ~ (0 <= sc < 48) -> s_alist st sc = [];
  (* [comment removed for export] *)
  wl_link : forall m, metaU m -> ~ listed m -> mr_next (MRc m) = 0 /\ mr_prev (MRc m) = 0;
  wl_linked : forall m, listed m -> mr_next (MRc m) <> 0 /\ mr_prev (MRc m) <> 0;
  (* [comment removed for export] *)
  wl_rest : forall sc m, In m (s_alist st sc) -> m <> head_of (s_alist st sc) -> gav m = 0 /\ gfr m <> 0
}.

(* [comment removed for export] *)
Definition slot_wf (m i : Z) (s : slot_st) : Prop :=
  match s with
  | SAvail => True
  | SFreed => True
  | SUser p n off res =>
      0 <= off /\ 0 <= n /\ p = gss m i + 16 * off /\ res = gstride m - IB - n - 16 * off /\ 0 <= res < 2 ^ 31 /\
      ptr_ok m i p /\ In (p, n) L
  | SHost m' off =>
      0 <= off /\ is_group m' /\ m' <> m /\ s_kind st m' = GNest m i off /\ ptr_ok m i (gss m i + 16 * off)
  | SJunk off =>
      0 <= off /\ 16 * off <= gstride m - IB /\ ptr_ok m i (gss m i + 16 * off)
  end.

Record wf_group (m : Z) : Prop := WFG {
  wg_U : metaU m;
  wg_notfresh : ~ fresh m;
  wg_Wr : 0 <= gW m < 2 ^ 64;
  wg_avr : 0 <= gav m < 2 ^ 32;
  wg_frr : 0 <= gfr m < 2 ^ 32;
  wg_mem : 0 < gmem m /\ gmem m mod 16 = 0 /\ gmem m + UNIT + gstride m * gcnt m < 2 ^ 47;
  wg_ai : 0 <= gai m <= glast m;
  wg_freeable : w_freeable (gW m) = 1;
  wg_sc : gsc m < 48 \/ (gsc m = 63 /\ glast m = 0 /\ gml m > 0);
  wg_stride : 16 <= gstride m /\ gstride m mod 16 = 0;
  (* [comment removed for export] *)
  wg_av : forall i, 0 <= i -> (Z.testbit (gav m) i = true <-> (i <= glast m /\ gslot m i = SAvail));
  wg_fr : forall i, 0 <= i -> (Z.testbit (gfr m) i = true <-> (i <= glast m /\ gslot m i = SFreed));
  wg_avai : forall i, 0 <= i <= glast m -> gslot m i = SAvail -> i <= gai m;            (* [comment removed for export] *)
  wg_high : forall i, gai m < i <= glast m -> gslot m i = SFreed;                         (* [comment removed for export] *)
  (* [comment removed for export] *)
  wg_listed_sc : in_alist m -> In m (s_alist st (gsc m));
  wg_notfree : ~ in_flist m;
  wg_63 : gsc m = 63 -> ~ listed m;
  wg_partial : gai m < glast m -> In m (s_alist st (gsc m));                              (* [comment removed for export] *)
  wg_full : (forall i, 0 <= i <= glast m -> gslot m i <> SAvail /\ gslot m i <> SFreed) ->
            m <> head_of (s_alist st (gsc m)) -> ~ listed m;
  (* [comment removed for export] *)
  wg_kind : match s_kind st m with
            | GTop => gml m > 0 /\ In (RG (gmem m) (4096 * gml m) (RGroup m)) regions /\ gmem m mod 4096 = 0 /\
                      UNIT + gcnt m * gstride m <= 4096 * gml m
            | GNest hm hi hoff => gml m = 0 /\ is_group hm /\ hm <> m /\ 0 <= hi <= glast hm /\ 0 <= hoff /\
                      gslot hm hi = SHost m hoff /\ gsc m < gsc hm /\ gsc hm < 48 /\
                      gmem m = gss hm hi + 16 * hoff /\
                      UNIT + gcnt m * gstride m - IB <= gstride hm - IB - 16 * hoff /\
                      2 <= gcnt m /\ UNIT + gcnt m * gstride m <= 2048
            end;
  wg_under : gsc m < 48 -> gstride m < UNIT * size_class (gsc m) -> glast m = 0;
  (* [comment removed for export] *)
  wg_fullfree : (forall k, 0 <= k <= glast m -> gslot m k = SAvail \/ gslot m k = SFreed) ->
                s_kind st m = GTop /\ gsc m < 48 /\ In m (s_alist st (gsc m));
  wg_slots : forall i, 0 <= i <= glast m -> slot_wf m i (gslot m i);
  wg_dbound : nest_depth_le (dbound (gstride m)) m;
  (* [comment removed for export] *)
  wg_fit : gsc m < 48 -> gstride m < UNIT * size_class (gsc m) -> forall i, 0 <= i <= glast m -> gslot m i <> SAvail /\ gslot m i <> SFreed;
  (* [comment removed for export] *)
  wg_single : s_kind st m = GTop -> gsc m < 48 -> glast m = 0 ->
      gstride m < UNIT * size_class (gsc m) \/
      (4096 * gml m = page_round_up_Z (UNIT * size_class (gsc m) + UNIT) /\ 2048 < UNIT * size_class (gsc m) + UNIT);
  (* [comment removed for export] *)
  wg_q : gsc m < 48 -> gstride m * gcnt m <= 2 ^ 20;
  (* [comment removed for export] *)
  wg_pnd : gai m < glast m -> 4096 mod gstride m <> 0
}.

Lemma nest_depth_mono : forall f f' m, (f <= f')%nat -> nest_depth_le f m -> nest_depth_le f' m.
Proof.
  induction f as [|f IH]; intros f' m Hle D; cbn in D |- *; destruct f' as [|f'']; cbn; destruct (s_kind st m) as [|hm j o]; try exact I; try exact D.
  - destruct D.
  - lia.
  - apply (IH f''); [lia | exact D].
Qed.
Lemma dbound_le7 : forall s, 0 <= s -> (dbound s <= 7)%nat.
Proof.
  intros s Hs. unfold dbound.
  assert (Hq : 0 <= 2064 / (s + 16) <= 129).
  { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; lia. }
  destruct (Z.eq_dec (2064 / (s + 16)) 0) as [E|NE]; [rewrite E; cbn; lia|].
  assert (Hl : Z.log2 (2064 / (s + 16)) < 8).
  { apply Z.log2_lt_pow2; [lia|]. change (2 ^ 8) with 256. lia. }
  pose proof (Z.log2_nonneg (2064 / (s + 16))). lia.
Qed.
Lemma wg_depth : forall m, wf_group m -> nest_depth_le 8 m.
Proof.
  intros m W. apply (nest_depth_mono (dbound (gstride m))); [|exact (wg_dbound m W)].
  pose proof (dbound_le7 (gstride m) ltac:(pose proof (wg_stride m W); lia)). lia.
Qed.

Record wf_groups : Prop := WFGS {
  wG_nodup : NoDup groups;
  wG_each : forall m, is_group m -> wf_group m;
  (* [comment removed for export] *)
  wG_onepartial : forall m1 m2, is_group m1 -> is_group m2 ->
      gai m1 < glast m1 -> gai m2 < glast m2 -> gsc m1 = gsc m2 -> m1 = m2;
  (* [comment removed for export] *)
  wG_regions : forall b len m, In (RG b len (RGroup m)) regions -> is_group m /\ s_kind st m = GTop /\ b = gmem m /\ len = 4096 * gml m;
  (* [comment removed for export] *)
  wG_fresh0 : forall m, fresh m -> MRc m = meta_zero;
  (* [comment removed for export] *)
  wG_meta_other : forall m, metaU m -> ~ is_group m -> ~ in_flist m -> ~ fresh m -> In m (s_limbo st);
  wG_limbo : forall m, In m (s_limbo st) -> metaU m /\ ~ is_group m /\ ~ listed m /\ ~ fresh m;
  (* [comment removed for export] *)
  wG_oneff : forall m1 m2, is_group m1 -> is_group m2 ->
      (forall k, 0 <= k <= glast m1 -> gslot m1 k = SAvail \/ gslot m1 k = SFreed) ->
      (forall k, 0 <= k <= glast m2 -> gslot m2 k = SAvail \/ gslot m2 k = SFreed) ->
      gsc m1 = gsc m2 -> m1 = m2
}.

(* [comment removed for export] *)
Record wf_geom : Prop := WFGE {
  (* [comment removed for export] *)
  ge_inreg : forall m, is_group m -> exists r, In r regions /\ rg_base r <= gmem m /\ gspan m <= rg_base r + rg_len r;
  (* [comment removed for export] *)
  ge_cells : forall m1 m2 a, is_group m1 -> is_group m2 -> m1 <> m2 -> gcell m1 a -> gcell m2 a -> False;
  (* [comment removed for export] *)
  ge_area : forall m a, is_group m -> gmem m <= a < gspan m -> areab a -> False;
  (* [comment removed for export] *)
  ge_app_cell : forall m a, is_group m -> gcell m a -> appb a -> False;
  ge_app_area : forall a, appb a -> areab a -> False;
  (* [comment removed for export] *)
  ge_app_disj : forall m1 k1 m2 k2 p1 n1 o1 r1 p2 n2 o2 r2,
      is_group m1 -> is_group m2 -> 0 <= k1 <= glast m1 -> 0 <= k2 <= glast m2 ->
      gslot m1 k1 = SUser p1 n1 o1 r1 -> gslot m2 k2 = SUser p2 n2 o2 r2 -> (m1, k1) <> (m2, k2) ->
      p1 + n1 <= p2 \/ p2 + n2 <= p1;
  (* [comment removed for export] *)
  ge_garb_cell : forall m k a m2, is_group m -> garbage m k a -> is_group m2 -> gcell m2 a -> False;
  ge_garb_app : forall m k a, is_group m -> garbage m k a -> appb a -> False;
  ge_garb_area : forall m k a, is_group m -> garbage m k a -> areab a -> False;
  (* [comment removed for export] *)
  ge_span : forall m, is_group m ->
      match s_kind st m with
      | GTop => gspan m <= gmem m + 4096 * gml m
      | GNest hm j hoff => gss hm j + 16 * hoff = gmem m /\ gspan m - 1 <= gse hm j
      end
}.

Record wf_live : Prop := WFLV {
  wL_in : forall p n, In (p, n) L -> exists m i off res, is_group m /\ 0 <= i <= glast m /\ gslot m i = SUser p n off res;
  wL_nodup : NoDup L;
  wL_fun : forall m1 i1 m2 i2 p n1 n2 o1 o2 r1 r2,
      is_group m1 -> is_group m2 -> 0 <= i1 <= glast m1 -> 0 <= i2 <= glast m2 ->
      gslot m1 i1 = SUser p n1 o1 r1 -> gslot m2 i2 = SUser p n2 o2 r2 -> m1 = m2 /\ i1 = i2;
  wL_len : Z.of_nat (length L) <= LMAX
}.

Record wf_regions : Prop := WFR {
  wr_rng : forall r, In r regions ->
      HEAPLO <= rg_base r /\ rg_base r + rg_len r <= CEIL /\ rg_base r mod 4096 = 0 /\ 0 < rg_len r /\ rg_len r mod 4096 = 0;
  wr_disj : forall r1 r2, In r1 regions -> In r2 regions -> r1 <> r2 ->
      rg_base r1 + rg_len r1 <= rg_base r2 \/ rg_base r2 + rg_len r2 <= rg_base r1;
  wr_nodup : NoDup regions;
  wr_len : forall r, In r regions -> rg_len r <= 2 ^ 35;     (* [comment removed for export] *)
  wr_grp_bound : forall b len m, In (RG b len (RGroup m)) regions -> gsc m < 48 -> len <= GRPMAX;
  wr_grp63 : forall b len m, In (RG b len (RGroup m)) regions -> gsc m = 63 ->
      (exists p n off res, gslot m 0 = SUser p n off res /\ len <= n + 4116) \/ (exists off, gslot m 0 = SJunk off);
  wr_meta : forall b len e, In (RG b len (RMeta e)) regions -> 0 <= e /\ 4096 * (1 + e) <= len /\ len <= 2 ^ 24;
  (* [comment removed for export] *)
  wr_meta_cnt : Z.of_nat (length (List.filter (fun r => match rg_kind r with RMeta _ => true | _ => false end) regions)) <= c_shift cx;
  wr_brk : match s_brk st with
           | BrkUntried => forall b len, ~ In (RG b len RBrk) regions
           | BrkLive b0 b gk => (forall b' len, In (RG b' len RBrk) regions -> b0 <= b' /\ b' + len <= b) /\
                             Z.of_nat (length (List.filter (fun r => match rg_kind r with RBrk => true | _ => false end) regions)) <= Z.of_nat (length areas) /\
                             In (first_brk_region b0 gk) regions   (* [comment removed for export] *)
           | BrkDead g => Z.of_nat (length (List.filter (fun r => match rg_kind r with RBrk => true | _ => false end) regions)) <= Z.of_nat (length areas) /\
                          match g with Some (b0, gk) => In (first_brk_region b0 gk) regions | None => True end
           end;
  (* [comment removed for export] *)
  wr_brklen : forall b len, In (RG b len RBrk) regions -> len <= 8192
  (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Record wf_img : Prop := WFI {
  wi_areas : forall a, In a areas -> img_free a (a + 4096);
  wi_regions : forall r, In r regions -> img_free (rg_base r) (rg_base r + rg_len r)
}.

Definition WF : Prop := wf_ctx /\ wf_areas /\ wf_lists /\ wf_groups /\ wf_geom /\ wf_live /\ wf_regions /\ wf_img.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Rep.
Variable M : mem.

Record rep_statics : Prop := RST {
  rc_needlocks : cell M A_NEED_LOCKS 1 0;
  rc_pagesize : cell M A_PAGESIZE 8 4096;
  rc_lock : cell M MLOCK 4 0;
  rc_canary : cell M A_CANARY 8 (s_canary st);
  rc_got : cell M A_GOT_CANARY 8 A_CANARY;
  rc_errno : cell M A_ERRNO 4 (s_errno st);
  rc_tab_ctz : img_clear M A_TAB_CTZ (A_TAB_CTZ + 32);
  rc_tab_sc : img_clear M A_TAB_SC (A_TAB_MED + 4)
}.

Record rep_ctx : Prop := RCX {
  rc_secret : cell M ctx_secret 8 (c_secret cx);
  rc_init : cell M ctx_init_done 4 1;
  rc_ctr : cell M ctx_mmap_counter 4 (c_mmap_ctr cx);
  rc_fmh : cell M ctx_free_meta_head 8 (c_free_head cx);
  rc_am : cell M ctx_avail_meta 8 (c_avail_meta cx);
  rc_amc : cell M ctx_avail_meta_count 8 (c_avail_cnt cx);
  rc_amac : cell M ctx_avail_meta_area_count 8 (c_area_cnt cx);
  rc_mas : cell M ctx_meta_alloc_shift 8 (c_shift cx);
  rc_mah : cell M ctx_meta_area_head 8 (c_area_head cx);
  rc_mat : cell M ctx_meta_area_tail 8 (c_area_tail cx);
  rc_amas : cell M ctx_avail_meta_areas 8 (c_cursor cx);
  rc_active : forall sc, 0 <= sc < 48 -> cell M (ctx_active sc) 8 (c_active cx sc);
  rc_usage : forall sc, 0 <= sc < 48 -> cell M (ctx_usage sc) 8 (c_usage cx sc);
  rc_useq : forall i, 0 <= i < 32 -> cell M (ctx_unmap_seq i) 1 (c_unmap_seq cx i);
  rc_bnc : forall i, 0 <= i < 32 -> cell M (ctx_bounces i) 1 (c_bounces cx i);
  rc_seq : cell M ctx_seq 1 (c_seq cx);
  rc_brk : cell M ctx_brk 8 (c_brk cx)
  (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Record rep_meta (m : Z) (r : meta_rec) : Prop := RMT {
  rm_prev : cell M m 8 (mr_prev r);
  rm_next : cell M (m + 8) 8 (mr_next r);
  rm_mem : cell M (m + 16) 8 (mr_mem r);
  rm_avail : cell M (m + 24) 4 (mr_avail r);
  rm_freed : cell M (m + 28) 4 (mr_freed r);
  rm_W : cell M (m + 32) 8 (mr_W r)
}.

Record rep_area (a : Z) : Prop := RAR {
  ra_check : cell M a 8 (c_secret cx);
  ra_nslots : cell M (a + 16) 4 NSLOTS;
  ra_def : defined M a (a + 4096);
  ra_metas : forall k, 0 <= k < NSLOTS -> rep_meta (meta_addr a k) (MRc (meta_addr a k))
}.

(* [comment removed for export] *)
Record rep_hdr (m i p : Z) (rc : Z) : Prop := RHD {
  rh_m4 : byte_at M (p - 4) 0;
  rh_m3 : byte_at M (p - 3) (i + 32 * rc);
  rh_m2 : cell M (p - 2) 2 (inband m p)
}.

Definition rep_slot (m i : Z) (s : slot_st) : Prop :=
  match s with
  | SAvail => True
  | SFreed => True
  | SUser p n off res =>
      rep_hdr m i p (res_code res) /\
      (0 < res -> byte_at M (p + n) 0) /\
      (5 <= res -> cell M (gse m i - 4) 4 res /\ byte_at M (gse m i - 5) 0)
  | SHost m' off =>
      exists rc, 0 <= rc < 8 /\ rep_hdr m i (gss m i + 16 * off) rc
  | SJunk off => True   (* [comment removed for export] *)
  end.

Record rep_group (m : Z) : Prop := RGP {
  rg_meta : cell M (gmem m) 8 m;
  rg_aidx : exists b, 0 <= b < 256 /\ byte_at M (gmem m + 8) b /\ b mod 32 = gai m;
  (* [comment removed for export] *)
  rg_hdr0 : forall i, 0 <= i <= gcnt m -> (i < gcnt m \/ endb_own m) -> byte_at M (gss m i - 4) 0;
  rg_def : match s_kind st m with GTop => defined M (gmem m) (gmem m + 4096 * gml m) | GNest _ _ _ => True end;
  rg_slots : forall i, 0 <= i <= glast m -> rep_slot m i (gslot m i)
}.

Record REP : Prop := RP {
  rp_statics : rep_statics;
  rp_ctx : rep_ctx;
  rp_areas : forall a, In a areas -> rep_area a;
  rp_groups : forall m, is_group m -> rep_group m
}.

End Rep.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition region_entry (r : region) : word * word := (Z_to_bv 64 (rg_base r), Z_to_bv 64 (rg_len r)).

Definition noacc_of_region (r : region) : list (word * word) :=
  match rg_kind r with
  | RMeta e => if e =? 0 then [(Z_to_bv 64 (rg_base r), Z_to_bv 64 (rg_len r))]   (* [comment removed for export] *)
               else (Z_to_bv 64 (rg_base r), Z_to_bv 64 4096)
                    :: (if 4096 * (1 + e) <? rg_len r
                        then [(Z_to_bv 64 (rg_base r + 4096 * (1 + e)), Z_to_bv 64 (rg_len r - 4096 * (1 + e)))]
                        else [])
  | _ => []
  end.

Definition noacc_of : list (word * word) :=
  match guard_noacc (s_brk st) with Some b0 => [(Z_to_bv 64 b0, Z_to_bv 64 4096)] | None => [] end
  ++ flat_map noacc_of_region regions.

Record LEDGER (vm : VmMaps) : Prop := LDG {
  lg_maps : Permutation (vm_maps vm) (map region_entry regions);
  lg_noacc : Permutation (vm_noaccess vm) noacc_of;
  lg_brk : match s_brk st with
           | BrkUntried => vm_brk vm = vm_start_brk vm /\ bv_unsigned (vm_start_brk vm) mod 4096 = 0 /\
                           IMG_HI <= bv_unsigned (vm_start_brk vm) /\ bv_unsigned (vm_start_brk vm) + 8192 <= CEIL
           | BrkLive b0 b _ => bv_unsigned (vm_brk vm) = b /\ bv_unsigned (vm_start_brk vm) = b0
           | BrkDead _ => True
           end;
  lg_res : vm_reserved vm = segments_reserved RSEGS;
  lg_top : page_floor (alloc_top vm) = CEIL       (* [comment removed for export] *)
}.

End WithState.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition nojunk (st : mst) : Prop :=
  forall m k off, is_group st m -> 0 <= k <= g_lastidx st m -> s_slot st m k <> SJunk off.

(* [comment removed for export] *)
Definition nolimbo (st : mst) : Prop := s_limbo st = [].

Definition MInv `{mh_run} (L : list (Z * Z)) (M : mem) (vm : VmMaps) : Prop :=
  exists st, WF st L /\ REP st M /\ LEDGER st vm /\ nojunk st /\ nolimbo st.

(* [comment removed for export] *)
Definition agf (st : mst) : Prop :=
  forall m, is_group st m -> mr_avail (s_meta st m) = 0 /\ mr_freed (s_meta st m) = 0.

Definition MInvF `{mh_run} (L : list (Z * Z)) (M : mem) (vm : VmMaps) : Prop :=
  exists st, WF st L /\ REP st M /\ LEDGER st vm /\ nojunk st /\ nolimbo st /\ agf st.

Lemma MInvF_MInv `{mh_run} : forall L M vm, MInvF L M vm -> MInv L M vm.
Proof. intros L M vm (st & A & B & C & D & E & _). exists st. exact (conj A (conj B (conj C (conj D E)))). Qed.

