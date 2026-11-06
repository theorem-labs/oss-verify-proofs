(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec Require Import STree Malloc KInv MI_Inv LB_Tables.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition zlen {A} (l : list A) : Z := Z.of_nat (length l).
Definition zcount {A} (f : A -> bool) (l : list A) : Z := zlen (List.filter f l).

Section Q.
Variable st : mstate.
Variable BL : list blk.
Let R := MR st.

Definition cls (m : aptr) : Z := m_sizeclass (R m).

Definition stdg (m : aptr) : bool := (cnt_of (R m) =? cmax (cls m)) && (get_stride (R m) =? S_ (cls m)).

Definition groups_l : list (aptr * ghdr) := map_to_list (s_groups st).
Definition regions_l : list (N * region) := map_to_list (s_regions st).

Definition gmetas : list (aptr * aptr) :=
  flat_map (fun bh : aptr * ghdr => match g_meta (snd bh) with Some m => [(m, fst bh)] | None => [] end) groups_l.

Definition slotcls (s : aptr) : option Z :=
  match s_slots st !! s with Some (p, _) => Some (cls p) | None => None end.

Definition nsc (c : Z) : Z :=
  zsum (map (fun mb => if (cls (fst mb) =? c) && negb (stdg (fst mb)) then cnt_of (R (fst mb)) else 0) gmetas).

Definition nstd (c : Z) : Z := zcount (fun mb => (cls (fst mb) =? c) && stdg (fst mb)) gmetas.

Definition hosted (c : Z) : Z :=
  zcount (fun mb => (m_maplen (R (fst mb)) =? 0) && match slotcls (snd mb) with Some c' => c' =? c | None => false end) gmetas.

Definition n63g : Z := zcount (fun mb => cls (fst mb) =? 63) gmetas.

Definition ngroups : Z := zlen gmetas.

Definition isbig (k : blk) : bool := MMAP_THRESHOLD <=? bsize k.
Definition LR (c : Z) : Z := zcount (fun k => negb (isbig k) && (size_to_class (bsize k) =? c)) BL.
Definition LS (c : Z) : Z := zcount (fun k => match slotcls (bslot k) with Some c' => c' =? c | None => false end) BL.
Definition MIS (c : Z) : Z :=
  zcount (fun k => match slotcls (bslot k) with Some c' => (c' =? c) && (size_to_class (bsize k) =? c - 1) | None => false end) BL.
Definition n63 : Z := zcount isbig BL.
Definition R63 : Z := zsum (map (fun k => if isbig k then round_up_pg (bsize k + IB + UNIT) else 0) BL).

Definition ncarved : Z := zlen (map_to_list (s_metas st)).
Definition is_metakind_b (r : region) : bool := match r_kind r with RKGroup => false | _ => true end.
Definition apages : Z :=
  zsum (map (fun kr : N * region => if is_metakind_b (snd kr) then frontier st (fst kr) (snd kr) / PGSZ - 1 else 0) regions_l).
Definition brk_pages : Z :=
  zsum (map (fun kr : N * region => match r_kind (snd kr) with RKBrk => r_len (snd kr) / PGSZ | _ => 0 end) regions_l).
Definition meta_bytes : Z :=
  zsum (map (fun kr : N * region => match r_kind (snd kr) with RKMeta => r_len (snd kr) | _ => 0 end) regions_l).

Definition regbytes : Z := zsum (map (fun kr : N * region => round_up_pg (r_len (snd kr))) regions_l).
Definition group_bytes : Z :=
  zsum (map (fun kr : N * region => match r_kind (snd kr) with RKGroup => round_up_pg (r_len (snd kr)) | _ => 0 end) regions_l).
End Q.

Definition CAP0 (P : Z -> Z) (c : Z) : Z := P c + 14 + (if c <=? 23 then 160 * c else 0).
Definition guests : list Z := [0; 1; 2; 3; 4; 5; 6].
Definition HOSTSTD (P : Z -> Z) (c : Z) : Z :=
  zsum (map (fun c' => if bighost c' =? c then (CAP0 P c' + 32) / cmax c' else 0) guests).
Definition CAP (P : Z -> Z) (c : Z) : Z := CAP0 P c + HOSTSTD P c.

Definition NG (P : Z -> Z) : Z := zsum (map (fun c => (CAP P c + 32) / cmax c + 160) classes) + P 63.
Definition NCAP (P : Z -> Z) : Z := NG P + 4.

Definition PHI (P : Z -> Z) : Z :=
  zsum (map (fun c => if std_nested c then 0 else std_len c * ((CAP P c + 32) / cmax c)) classes)
  + zsum (map (fun c => 160 * (S_ c + 4111)) classes)
  + PGSZ * (5 * NCAP P / 101 + 8)
  + 3 * PGSZ.

Section INVQ.
Variable X : extras.
Variable st : mstate.
Variable BL : list blk.
Let R := MR st.
Let cx := s_ctx st.

Record SINV : Prop := mkSINV {

  qb_cls : forall k, In k BL -> exists m i, s_slots st !! bslot k = Some (m, i)
      /\ (m_sizeclass (R m) < 48 -> bsize k < MMAP_THRESHOLD
            /\ (size_to_class (bsize k) = m_sizeclass (R m) \/ size_to_class (bsize k) = m_sizeclass (R m) - 1))
      /\ (m_sizeclass (R m) = 63 -> MMAP_THRESHOLD <= bsize k /\ m_maplen (R m) * 4096 = round_up_pg (bsize k + IB + UNIT));
  qb_mis : forall c, MIS st BL c <= 13;

  qg_map : forall b m ai, s_groups st !! b = Some (mkGhdr (Some m) ai) -> m_sizeclass (R m) < 48 -> m_maplen (R m) <> 0 ->
      m_maplen (R m) * 4096 <= cnt_of (R m) * S_ (m_sizeclass (R m)) + 4111;
  qg_std : forall b m ai, s_groups st !! b = Some (mkGhdr (Some m) ai) -> stdg st m = true ->
      (m_maplen (R m) = 0 <-> std_nested (m_sizeclass (R m)) = true)
      /\ (m_maplen (R m) = 0 -> exists p i, s_slots st !! b = Some (p, i) /\ m_sizeclass (R p) = bighost (m_sizeclass (R m)))
      /\ (m_maplen (R m) <> 0 -> m_maplen (R m) * 4096 = std_len (m_sizeclass (R m)));
  qg_small : forall c, 0 <= c < 48 -> nsc st c < 160;
  qg_63 : forall b m ai, s_groups st !! b = Some (mkGhdr (Some m) ai) -> m_sizeclass (R m) = 63 ->
      In (slot_start' (R m) 0) (map bslot BL);

  qg_host : forall b m ai p i, s_groups st !! b = Some (mkGhdr (Some m) ai) -> m_maplen (R m) = 0 ->
      s_slots st !! b = Some (p, i) -> m_sizeclass (R p) <= 23;

  qm_leak : forall m mr, s_metas st !! m = Some mr -> m_mem mr = None -> m_next mr <> None \/ In m (x_idle X);
  qm_pages : 101 * apages st <= ncarved st + c_avail_meta_count cx;
  qm_brk : forall rid r, s_regions st !! rid = Some r -> r_kind r = RKBrk -> 101 * (r_len r / PGSZ - 2) <= ncarved st;
  qm_len : forall rid r, s_regions st !! rid = Some r -> r_kind r = RKMeta ->
      exists j, 1 <= j <= c_meta_alloc_shift cx /\ r_len r = 2 ^ j * PGSZ;
  qm_dist : forall rid1 rid2 r1 r2, s_regions st !! rid1 = Some r1 -> s_regions st !! rid2 = Some r2 ->
      r_kind r1 = RKMeta -> r_kind r2 = RKMeta -> rid1 <> rid2 -> r_len r1 <> r_len r2;
  qm_shift : 1 <= c_meta_alloc_shift cx -> 101 * (2 ^ c_meta_alloc_shift cx - 1) <= 2 * ncarved st + 101
}.

Record AQ (P : Z -> Z) : Prop := mkAQ {
  aq_live : forall c, 0 <= c < 48 -> LR BL c <= P c;
  aq_slots : forall c, 0 <= c < 48 -> gcnt st c <= CAP P c + 32;
  aq_big : n63 BL <= P 63;
  aq_carved : ncarved st <= NCAP P;
  aq_P : forall c, 0 <= P c
}.
End INVQ.
