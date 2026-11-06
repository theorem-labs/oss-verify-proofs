(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file, written by a Theorem Labs lane: the asan-ubsan (lib/AU) twin of
   lib/A/AD3i.v, for a Theorem Labs lane's knock
   StackDepot first-use chain. rule 24: no function proved (a budget / room lemma that discharges premises of the
   MmapOrDie (S8, lib/A/AD3h.v) and MmapNoReserveOrDie (S4, lib/A/AD3d.v) contracts at StackDepotPut's first use,
   and a counting lemma that keeps the depot in ONE node block and ONE store block). *)
(* Lemma names and statements are lib/A/AD3i.v's. The A-core modules are replaced by their AU twins: A/AWalkFw0 ->
   AU/AWalkFw0 (tfibsegs = AsanUbsan.M.loaded_segments), AF0m -> YF0m, AF0x -> YF0x, AFia -> YFia, AFem -> YFem;
   lib/Reusable is shared. The image facts below are re-measured on the asan-ubsan image
   (internal path): every address cited here holds the same instruction there as in the asan image.

   THE ORDER OF THE TWO MAPS (fuzz_knock.asan-ubsan, unstripped twin sha256 6b6e06f3...87773,
   StackDepotBase<...>::Put 0x70f10):
     0x710cc amoadd.w (n_uniq_ids += 1); 0x710e4 srli a1,s1,0x10 (idx = id >> 16); 0x710f0 ld map1_[idx];
     0x710f4 beqz -> 0x71188, 0x7118c jal TwoLevelMap::Create (NB, MmapOrDie 0x100000), j back to 0x710f8;
     0x71114 jal StackDepotNode::store -> StackStore::Store -> Alloc -> BlockInfo::Create (SB, MmapNoReserveOrDie
     0x800000). So the NB map comes first and the SB map second, and the S4 gate is stated on the post of the S8 map.

   THE ROOM PREMISE (the core's own, cgif form): at the entry of every allocator walk the core holds
     AR tfibsegs B ly S W mem0 md0 (lib/Reusable/YG0n.v:807-808: ARm, ALedger, abudget_ok, amwf, ahs) and
     qmeter S (YG0n.v:876), whose mroom S (YG0n.v:874) is  ameter S + VM_HEAD <= ASAN_VM_LMIN  with VM_HEAD = 2^30
     (YG0n.v:872). mroom_slack (lib/Reusable/YG08.v:182-185) turns this into
       eager_used md + a + (VM_HEAD - 2 * k) <= vm_limit (m_vmmaps md)
     at any later state md of the walk whose eager use and world grew by at most k (the eager-map precedent is
     YFjs.v:482-491 slackS and its use at YFjs.v:573). That is the room Put's call has: depot_gates below spends
     it on the two depot maps, 2 * k + 11 * 2^20 <= 2^30 (k = 0 on the primary and free paths, d3i_k_sec on the
     secondary path, where the walk already mapped the secondary block and its shadow before Put).
     Placement comes from the ledger: al_reserved, al_cover, al_top, al_img (YG0n.v:609, :615-617, :626, :607) give a
     free NOB-spaced candidate below ASAN_CEIL by YF06.v's obstacle count (sec_grant_exists, YF06.v:145-184), here
     extended by the maps the walk added after the ledger state (X) and by the NB grant itself.
     These proofs do not use al_perm (YG0n.v:623) nor perm_maps (YG0n.v:530-538); in the kernel this note was written on, those named (ly_NB,
     kNodesBlockSize) and (ly_SB, kStoreBlockSize) as mapped (cgif maps the depot before main; knock does not):
     that was a ledger-shape question for the porter (S9 measurement, section 5 of
     depot-budget.md (sha256 0de5d6920ca7; internal record)), not a room
     one, and a ledger that drops those two entries keeps every lemma here.

   THE PLACEMENT CONCLUSIONS are stated as the body of md_room (lib/A/AD3d.v, on a Theorem Labs lane's branch,
   in another Theorem Labs lane's text), word for word, so [exact] closes [md_room md n] by delta and
   [proj1 (depot_room ...)] closes AD3h.v's [mod_room Wx md kNodesBlockSize]; this file defines no copy of md_room.
   The base this file was written on had no lib/AU twin of AD3d.v or AD3h.v.

   THE ONE-BLOCK LEMMA: the bound the core already proves is the universe one, not an event count:
   TfibSyms B gives universe_ok (as_universe B) (YF0m.v:254; YG01.v:141-143: at most DEPOT_MAX = 4096
   traces, each of at most kUnwindMax = 30 frames, YG00.v:39), Wf gives the depot NoDup inside it (YG01.v:338), and
   YFem.v:37 depot_len_bound / YFem.v:41 depot_frames_bound bound the depot (the same two give YFem.v:147 TOT_range).
   So s_total (F) <= 32 + 31 * 4096 and F + n + 1 <= 127039 < kStoreFramesPerBlock = 2^20 (YG00.v:38): every Store's
   frames lie in block 0, and Alloc's new-block branch is refuted. Node ids: at most 4096 distinct traces, so the new
   id <= 4097 < 65536 = kDepotIdsPerBlock (YG00.v:37) and idx = id >> 16 = 0. The 32 in the F premise covers both
   numberings of s_total: the donor's cell len(ly_tr0) + 1 + depot_frames S (YG0n.v:110, lo_tr0 YG0f.v:446) and
   knock's empty-at-main store, depot_frames S.
   The 30 is measured on the asan-ubsan image (S9 trace-cap measurement on the asan image,
   (internal path), re-measured on the asan-ubsan image in (internal path)): kStackTraceMax =
   255 (0x3d128 addi a4,zero,0xff, the CHECK malloc_context_size <= kStackTraceMax in __asan::InitializeFlags); the
   UnwindFast loop stops at size >= max_depth (0x7193c bgeu a5,s0); malloc and free pass max_depth = malloc_context_size
   (malloc 0x51664, free 0x51504), which InitializeFlags sets to 30 (0x3c3c0 addi a1,zero,0x1e; 0x3c3c8 sw a1,0x18c(sp))
   before parsing ASAN_OPTIONS; StackStore::Store clamps to 255 (0x6e940-0x6e948). So 30 holds when ASAN_OPTIONS sets
   neither malloc_context_size nor start_deactivated; the core states it as universe_ok (as_universe B). *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK11 YK0v YK00 YK13 YK06 YK04 YA0n.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import AWalkFw0.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YF06.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG0f YG00 YG0a YG01 YG0n YG0s YG0h YG08 YG0j.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import YF0m YF0x YFia.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require YFem.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YG07 YP0n YA09.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ===== Closed arithmetic (no Section variables). ===== *)

(* The slack mroom_slack leaves pays the NB gate (grant n + allow_expose n) and the whole first-use sum. *)
Lemma d3i_gate_arith : forall e a l k,
  e + a + (VM_HEAD - 2 * k) <= l -> 2 * k + 11 * 2 ^ 20 <= 2 ^ 30 ->
  e + a + 2 * kNodesBlockSize <= l /\ e + a + 3 * kNodesBlockSize + kStoreBlockSize <= l.
Proof. intros e a l k H Hk. unfold VM_HEAD, kNodesBlockSize, kStoreBlockSize in *. lia. Qed.

(* After the NB grant and its exposure (eager use and world each grow by at most one NB), the SB gate. *)
Lemma d3i_post_arith : forall e a l e' a',
  e + a + 3 * kNodesBlockSize + kStoreBlockSize <= l -> e' <= e + kNodesBlockSize -> a' <= a + kNodesBlockSize ->
  e' + a' + kStoreBlockSize <= l.
Proof. intros e a l e' a' H1 H2 H3. unfold kNodesBlockSize, kStoreBlockSize in *. lia. Qed.

(* The secondary path: before Put the walk mapped the secondary block (eager use <= ms) and exposed it with its
   shadow hull (world <= ms + (ms / 8 + 8192), YFjs.v:453 SH_hull); that growth still leaves the depot's room. *)
Lemma d3i_k_sec : forall ms, 0 < ms <= MALLOC_MAX + 4 * 4096 -> 2 * (ms + (ms / 8 + 8192)) + 11 * 2 ^ 20 <= 2 ^ 30.
Proof.
intros ms [H0 H1]. unfold MALLOC_MAX in H1.
assert (D : ms / 8 <= 33556480) by (apply Z.div_le_upper_bound; lia).
assert (D0 : 0 <= ms / 8) by (apply Z.div_pos; lia).
lia.
Qed.

(* A frame index below 2^20 is in block 0 (GetBlockIdx = idx >> 20); a node id below 2^16 is in map1_[0]. *)
Lemma d3i_blk0 : forall x, 0 <= x < 2 ^ 20 -> Z.shiftr x 20 = 0.
Proof. intros x Hx. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.

Lemma d3i_idx0 : forall id, 0 <= id < 65536 -> Z.shiftr id 16 = 0.
Proof. intros id Hid. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.

Section d3i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).

(* ===== The budget gates at Put's call (S8 at the call, and the first-use sum for S4). ===== *)
Lemma depot_gates : forall B ly S W mem0 md0 (md : Model) (Wx : world tfibsegs) k,
  AR tfibsegs B ly S W mem0 md0 -> mroom S ->
  vm_limit (m_vmmaps md) = vm_limit (m_vmmaps md0) ->
  eager_used md <= eager_used md0 + k -> A_bytes (w_A Wx) <= A_bytes (w_A W) + k ->
  0 <= k -> 2 * k + 11 * 2 ^ 20 <= 2 ^ 30 ->
  eager_used md + A_bytes (w_A Wx) + 2 * kNodesBlockSize <= vm_limit (m_vmmaps md) /\
  eager_used md + A_bytes (w_A Wx) + 3 * kNodesBlockSize + kStoreBlockSize <= vm_limit (m_vmmaps md).
Proof.
intros B ly S W mem0 md0 md Wx k HAR HM LIM EG AB Hk HK.
pose proof HAR as (M & L & [AB0 _] & _ & _).
pose proof (mroom_slack tfibsegs (as_universe B) ly S md0 md (A_bytes (w_A W)) (A_bytes (w_A Wx)) k
  (am_wf _ _ _ _ M) L AB0 HM LIM EG AB Hk) as SL.
exact (d3i_gate_arith _ _ _ _ SL HK).
Qed.

(* ===== Placement: a grant of any size up to NOB exists at a state whose maps are the ledger state's plus X. ===== *)
Lemma depot_grant_exists : forall ly S md0 md (X : list (word * word)) nZ,
  layout_ok ly -> ALedger tfibsegs ly S md0 ->
  (forall e, In e (vm_maps (m_vmmaps md0)) -> 0 < bv_unsigned (snd e)) ->
  Z.of_nat (length (sec_extents ly S)) <= SEC_LIVE_N ->
  Forall (fun e => 0 <= snd e <= NOB) (sec_extents ly S) ->
  vm_reserved (m_vmmaps md) = vm_reserved (m_vmmaps md0) ->
  alloc_top (m_vmmaps md0) <= alloc_top (m_vmmaps md) ->
  (forall e, In e (vm_maps (m_vmmaps md)) -> In e (vm_maps (m_vmmaps md0)) \/ In e X) ->
  Forall (fun e => 0 < bv_unsigned (snd e) <= NOB) X -> Z.of_nat (length X) <= 1024 ->
  0 < nZ <= NOB ->
  exists a, grant_ok_na_pin md a nZ = true.
Proof.
intros ly S md0 md X nZ LY L NZ SECN SECS ERS ETOP EM XS XN HnZ.
pose proof (YM05.ceil_le_top _ (al_top _ _ _ _ L)) as Htop. pose proof bottomup_floor_val as Hfv.
set (obs := obstacles (lazy_zones ly ++ sec_extents ly S ++ map YG0h.wz X)).
assert (LEN : Z.of_nat (length obs) <= 257 * 25 + SEC_LIVE_N + 1024).
{ pose proof (obstacles_app (lazy_zones ly) (sec_extents ly S ++ map YG0h.wz X)) as O1.
  pose proof (obstacles_app (sec_extents ly S) (map YG0h.wz X)) as O2.
  pose proof (f_equal (@length (Z * Z)) O1) as L1. pose proof (f_equal (@length (Z * Z)) O2) as L2.
  rewrite (length_app (obstacles (lazy_zones ly)) (obstacles (sec_extents ly S ++ map YG0h.wz X))) in L1.
  rewrite (length_app (obstacles (sec_extents ly S)) (obstacles (map YG0h.wz X))) in L2.
  pose proof (obstacles_len (lazy_zones ly) 257 ltac:(lia) (lazy_zones_relevant ly LY)) as A.
  pose proof (lazy_zones_len ly LY) as B.
  pose proof (obstacles_len (sec_extents ly S) 1 ltac:(lia) ltac:(apply Forall_impl with (2 := SECS); intros e He _; lia)) as C.
  assert (XF : Forall (fun z => relevantb z = true -> 0 <= snd z <= 1 * NOB) (map YG0h.wz X)).
  { apply Forall_forall. intros z Hz _. apply in_map_iff in Hz as (e & <- & He).
    pose proof (proj1 (Forall_forall _ _) XS e He) as [X1 X2]. unfold YG0h.wz, YG0h.uw. cbn [snd]. lia. }
  pose proof (obstacles_len (map YG0h.wz X) 1 ltac:(lia) XF) as D. rewrite length_map in D.
  subst obs. clear - L1 L2 A B C D XN SECN. lia. }
destruct (pick_candidateZ NOB nZ obs (seq 0 (Datatypes.S (length obs))) ltac:(lia) (obstacles_size _) (List.seq_NoDup _ _)
  ltac:(rewrite length_seq; lia)) as (j & Hj & Hfree).
apply in_seq in Hj.
set (a := cand NOB j).
assert (Ha : bottomup_floor <= a <= bottomup_floor + (257 * 25 + SEC_LIVE_N + 1024) * (2 * NOB)).
{ subst a. unfold cand. unfold NOB, SEC_LIVE_N in *. split; [nia|]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_r; [lia|]. lia. }
assert (Hce : a + nZ <= ASAN_CEIL) by (ceil; unfold ASAN_CEIL, NOB, SEC_LIVE_N in *; rewrite Hfv in Ha; lia).
exists (Z_to_bv 64 a).
unfold grant_ok_na_pin. rewrite !u64_lit by (ceil; unfold ASAN_CEIL in Hce; lia).
assert (E1 : a mod page_size = 0).
{ subst a. unfold cand. rewrite Hfv. unfold page_size, NOB. rewrite Z.add_mod by lia.
  replace (Z.of_nat j * (2 * 536870912)) with ((Z.of_nat j * 262144) * 4096) by lia. rewrite Z_mod_mult. reflexivity. }
rewrite (proj2 (Z.eqb_eq _ _) E1), (proj2 (Z.ltb_lt 0 _)) by lia.
rewrite (proj2 (Z.leb_le _ _)) by (unfold ASAN_CEIL in Hce; lia).
rewrite YK13.region_free_app.
rewrite ERS, (al_reserved _ _ _ _ L).
replace (Z_to_bv 64 a) with (w64 a) by reflexivity. replace (Z_to_bv 64 nZ) with (w64 nZ) by reflexivity.
assert (IMGb : forall sg, In sg tfibsegs -> 4096 <= Z.of_N (seg_base sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= kImgEnd).
{ intros sg Hsg. pose proof (al_img _ _ _ _ L sg Hsg) as [I1 I2]. pose proof (lo_img ly LY) as (J0 & J1 & J2 & J3).
  rewrite J0 in I1, I2. unfold kImgLo in *. lia. }
rewrite (YG0h.region_free_reserved tfibsegs a nZ IMGb) by (ceil; unfold kImgEnd, ASAN_CEIL in *; lia).
rewrite (YG0h.region_free_intro); [reflexivity|].
intros e He. unfold YG0h.uw, w64. rewrite !u64_lit by (ceil; unfold ASAN_CEIL in *; lia).
destruct (EM e He) as [H0|HX].
- pose proof (al_cover _ _ _ _ L e H0) as AC.
  apply (obstacles_free (lazy_zones ly ++ sec_extents ly S ++ map YG0h.wz X) a nZ); [lia | exact (NZ e H0) | lia | exact Hce | exact Hfree |].
  apply Exists_app in AC as [AC|AC]; apply Exists_app; [left; exact AC | right; apply Exists_app; left; exact AC].
- pose proof (proj1 (Forall_forall _ _) XS e HX) as [X1 X2].
  apply (obstacles_free (lazy_zones ly ++ sec_extents ly S ++ map YG0h.wz X) a nZ); [lia | exact X1 | lia | exact Hce | exact Hfree |].
  apply Exists_app; right; apply Exists_app; right. apply Exists_exists. exists (YG0h.wz e).
  split; [apply in_map; exact HX | unfold YG0h.wz, YG0h.uw; cbn [fst snd]; lia].
Qed.

(* grant_ok_na_pin is md_room's body (lib/A/AD3d.v) with g := bv_unsigned a. *)
Lemma pin_room : forall md (a : word) n, grant_ok_na_pin md a n = true ->
  exists g, g mod 4096 = 0 /\ 0 < g /\ g + n <= alloc_top (m_vmmaps md) /\
    region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) (Z_to_bv 64 g) (Z_to_bv 64 n) = true.
Proof.
intros md a n Hg. unfold grant_ok_na_pin in Hg.
apply andb_prop in Hg as [Hg Hrf]. apply andb_prop in Hg as [Hg Htop]. apply andb_prop in Hg as [Hal Hpos].
apply Z.eqb_eq in Hal. apply Z.ltb_lt in Hpos. apply Z.leb_le in Htop. unfold page_size in Hal.
exists (bv_unsigned a). rewrite Z_to_bv_bv_unsigned. repeat split; assumption.
Qed.

(* The shape of S8's post model (lib/A/AD3h.v mod_contract: md' = with_vm_backing (m_vm_lazy md) mat (mmap_model x n md)),
   which is what depot_room's S4 part asks of md'. *)
Lemma d3i_mmap_shape : forall lz mat (a n : word) md,
  vm_limit (m_vmmaps (with_vm_backing lz mat (mmap_model a n md))) = vm_limit (m_vmmaps md) /\
  vm_reserved (m_vmmaps (with_vm_backing lz mat (mmap_model a n md))) = vm_reserved (m_vmmaps md) /\
  alloc_top (m_vmmaps (with_vm_backing lz mat (mmap_model a n md))) = alloc_top (m_vmmaps md) /\
  vm_maps (m_vmmaps (with_vm_backing lz mat (mmap_model a n md))) = (a, n) :: vm_maps (m_vmmaps md).
Proof. intros lz mat a n md. rewrite !m_vmmaps_wvb. unfold mmap_model. repeat split; reflexivity. Qed.

(* ===== THE ROOM LEMMA: at Put's call, from the walk's room premise.
   md0 / W: the ledger state and world of the walk's AR premise; md / Wx: the model and world at Put's call, which
   differ from md0 / W only by maps the walk added (X) and by at most k of eager use and of world.
   Conclusions, in the consumers' words:
   (1) lib/A/AD3h.v's mod_room Wx md kNodesBlockSize (md_room body + the 2n gate): the S8 / S7 map never refuses;
   (2) the first-use sum eager + A + 3 * NB + SB <= vm_limit;
   (3) for the post of the NB grant (md' maps = md maps + (xw, nw) with nw = NB, eager use and world grown by at most
       NB): md_room md' kStoreBlockSize and the S4 / S3 gate eager + A + SB <= vm_limit: the SB map never refuses. *)
Theorem depot_room : forall B ly S W mem0 md0 (md : Model) (Wx : world tfibsegs) (X : list (word * word)) k,
  AR tfibsegs B ly S W mem0 md0 -> mroom S ->
  vm_limit (m_vmmaps md) = vm_limit (m_vmmaps md0) ->
  vm_reserved (m_vmmaps md) = vm_reserved (m_vmmaps md0) ->
  alloc_top (m_vmmaps md0) <= alloc_top (m_vmmaps md) ->
  (forall e, In e (vm_maps (m_vmmaps md)) -> In e (vm_maps (m_vmmaps md0)) \/ In e X) ->
  Forall (fun e => 0 < bv_unsigned (snd e) <= NOB) X -> Z.of_nat (length X) <= 1023 ->
  eager_used md <= eager_used md0 + k -> A_bytes (w_A Wx) <= A_bytes (w_A W) + k ->
  0 <= k -> 2 * k + 11 * 2 ^ 20 <= 2 ^ 30 ->
  ((exists g, g mod 4096 = 0 /\ 0 < g /\ g + kNodesBlockSize <= alloc_top (m_vmmaps md) /\
      region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) (Z_to_bv 64 g) (Z_to_bv 64 kNodesBlockSize) = true) /\
   eager_used md + A_bytes (w_A Wx) + 2 * kNodesBlockSize <= vm_limit (m_vmmaps md)) /\
  eager_used md + A_bytes (w_A Wx) + 3 * kNodesBlockSize + kStoreBlockSize <= vm_limit (m_vmmaps md) /\
  (forall (xw nw : word) (md' : Model) (Wx' : world tfibsegs),
    bv_unsigned nw = kNodesBlockSize ->
    vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md) ->
    vm_reserved (m_vmmaps md') = vm_reserved (m_vmmaps md) ->
    alloc_top (m_vmmaps md) <= alloc_top (m_vmmaps md') ->
    (forall e, In e (vm_maps (m_vmmaps md')) -> e = (xw, nw) \/ In e (vm_maps (m_vmmaps md))) ->
    eager_used md' <= eager_used md + kNodesBlockSize -> A_bytes (w_A Wx') <= A_bytes (w_A Wx) + kNodesBlockSize ->
    (exists g, g mod 4096 = 0 /\ 0 < g /\ g + kStoreBlockSize <= alloc_top (m_vmmaps md') /\
      region_free (vm_reserved (m_vmmaps md') ++ vm_maps (m_vmmaps md')) (Z_to_bv 64 g) (Z_to_bv 64 kStoreBlockSize) = true) /\
    eager_used md' + A_bytes (w_A Wx') + kStoreBlockSize <= vm_limit (m_vmmaps md')).
Proof.
intros B ly S W mem0 md0 md Wx X k HAR HM LIM ERS ETOP EM XS XN EG AB Hk HK.
pose proof HAR as (M & L & _ & [_ NZ] & _).
pose proof (depot_gates B ly S W mem0 md0 md Wx k HAR HM LIM EG AB Hk HK) as [G8 G84].
assert (PL : forall md' (X' : list (word * word)) nZ,
  vm_reserved (m_vmmaps md') = vm_reserved (m_vmmaps md0) -> alloc_top (m_vmmaps md0) <= alloc_top (m_vmmaps md') ->
  (forall e, In e (vm_maps (m_vmmaps md')) -> In e (vm_maps (m_vmmaps md0)) \/ In e X') ->
  Forall (fun e => 0 < bv_unsigned (snd e) <= NOB) X' -> Z.of_nat (length X') <= 1024 -> 0 < nZ <= NOB ->
  exists a, grant_ok_na_pin md' a nZ = true).
{ intros md' X' nZ E1 E2 E3 E4 E5 E6.
  exact (depot_grant_exists ly S md0 md' X' nZ (am_layout _ _ _ _ M) L NZ
    (YFia.sec_extents_count _ _ _ _ M) (YFia.sec_extents_sizes _ _ _ _ M) E1 E2 E3 E4 E5 E6). }
split; [split; [|exact G8] | split; [exact G84 |]].
- destruct (PL md X kNodesBlockSize ERS ETOP EM XS ltac:(lia) ltac:(unfold kNodesBlockSize, NOB; lia)) as [a Ha].
  exact (pin_room _ _ _ Ha).
- intros xw nw md' Wx' Hnw LIM' ERS' ETOP' EM' EG' AB'.
  split.
  + assert (EM2 : forall e, In e (vm_maps (m_vmmaps md')) -> In e (vm_maps (m_vmmaps md0)) \/ In e ((xw, nw) :: X)).
    { intros e He. destruct (EM' e He) as [->|He']; [right; left; reflexivity|].
      destruct (EM e He') as [H0|H1]; [left; exact H0 | right; right; exact H1]. }
    assert (XS2 : Forall (fun e => 0 < bv_unsigned (snd e) <= NOB) ((xw, nw) :: X)).
    { apply Forall_cons; [simpl; rewrite Hnw; unfold kNodesBlockSize, NOB; lia | exact XS]. }
    assert (ERS2 : vm_reserved (m_vmmaps md') = vm_reserved (m_vmmaps md0)) by (rewrite ERS'; exact ERS).
    assert (XN2 : Z.of_nat (length ((xw, nw) :: X)) <= 1024) by (cbn [length]; lia).
    destruct (PL md' ((xw, nw) :: X) kStoreBlockSize ERS2 ltac:(lia) EM2 XS2 XN2 ltac:(unfold kStoreBlockSize, NOB; lia)) as [a Ha].
    exact (pin_room _ _ _ Ha).
  + rewrite LIM'. exact (d3i_post_arith _ _ _ _ _ G84 EG' AB').
Qed.

(* ===== THE ONE-BLOCK LEMMA, at Put's call of Store / Alloc / TwoLevelMap::Create, from premises every walk has
   (TfibSyms B, Wf (as_universe B) S, and Put's own In tr (as_universe B), tfib_depot_spec YFl0.v:66-75).
   F = s_total before the call, n = the trace's frames (Store), cnt = n + 1 (Alloc's count). ===== *)
Theorem depot_store_one_block : forall B S (tr : list Z) (F : Z),
  TfibSyms B -> Wf (as_universe B) S -> In tr (as_universe B) -> F <= 32 + depot_frames S ->
  let n := Z.of_nat (length tr) in
  F + n + 1 <= 2 ^ 20.
Proof.
intros B S tr F HB WF Htr HF n.
pose proof (ts_universe B HB) as HU.
pose proof (wf_depot _ _ _ _ _ WF) as [Hnd Hincl].
pose proof (YFem.depot_len_bound _ _ HU Hnd Hincl) as Lb.
pose proof (YFem.depot_frames_bound _ _ HU Hincl) as Fb.
assert (Hn : (length tr <= kUnwindMax)%nat) by (destruct HU as (_ & HF' & _); exact (proj1 (Forall_forall _ _) HF' tr Htr)).
unfold depot_frames in HF. unfold DEPOT_MAX in Lb. unfold kUnwindMax in Hn. subst n.
clear - HF Lb Fb Hn. lia.
Qed.

Theorem depot_alloc_one_block : forall B S (tr : list Z) (F cnt : Z),
  TfibSyms B -> Wf (as_universe B) S -> In tr (as_universe B) -> F <= 32 + depot_frames S ->
  cnt = Z.of_nat (length tr) + 1 ->
  F + cnt <= 2 ^ 20.
Proof.
intros B S tr F cnt HB WF Htr HF ->.
pose proof (depot_store_one_block B S tr F HB WF Htr HF) as X. cbv zeta in X. lia.
Qed.

(* The new node id (n_uniq_ids + 1) of an inserting Put (aok's z = 1 arm, YG00.v:601: the trace is not yet in the
   depot) is at most 4097, in either numbering (the donor's n_uniq_ids = depot_ids S, knock's = len (st_depot S)). *)
Theorem depot_node_one_block : forall B S (tr : list Z) (id : Z),
  TfibSyms B -> Wf (as_universe B) S -> In tr (as_universe B) -> mem_trace tr (st_depot S) = false ->
  id <= depot_ids S + 1 ->
  id <= 4097 < 65536.
Proof.
intros B S tr id HB WF Htr Hm Hid.
pose proof (ts_universe B HB) as HU.
pose proof (wf_depot _ _ _ _ _ WF) as [Hnd Hincl].
assert (Hnd' : List.NoDup (tr :: st_depot S)) by (apply List.NoDup_cons; [exact (YG07.mem_trace_false _ _ Hm) | exact Hnd]).
assert (Hincl' : incl (tr :: st_depot S) (as_universe B)) by (intros x [<-|Hx]; [exact Htr | exact (Hincl x Hx)]).
pose proof (YFem.depot_len_bound _ _ HU Hnd' Hincl') as Lb. cbn [length] in Lb.
unfold depot_ids in Hid. unfold DEPOT_MAX in Lb. lia.
Qed.

(* Every id already in the depot (and knock's new id len (st_depot S) + 1 = depot_ids S) is at most 4097 too. *)
Theorem depot_node_id_le : forall B S (id : Z),
  TfibSyms B -> Wf (as_universe B) S -> id <= depot_ids S ->
  id <= 4097 < 65536.
Proof.
intros B S id HB WF Hid.
pose proof (wf_depot _ _ _ _ _ WF) as [Hnd Hincl].
pose proof (YFem.depot_len_bound _ _ (ts_universe B HB) Hnd Hincl) as Lb.
unfold depot_ids in Hid. unfold DEPOT_MAX in Lb. lia.
Qed.

(* ===== The LPS budget mark (Run.v alloc_budget_refused_b, the grant clause of budget_refused_at) at the two
   first-use ecalls, in the register form of anon_node (YF05.v:150-162): the run is NOT budget-refused there.
   This core cannot take the mark from the statement's [~ run_scfg_budget_refused] premise: its obligation
   (KnockAsanTop.v:77-92 ASAN_T) is srealizes at target_alloc_limit with no budget premise, srealizes
   (YK18.v:20-34) has no cut, and the agreement statements bound only the plain run. So the mark is shown from the
   model: the NB map (flags 0x22) from MInv and the walk's gate (depot_room (1)); the SB map (flags 0x4022) is
   MAP_NORESERVE, which the mark never sets (Mmap.v mmap_noreserve_backed_ok). Twins of lib/A/AD3i.v's two lemmas
   (a Theorem Labs lane): same names and statements; they hold for any segment list and cite no image address. ===== *)
Lemma depot_nb_not_budget_refused : forall segs regs pc mem rom md (A : list (Z * Z)),
  getr regs 17 = Z_to_bv 64 222 -> getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 kNodesBlockSize ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = Z_to_bv 64 34 -> getr regs 14 = Z_to_bv 64 (-1) ->
  getr regs 15 = Z_to_bv 64 0 ->
  MInv A md -> A_wf A -> eager_used md + A_bytes A + kNodesBlockSize <= vm_limit (m_vmmaps md) ->
  alloc_budget_refused_b (sys_input segs (YP0n.pend_at regs pc mem rom) (getr regs 17)) md = false.
Proof.
intros segs regs pc mem rom md A H17 H10 H11 H12 H13 H14 H15 HM HA HB.
assert (Hb : Mmap.mmap_noreserve_backed_ok (Z_to_bv 64 34) md kNodesBlockSize = true).
{ unfold Mmap.mmap_noreserve_backed_ok. replace (Mmap.mmap_noreserve_b (Z_to_bv 64 34)) with false by (vm_compute; reflexivity).
  cbv beta iota. apply Z.leb_le. pose proof (YA09.vm_backing_used_le A md HM HA). lia. }
assert (Hru : page_round_up_Z (bv_unsigned (Z_to_bv 64 kNodesBlockSize)) = kNodesBlockSize) by (vm_compute; reflexivity).
unfold alloc_budget_refused_b. cbv zeta.
rewrite YP0n.si_sysno, YP0n.si_arg0, YP0n.si_arg1, YP0n.si_arg2, YP0n.si_arg3, YP0n.si_arg4, YP0n.si_arg5.
rewrite H17, H10, H11, H12, H13, H14, H15.
unfold Mmap.mmap_budget_refused_b. cbv zeta. rewrite Hru, Hb. reflexivity.
Qed.

Lemma depot_sb_not_budget_refused : forall segs regs pc mem rom md,
  getr regs 17 = Z_to_bv 64 222 -> getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 kStoreBlockSize ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = Z_to_bv 64 16418 -> getr regs 14 = Z_to_bv 64 (-1) ->
  getr regs 15 = Z_to_bv 64 0 ->
  alloc_budget_refused_b (sys_input segs (YP0n.pend_at regs pc mem rom) (getr regs 17)) md = false.
Proof.
intros segs regs pc mem rom md H17 H10 H11 H12 H13 H14 H15.
assert (Hb : Mmap.mmap_noreserve_backed_ok (Z_to_bv 64 16418) md kStoreBlockSize = true).
{ unfold Mmap.mmap_noreserve_backed_ok. replace (Mmap.mmap_noreserve_b (Z_to_bv 64 16418)) with true by (vm_compute; reflexivity).
  reflexivity. }
assert (Hru : page_round_up_Z (bv_unsigned (Z_to_bv 64 kStoreBlockSize)) = kStoreBlockSize) by (vm_compute; reflexivity).
unfold alloc_budget_refused_b. cbv zeta.
rewrite YP0n.si_sysno, YP0n.si_arg0, YP0n.si_arg1, YP0n.si_arg2, YP0n.si_arg3, YP0n.si_arg4, YP0n.si_arg5.
rewrite H17, H10, H11, H12, H13, H14, H15.
unfold Mmap.mmap_budget_refused_b. cbv zeta. rewrite Hru, Hb. reflexivity.
Qed.

End d3i.
