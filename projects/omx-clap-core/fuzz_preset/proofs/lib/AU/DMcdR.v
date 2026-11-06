(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/DMcdR.v (commit ce1a656b52b7, file sha256 3692d62389a4) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its image-row names to preset's (ReplyImg_* -> PresetImg_*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 3 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMcdR.v (commit 67fc7ef5787c2195464dbe4d4f7905278328dc0c, CacheDealloc walk (H3 DMcd* + FG*N, a prior worker DMcdGWb / DMcdGW); file sha256 0e41a3a4f172) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 0 code pcs the tool read as sizes, by the internal file funcpair.py), and 3 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMcdR.v at commit 9ee489aa7d7, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (3 numerals; per-numeral report). *)
(* Theorem Labs, 2026-10-30 (lane B1 slice H3 of ReallocPrimary's Theorem Labs walk lanes; brief
   a Theorem Labs lane's internal file B-WALK-LANES.md, interface DMwalkIF.v at 3e29c198d40, frozen): the READ FIELDS of
   the CacheDealloc walk (SizeClassAllocator64LocalCache::Deallocate, 0x34d00) over an OPAQUE cut relation [ARXr].
   rule 24: no function proved here (kind: field statements; the lane's reuse search is the internal file LOOKUP-B1-drain.txt,
   `proof-index MergeBatches Recycle QuarantineCallback_Recycle Drain` 2026-10-29T23:07:48Z exit 0, B1LookupCheck
   CONFIRM).

   [cd_reads] is what the walk reads of the machine through [ARXr] beyond DMwalkIF.v's heads, and what it needs to
   re-establish [ARXr] after the step.  Only the cf instance discharges it (CfF2b: rd_grow / rd_growT / rd_step are its
   obligations; a Theorem Labs lane 00:18Z / 00:20Z).  Every field is stated over the walk's own machine vocabulary (addresses of
   YFgk / YFk5, val_mem / apresent, the walk's frame YFgk.MEQ and its leaf values), never over cgif's AR cells:
   - rd_geo        layout / image cover / tsd at every cut (DMiface.qview has them only at Drain's entry)       [F1]
   - rd_thread     the thread object present (the per-class cache words, the two stat windows of efa_pre)       [F5]
   - rd_rinfo      region info of class c present                                                               [F5]
   - rd_fa         the mapped free array of class c present (the drain copies into it)                          [F5]
   - rd_cache      the per-class cache words equal the model (count, max, size, the cached slots)               [F6]
   - rd_region     the region-info words equal the model (free count, mapped_fa, alloc / mapped user)           [F6]
   - rd_img        the image's constant cells (the whole as_const list; the walk's six constant words follow)     [F2]
   - rd_own        the walk's written windows (cache words, region words, free-array slots) are OWNED (AOX)     (frame)
   - rd_grow       growth arm (KMapFreeArray): the next map slot reserved and unmapped, amwf / ceil_of_top, the
                   byte budget for the grant, the new map's shadow present                                      [F7-F10]
   - rd_growT      ARXr re-established after the grant (world / vm / eager_used change), with its frame        [F11]
   - rd_step       ARXr re-established after the no-growth step, from the walk's own frame + written values     [F12]
   [F3] / [F4] are cd_model's conjuncts (DMwalkIF.v:448-459). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1w YFeq YFew YFeu YFgj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0b.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YFgk YFez YFk5 YFkn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YFfh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require FGcN.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface DIfaceR. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import DMwalkIF.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require AGif2cgif DGif0cgif.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
#[local] Existing Instance AGif2cgif.AImg_cgif.
#[local] Existing Instance DGif0cgif.DImg_cgif.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section r.
Variable B : asyms.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
(* the drain's queue invariant (DMwalkIF's DRq): rd_budget_x reads the pending items' byte bound off it (a Theorem Labs lane 08:29Z) *)
Variable DRq : astate -> list chunk -> list Z -> Prop.
Variable RMAXD : Z.

Local Notation m_of W mem := (mrestrict (w_H W) mem).

(* [F1] the layout facts at every cut. *)
Definition rd_geo : Prop :=
forall inst ly X W mem md, ARXr inst ly X W mem md ->
layout_ok ly /\ img_cover ly /\ ly_tsd ly = TFIB_TSD.

(* [F5] presence of the thread object, of class c's region info and of its mapped free array. *)
Definition rd_thread : Prop :=
forall inst ly X W mem md, ARXr inst ly X W mem md ->
forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> apresent (w_H W) mem a.
Definition rd_rinfo : Prop :=
forall inst ly X W mem md c, ARXr inst ly X W mem md -> 1 <= c <= 30 ->
forall a, YFgk.RGv ly c <= a < YFgk.RGv ly c + 128 -> apresent (w_H W) mem a.
Definition rd_fa : Prop :=
forall inst ly X W mem md c, ARXr inst ly X W mem md -> 1 <= c <= 30 ->
forall a, YFgk.FAv ly c <= a < YFgk.FAv ly c + rg_mapped_fa (reg X c) -> apresent (w_H W) mem a.

(* [F6] the per-class cache words and the region-info words equal the model (YFfi.cache_vals / slot_vals /
   region_vals, YFfi.v:159-196, at cgif from its cells). *)
Definition rd_cache : Prop :=
forall inst ly X W mem md c, ARXr inst ly X W mem md -> 1 <= c <= 30 -> st_cache_inited X = true ->
val_mem tfibsegs (m_of W mem) (YFgk.PCv ly c) 4 (Z.of_nat (length (pc_chunks (cache X c)))) /\
val_mem tfibsegs (m_of W mem) (YFgk.PCv ly c + 4) 4 (YFgk.MAXv c) /\
val_mem tfibsegs (m_of W mem) (YFgk.PCv ly c + 8) 8 (YFgk.SZv c) /\
(forall (i : nat) v, nth_error (pc_chunks (cache X c)) i = Some v ->
 val_mem tfibsegs (m_of W mem) (YFgk.PCv ly c + 16 + 4 * Z.of_nat i) 4 (v / 16)).
Definition rd_region : Prop :=
forall inst ly X W mem md c, ARXr inst ly X W mem md -> 1 <= c <= 30 ->
let RG := YFgk.RGv ly c in
val_mem tfibsegs (m_of W mem) RG 8 0 /\ val_mem tfibsegs (m_of W mem) (RG + 8) 8 0 /\
val_mem tfibsegs (m_of W mem) (RG + 16) 8 (fa_len (rg_free (reg X c))) /\
val_mem tfibsegs (m_of W mem) (RG + 24) 8 (rg_mapped_fa (reg X c)) /\
val_mem tfibsegs (m_of W mem) (RG + 32) 8 (rg_alloc_user (reg X c)) /\ val_mem tfibsegs (m_of W mem) (RG + 40) 8 0 /\
val_mem tfibsegs (m_of W mem) (RG + 48) 8 (rg_mapped_user (reg X c)) /\
val_mem tfibsegs (m_of W mem) (RG + 56) 8 0.

(* [F2] the image's constant cells at every cut, as the AM relation's am_const (YF0x.v:163).  The no-growth walk's
   six constant words (space base, region-info base, the mask, ...; YFfi.const_vals) are cells of this list
   (DMcdF.const_vals), and EnsureFreeArraySpace's seed reads about 25 of them (FGkN.v:203-253) through
   FGtN.efa_pre_lk.  Stated for the head's symbol record B (cd_pre_cx's), so [cd_reads] takes B; at cf it is the
   projection amr_const of ARmcfR (YGcfInstDrainR.v:61; a Theorem Labs lane 04:21Z). *)
Definition rd_img : Prop :=
forall inst ly X W mem md, ARXr inst ly X W mem md ->
Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (as_const B ly).

(* the walk's allocator object is the symbols' (cd_pre_cx states it; MnRecycle.cd_pre_x, cdealloc_m_t's premise, does
   not, a Theorem Labs lane 06:32Z): at cf ARXr_cf's first conjunct IOK inst (YGcfInstDrainR.v:280-281) with IOK_ok
   (YGcfInstBase.v:173). *)
Definition rd_inst : Prop :=
forall inst ly X W mem md, ARXr inst ly X W mem md -> inst = as_inst B.

(* the growth arm's byte budget at the BATCH class's call (cdealloc_m_t's premise DMiface.cd_pre_x does not state
   it; cd_pre_cx does, DMwalkIF.v:451-452): a Theorem Labs lane 07:33Z, a field; at cf from room_rec_cf via room_wA_parts_cf. *)
Definition rd_budget_x : Prop :=
forall inst ly X z W regs mem md, cd_pre_x B ARXr inst ly X z W regs mem md ->
(* the pending items' byte bound is only in DRq_cf at cf (CfF2bRChunk, a Theorem Labs lane 08:29Z) *)
forall its zs, DRq X its zs ->
rg_mapped_fa (reg X kBatchClass) < 4 * (fa_len (rg_free (reg X kBatchClass)) + max_cached kBatchClass / 2) ->
eager_used md + A_bytes (w_A W) + 2 * kUserMapSize + 32768 <= vm_limit (m_vmmaps md).

(* (frame) the windows the walk writes, other than its stack scratch, are owned (at cgif YFez.D_owned, YFez.v:812). *)
Definition rd_own : Prop :=
forall inst ly X W mem md c off, ARXr inst ly X W mem md -> cd_model RMAXD X c off ->
let cnt := Z.of_nat (length (pc_chunks (cache X c))) in
forall a, YFgk.WINF ly c cnt a \/ YFgk.WINR ly c cnt (fa_len (rg_free (reg X c))) a -> AOX ly X a.

(* (model) the per-class lists cover classes 1 .. 31 (cgif: Wf's wf_len_cache / wf_len_regions), so set_pc / set_region
   update class c (cache_dealloc's model step, YFfh.cache_dealloc_eq_full). *)
Definition rd_len : Prop :=
forall inst ly X W mem md, ARXr inst ly X W mem md ->
(32 <= length (st_cache X))%nat /\ (32 <= length (st_regions X))%nat.

(* (frame) every class's allocated user part stays inside its mapped part, inside its 2^32 region below the free array
   (cgif: YG0m.mapped_user_bound), mapped in whole kUserMapSize maps and allocated in 16-byte units: the user bytes are
   apart from every window the walk writes (cdealloc_g_t's puser frame), and EnsureFreeArraySpace's region premise holds. *)
Definition rd_user : Prop :=
forall inst ly X W mem md c', ARXr inst ly X W mem md -> 1 <= c' <= 31 ->
0 <= rg_alloc_user (reg X c') <= rg_mapped_user (reg X c') /\ rg_mapped_user (reg X c') <= kFreeArrayOffset /\
rg_mapped_user (reg X c') mod kUserMapSize = 0 /\ rg_alloc_user (reg X c') mod 16 = 0.

(* [F7-F10] the growth arm's premises of FGt.efa_pre (FGt.v:72-78), at a cut whose class c still has room for one
   more free-array map: the next map slot is reserved and not mapped, the model is well formed with the allocator top
   under the run ceiling, the byte budget pays the grant (the map and its shadow; bytes, not events), and the new
   map's shadow is present. *)
Definition rd_grow : Prop :=
forall inst ly X W mem md c, ARXr inst ly X W mem md -> 1 <= c <= 30 ->
let mf := rg_mapped_fa (reg X c) in
let fadr := YFk5.FAv ly c + mf in
mf + kFreeArrayMapSize <= kFreeArrayMax ->
(* the grant's byte budget is the CALL's fact (cd_pre_cx's last conjunct, DMwalkIF.v:451-452; at cf fm port's
   room_rec_cf), not derivable from ARXr alone (CfF2b, a Theorem Labs lane 07:22Z): a premise here *)
eager_used md + A_bytes (w_A W) + 2 * kUserMapSize + 32768 <= vm_limit (m_vmmaps md) ->
region_free (vm_reserved (m_vmmaps md)) (w64 fadr) (w64 kUserMapSize) = true /\
map_contains (vm_maps (m_vmmaps md)) (w64 fadr) (w64 kUserMapSize) = true /\
amwf md /\ YM05.ceil_of_top (alloc_top (m_vmmaps md)) /\
(forall a, YFkn.SHR (YFk5.SHBv + fadr / 8) a -> mem (w64 a) <> None).

(* [F11] ARXr after CacheDealloc's GROWTH arm, in two steps around an INTERMEDIATE memory mem1 (CfF2b 03:57Z / 04:00Z):
   mem1 is the entry memory with EnsureFreeArraySpace's grant applied (its scratch: the stack below the entry sp, the
   region record's mapped_free_array word and its non-cell junk bytes, the two thread stats windows; the new map, zero;
   its shadow, 0xfa).  The class's exhausted byte RG + 68 (cf_exh_off) is NOT in it: no step of the grant writes it
   (EnsureFreeArraySpace 0x35560-0x35660 stores only its frame, the stats words and RG + 24; a Theorem Labs lane 10:46Z), so mem1
   keeps the entry's byte there.  mem' (CacheDealloc's return) differs from mem1 only in the full-cache window WINT (the no-growth
   step's window, CfF2b's cdwin), with the tail's written values.  The grant is EnsureFreeArraySpace's leaf
   (FGcN.efa_leaf's second disjunct).  Conclusion: ARXr at S'' (the drain into the grown region, then the push), ownership
   does not grow, and every non-stack byte of WING1 (the record's mapped_free_array word and junk bytes, the two thread
   stat windows, the new map, its shadow) is owned at the entry, as cdealloc_g_t's post asks of a byte that changes
   (CfF2b 05:15Z: own_rinfo_cf / own_core_cf / own_fa_cf / own_shadow_prim_cf).  mem1 is constructed in the composition
   (no machine state equals it: at EnsureFreeArraySpace's return the lock is held and the count already drained). *)
Definition rd_growT : Prop :=
forall inst ly X W regs mem md c off W3 mem1 mem' matN mat',
ARXr inst ly X W mem md -> cd_model RMAXD X c off ->
let sp0 := bv_unsigned (getr regs 2) in
let cnt := Z.of_nat (length (pc_chunks (cache X c))) in
let old := fa_len (rg_free (reg X c)) in
let mf := rg_mapped_fa (reg X c) in
let N := YFgk.Nv c in
let RG := YFgk.RGv ly c in
let fadr := YFk5.FAv ly c + mf in
let shf := YFk5.SHBv + fadr / 8 in
let md2 := grant_md false YFkn.FL50 (w64 fadr) (w64 kUserMapSize) (with_vm_backing (m_vm_lazy md) matN md) in
let S'' := YFfh.XK_push c off (YFfh.XK_drain c (YG06.upd_reg c (FGcN.rgG (reg X c)) X)) in
let WING1 := fun a =>
  (sp0 - 240 - RSTACK <= a < sp0) \/ (RG + 24 <= a < RG + 32) \/ (RG + 64 <= a < RG + 68) \/ (RG + 69 <= a < RG + 128) \/
  (ly_T ly + 2768 <= a < ly_T ly + 2800) \/ (ly_T ly + 2872 <= a < ly_T ly + 2888) \/ YFkn.RANGE fadr a \/ YFkn.SHR shf a in
let WINT := fun a =>
  (sp0 - 320 <= a < sp0) \/ (YFgk.PCv ly c <= a < YFgk.PCv ly c + 4) \/ (YFgk.SLOTv ly c cnt <= a < YFgk.SLOTv ly c cnt + 4) \/
  (ly_T ly + t_cache + 2576 <= a < ly_T ly + t_cache + 2584) \/
  (RG <= a < RG + 8) \/ (RG + 16 <= a < RG + 24) \/ (RG + 80 <= a < RG + 88) \/
  (YFgk.DSTv ly c old <= a < YFgk.DSTv ly c old + 4 * N) in
(* the walk's stack is the cut's stack: without it WING1's / WINT's stack part is free (reviewer DMcdFGrowthReview) *)
ly_stk_lo ly + KSTACK_CF <= sp0 <= ly_stk_hi ly ->
cnt = YFgk.MAXv c -> mf < 4 * (old + N) ->
(* the grant (FGcN.efa_leaf's second disjunct) *)
wle W W3 -> w_A W3 = (shf, shf + 32768) :: (fadr, fadr + kUserMapSize) :: w_A W -> hsub (w_H W3) (w_H W) ->
(forall a : word, w_H W a = false -> w_H W3 a = false) ->
(forall a : word, ~ YFkn.RANGE fadr (bv_unsigned a) -> ~ YFkn.SHR shf (bv_unsigned a) -> w_H W3 a = w_H W a) ->
A_bytes (w_A W3) = A_bytes (w_A W) + kUserMapSize + 32768 ->
AI tfibsegs (w_H W3) (w_A W3) md2 -> amwf md2 -> same_io md md2 -> eager_used md2 <= eager_used md + kUserMapSize ->
(* the intermediate memory mem1 *)
(forall x : word, ~ WING1 (bv_unsigned x) -> mem1 x = mem x) ->
(forall a, WING1 a -> apresent (w_H W3) mem1 a) ->
(let m1 := mrestrict (w_H W3) mem1 in
 val_mem tfibsegs m1 RG 8 0 /\ val_mem tfibsegs m1 (RG + 16) 8 old /\ val_mem tfibsegs m1 (RG + 24) 8 (mf + kFreeArrayMapSize) /\
 (forall a, YFkn.RANGE fadr a -> mem1 (w64 a) = Some (Z_to_bv 8 0)) /\
 (forall a, YFkn.SHR shf a -> mem1 (w64 a) = Some (Z_to_bv 8 250))) ->
(* the tail: mem1 -> mem' in the full-cache window *)
(forall x : word, ~ WINT (bv_unsigned x) -> mem' x = mem1 x) ->
(forall a, WINT a -> apresent (w_H W3) mem' a) ->
(let m := mrestrict (w_H W3) mem' in
 val_mem tfibsegs m (YFgk.PCv ly c) 4 (YFgk.CNTPv c cnt + 1) /\
 val_mem tfibsegs m (YFgk.SLOTv ly c cnt) 4 (YFgk.RELv c off / 16) /\
 val_mem tfibsegs m RG 8 0 /\ val_mem tfibsegs m (RG + 16) 8 (old + N) /\
 (forall i v, 0 <= i < N -> val_mem tfibsegs (m_of W mem) (YFgk.SRCv ly c cnt + 4 * i) 4 v ->
   val_mem tfibsegs m (YFgk.DSTv ly c old + 4 * i) 4 v)) ->
ARXr inst ly S'' W3 mem' (with_vm_backing (m_vm_lazy md2) mat' md2) /\
(forall a, AOX ly S'' a -> AOX ly X a) /\
(forall a, WING1 a -> ~ (sp0 - 240 - RSTACK <= a < sp0) -> AOX ly X a).

(* [F12] ARXr after the no-growth step (a Theorem Labs lane 00:20Z, WalkB1's wording): the model takes cache_dealloc's state
   YFez.S' X c off, the world and the vm are unchanged, and the memory is the walk's leaf (YFgk.at_RETK, YFgk.v:394-405):
   equal to the entry's outside YFgk.WIN, present on WIN, with the written count / slot words and, when the cache
   was full, the region words and the copied free-array slots.  Ownership after the step is within the entry's. *)
Definition rd_step : Prop :=
forall inst ly X W regs mem md c off mem' mat,
ARXr inst ly X W mem md -> cd_model RMAXD X c off ->
(* the walk's stack is the cut's stack: without it the windows' stack part is free (reviewer DMcdFGrowthReview) *)
ly_stk_lo ly + KSTACK_CF <= bv_unsigned (getr regs 2) <= ly_stk_hi ly ->
let cnt := Z.of_nat (length (pc_chunks (cache X c))) in
let old := fa_len (rg_free (reg X c)) in
let mf := rg_mapped_fa (reg X c) in
4 * (old + (if cnt =? YFgk.MAXv c then YFgk.Nv c else 0)) <= mf ->
YFgk.MEQ ly regs mem c cnt old mem' ->
(forall a, YFgk.WIN ly regs c cnt old a -> apresent (w_H W) mem' a) ->
val_mem tfibsegs (m_of W mem') (YFgk.PCv ly c) 4 (YFgk.CNTPv c cnt + 1) ->
val_mem tfibsegs (m_of W mem') (YFgk.SLOTv ly c cnt) 4 (YFgk.RELv c off / 16) ->
(cnt = YFgk.MAXv c ->
 val_mem tfibsegs (m_of W mem') (YFgk.RGv ly c) 8 0 /\
 val_mem tfibsegs (m_of W mem') (YFgk.RGv ly c + 16) 8 (old + YFgk.Nv c) /\
 val_mem tfibsegs (m_of W mem') (YFgk.RGv ly c + 24) 8 mf /\
 (forall i v, 0 <= i < YFgk.Nv c -> val_mem tfibsegs (m_of W mem) (YFgk.SRCv ly c cnt + 4 * i) 4 v ->
  val_mem tfibsegs (m_of W mem') (YFgk.DSTv ly c old + 4 * i) 4 v)) ->
ARXr inst ly (YFez.S' X c off) W mem' (with_vm_backing (m_vm_lazy md) mat md) /\
(forall a, AOX ly (YFez.S' X c off) a -> AOX ly X a).

Record cd_reads : Prop := CdReads {
  cr_geo : rd_geo; cr_thread : rd_thread; cr_rinfo : rd_rinfo; cr_fa : rd_fa;
  cr_cache : rd_cache; cr_region : rd_region; cr_img : rd_img; cr_inst : rd_inst; cr_own : rd_own;
  cr_len : rd_len; cr_user : rd_user;
  cr_grow : rd_grow; cr_budget_x : rd_budget_x; cr_growT : rd_growT; cr_step : rd_step
}.
End r.
End d.
