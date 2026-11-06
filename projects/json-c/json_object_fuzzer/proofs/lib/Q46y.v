(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Set Keyed Unification.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKyU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKyU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy7F.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy7F. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qgp5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qgp5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPa2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPa2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhFR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QhFR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9dL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9dL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcxL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcxL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsc9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsc9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt4u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt4u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QX8X.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QX8X. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOb0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOb0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrTb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrTb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QchP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QchP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4l7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4l7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QAPX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QAPX. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QV5O.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV5O. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwca.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwca.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Record AM_frame (st st1 : mstate) : Prop := mkAMF {
amf_groups : s_groups st1 = s_groups st;
amf_slots : s_slots st1 = s_slots st;
amf_shadow : s_shadow st1 = s_shadow st;
amf_tick : s_tick st1 = s_tick st;
amf_active : forall sc, active st1 sc = active st sc;
amf_usage : forall sc, usage st1 sc = usage st sc;
amf_bounces : c_bounces (s_ctx st1) = c_bounces (s_ctx st);
amf_seq : c_seq (s_ctx st1) = c_seq (s_ctx st);
amf_mc : c_mmap_counter (s_ctx st1) = c_mmap_counter (s_ctx st);
amf_regions : forall rid r, s_regions st !! rid = Some r -> r_kind r = RKGroup -> s_regions st1 !! rid = Some r;
amf_next_rid : (s_next_rid st <= s_next_rid st1)%N;
amf_ssec : s_secret st1 = s_secret st
}.

Record L_frame (L L1 : mled) : Prop := mkLF {
lf_groups : ld_groups L1 = ld_groups L;
lf_live : ld_live L1 = ld_live L;
lf_resv : ld_resv L1 = ld_resv L
}.

Section TAKE.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HC : 0 < c_avail_meta_count (s_ctx st).

End TAKE.

Definition adv (st : mstate) (p : aptr) : mstate :=
upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st.

Definition carve_rest (s : mstate) (p : aptr) : mstate :=
let st2 := match c_meta_area_tail (ctx s) with
| Some tl => set_areas (<[tl := match (s_areas s) !! tl with
| Some a => mkArea (a_check a) (Some p) (a_nslots a)
| None => mkArea 0 (Some p) 0 end]> (s_areas s)) s
| None => upd_ctx (set_meta_area_head (Some p)) s
end in
let st3 := upd_ctx (set_meta_area_tail (Some p)) st2 in
let old := default (mkArea 0 None 0) ((s_areas st3) !! p) in
let st4 := set_areas (<[p := mkArea (c_secret (ctx st3)) (a_next old) NSLOTS]> (s_areas st3)) st3 in
upd_ctx (fun c => set_avail_meta (Some (aadd p AREA_HDR)) (set_avail_meta_count NSLOTS c)) st4.

Section CARVE.
Variables (X : extras) (s : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (p : aptr).
Hypothesis INV : INVL X s L BL LS.
Hypothesis HP : c_avail_meta_areas (s_ctx s) = Some (aadd p 4096).
Hypothesis NA : s_areas s !! p = None.
Hypothesis NM : forall k, 0 <= k < NSLOTS -> s_metas s !! mslot p k = None.
Hypothesis PG : PGSZ <= snd p.
Hypothesis PM : snd p mod PGSZ = 0.
Hypothesis INIT : c_init_done (s_ctx s) = 1.
Let s' := carve_rest s p.

Definition cr_areas : gmap aptr area :=
match c_meta_area_tail (ctx s) with
| Some tl => <[p := mkArea (c_secret (ctx s)) None NSLOTS]>
(<[tl := match (s_areas s) !! tl with Some a => mkArea (a_check a) (Some p) (a_nslots a) | None => mkArea 0 (Some p) 0 end]> (s_areas s))
| None => <[p := mkArea (c_secret (ctx s)) None NSLOTS]> (s_areas s)
end.
Definition cr_head : optr := match c_meta_area_tail (ctx s) with Some _ => c_meta_area_head (ctx s) | None => Some p end.

End CARVE.

Section META_ADV.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (rid : N) (off : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hcur : c_avail_meta_areas (s_ctx st) = Some (rid, off).
Hypothesis Hcnt : 0 < c_avail_meta_area_count (s_ctx st).
Let p : aptr := (rid, off).
Let a : Z := conc st p.
Let st' := adv st p.
Let L' := Qgp5.set_metas (map (bump_meta a) (ld_metas L)) L.

End META_ADV.

Section NEW_META.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (r : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hcnt : c_avail_meta_area_count (s_ctx st) = 0.
Let n : Z := Z.shiftl 2 (c_meta_alloc_shift (s_ctx st)).
Let len : Z := n * PGSZ.
Hypothesis HOK : mmap_answer_ok (live_ranges st) len r = true.
Hypothesis NERR : is_err r = false.
Let rid := s_next_rid st.
Let st1 := fst (new_region RKMeta r len st).
Let st2 := upd_ctx (fun c => set_meta_alloc_shift (c_meta_alloc_shift c + 1)
(set_avail_meta_area_count (n - 1) (set_avail_meta_areas (Some (rid, PGSZ)) c))) st1.
Let L' := Qgp5.set_metas ((r, len, 0) :: ld_metas L) L.

End NEW_META.

Section BRK_GROW.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (rid : N) (off : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hbrk : c_brk (s_ctx st) = BrkLive rid off.
Hypothesis Hcnt : c_avail_meta_area_count (s_ctx st) = 0.
Let old : Z := conc st (rid, off).
Hypothesis HOK : brk_pages_ok st old PGSZ = true.
Let st1 := upd_region rid (fun rg => mkRegion (r_kind rg) (r_base rg) (off + PGSZ)) st.
Let st2 := upd_ctx (fun c => set_avail_meta_area_count 1 (set_avail_meta_areas (Some (rid, off)) (set_brk (BrkLive rid (off + PGSZ)) c))) st1.
Let st3 := adv st2 (rid, off).

Let L' := Qgp5.set_brkreg (Some (old - off, off + PGSZ)) L.

End BRK_GROW.

Section BRK_FIRST.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (cur : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hbrk : c_brk (s_ctx st) = BrkUntried.
Hypothesis Hcnt : c_avail_meta_area_count (s_ctx st) = 0.
Hypothesis Hcur : brk0_answer_ok cur = true.
Let base : Z := round_up_pg cur.
Hypothesis HOK : brk_pages_ok st base (2 * PGSZ) = true.
Let rid := s_next_rid st.
Let st1 := fst (new_region RKBrk base (2 * PGSZ) st).
Let st2 := upd_ctx (fun c => set_avail_meta_area_count 1 (set_avail_meta_areas (Some (rid, PGSZ)) (set_brk (BrkLive rid (2 * PGSZ)) c))) st1.
Let st3 := adv st2 (rid, PGSZ).
Variable L0 : mled.
Hypothesis HL0 : ld_resv L0 = ld_resv L /\ ld_groups L0 = ld_groups L /\ ld_metas L0 = ld_metas L.
Let L' := Qgp5.set_brkph BPLive (Qgp5.set_brkreg (Some (base, 2 * PGSZ)) L0).

End BRK_FIRST.
