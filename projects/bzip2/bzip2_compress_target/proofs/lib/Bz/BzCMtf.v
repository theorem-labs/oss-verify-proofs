(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCHuff.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition BZ_RUNA : Z := 0.
Definition BZ_RUNB : Z := 1.
(* [comment removed for export] *)
Definition BZ_N_ITERS : nat := 4%nat.
Definition BZ_LESSER_ICOST : Z := 0.
Definition BZ_GREATER_ICOST : Z := 15.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint mk_maps (n : nat) (inUse unseq : zarr) (i nInUse : Z) : zarr * Z :=
  match n with
  | O => (unseq, nInUse)
  | S n' => if negb (zget inUse i =? 0)
            then mk_maps n' inUse (zset unseq i nInUse) (i + 1) (nInUse + 1)
            else mk_maps n' inUse unseq (i + 1) nInUse
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mtf_emit (arr1 mtfFreq : zarr) (wr v : Z) : zarr * zarr * Z :=
  (wr16 arr1 (2 * wr) v, zincr mtfFreq v, wr + 1).

(* [comment removed for export] *)
Fixpoint mtf_zrun (fuel : nat) (arr1 mtfFreq : zarr) (wr zPend : Z) : zarr * zarr * Z :=
  match fuel with
  | O => (arr1, mtfFreq, wr)
  | S f =>
      let '(arr1, mtfFreq, wr) := mtf_emit arr1 mtfFreq wr (if Z.land zPend 1 =? 0 then BZ_RUNA else BZ_RUNB) in
      if zPend <? 2 then (arr1, mtfFreq, wr)
      else mtf_zrun f arr1 mtfFreq wr ((zPend - 2) / 2)
  end.

(* [comment removed for export] *)
Fixpoint mtf_search (fuel : nat) (yy : zarr) (ll_i rtmp p : Z) : zarr * Z * Z :=
  match fuel with
  | O => (yy, rtmp, p)
  | S f => if ll_i =? rtmp then (yy, rtmp, p)
           else let p := p + 1 in let rtmp2 := rtmp in let rtmp' := zget yy p in
                mtf_search f (zset yy p rtmp2) ll_i rtmp' p
  end.

(* [comment removed for export] *)
Record gms := GMS { gm_arr1 : zarr; gm_mtfFreq : zarr; gm_yy : zarr; gm_wr : Z; gm_zPend : Z }.

Definition gm_iter (arr2 unseq : zarr) (nblock i : Z) (s : gms) : gms :=
  let j := rd32 (gm_arr1 s) i - 1 in
  let j := if j <? 0 then j + nblock else j in
  let ll_i := zget unseq (rd8 arr2 j) in
  if zget (gm_yy s) 0 =? ll_i then GMS (gm_arr1 s) (gm_mtfFreq s) (gm_yy s) (gm_wr s) (gm_zPend s + 1)
  else
    let '(arr1, mtfFreq, wr) :=
      (if 0 <? gm_zPend s then mtf_zrun 64%nat (gm_arr1 s) (gm_mtfFreq s) (gm_wr s) (gm_zPend s - 1)
       else (gm_arr1 s, gm_mtfFreq s, gm_wr s)) in
    let yy := gm_yy s in
    let rtmp := zget yy 1 in
    let yy := zset yy 1 (zget yy 0) in
    let '(yy, rtmp, p) := mtf_search 258%nat yy ll_i rtmp 1 in
    let yy := zset yy 0 rtmp in
    let '(arr1, mtfFreq, wr) := mtf_emit arr1 mtfFreq wr (p + 1) in
    GMS arr1 mtfFreq yy wr 0.

Fixpoint gm_loop (n : nat) (arr2 unseq : zarr) (nblock i : Z) (s : gms) : gms :=
  match n with
  | O => s
  | S n' => gm_loop n' arr2 unseq nblock (i + 1) (gm_iter arr2 unseq nblock i s)
  end.

(* [comment removed for export] *)
Fixpoint zfill0 (n : nat) (a : zarr) (i : Z) : zarr :=
  match n with O => a | S n' => zfill0 n' (zset a i 0) (i + 1) end.
Fixpoint yy_init (n : nat) (yy : zarr) (i : Z) : zarr :=
  match n with O => yy | S n' => yy_init n' (zset yy i i) (i + 1) end.

(* [comment removed for export] *)
Definition generateMTFValues (e : est) (yy0 : zarr) : est * zarr :=
  let '(unseq, nInUse) := mk_maps 256%nat (e_inUse e) (e_unseqToSeq e) 0 0 in
  let EOB := nInUse + 1 in
  let mtfFreq := zfill0 (Z.to_nat (EOB + 1)) (e_mtfFreq e) 0 in
  let yy := yy_init (Z.to_nat nInUse) yy0 0 in
  let s := gm_loop (Z.to_nat (e_nblock e)) (e_arr2 e) unseq (e_nblock e) 0 (GMS (e_arr1 e) mtfFreq yy 0 0) in
  let '(arr1, mtfFreq, wr) :=
    (if 0 <? gm_zPend s then mtf_zrun 64%nat (gm_arr1 s) (gm_mtfFreq s) (gm_wr s) (gm_zPend s - 1)
     else (gm_arr1 s, gm_mtfFreq s, gm_wr s)) in
  let '(arr1, mtfFreq, wr) := mtf_emit arr1 mtfFreq wr EOB in
  (EST (e_mode e) (e_state e) (e_avail_in_expect e) arr1 (e_arr2 e) (e_ftab e) (e_origPtr e)
       (e_state_in_ch e) (e_state_in_len e) (e_nblock e) (e_state_out_pos e) nInUse (e_inUse e) unseq
       (e_bw e) (e_blockCRC e) (e_combinedCRC e) (e_blockNo e) wr mtfFreq (e_selector e) (e_selectorMtf e)
       (e_len e) (e_code e) (e_rfreq e) (e_len_pack e),
   gm_yy s).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint sm_len_init_row (n : nat) (len : zarr) (t v : Z) : zarr :=
  match n with O => len | S n' => sm_len_init_row n' (zset len (258 * t + v) BZ_GREATER_ICOST) t (v + 1) end.
Fixpoint sm_len_init (n : nat) (len : zarr) (alphaSize t : Z) : zarr :=
  match n with O => len | S n' => sm_len_init n' (sm_len_init_row (Z.to_nat alphaSize) len t 0) alphaSize (t + 1) end.

Definition sm_nGroups (nMTF : Z) : Z :=
  if nMTF <? 200 then 2 else if nMTF <? 600 then 3 else if nMTF <? 1200 then 4 else if nMTF <? 2400 then 5 else 6.

(* [comment removed for export] *)
Fixpoint sm_grow (fuel : nat) (mtfFreq : zarr) (tFreq alphaSize ge aFreq : Z) : Z * Z :=
  match fuel with
  | O => (ge, aFreq)
  | S f => if (aFreq <? tFreq) && (ge <? alphaSize - 1)
           then sm_grow f mtfFreq tFreq alphaSize (ge + 1) (aFreq + zget mtfFreq (ge + 1))
           else (ge, aFreq)
  end.
(* [comment removed for export] *)
Fixpoint sm_setrow (n : nat) (len : zarr) (t gs ge v : Z) : zarr :=
  match n with
  | O => len
  | S n' => sm_setrow n' (zset len (258 * t + v) (if (gs <=? v) && (v <=? ge) then BZ_LESSER_ICOST else BZ_GREATER_ICOST)) t gs ge (v + 1)
  end.
Record sip := SIP { ip_len : zarr; ip_nPart : Z; ip_remF : Z; ip_gs : Z }.
Definition sm_init_iter (mtfFreq : zarr) (nGroups alphaSize : Z) (s : sip) : sip :=
  let nPart := ip_nPart s in
  let tFreq := ip_remF s / nPart in
  let '(ge, aFreq) := sm_grow 260%nat mtfFreq tFreq alphaSize (ip_gs s - 1) 0 in
  let '(ge, aFreq) :=
    (if (ip_gs s <? ge) && negb (nPart =? nGroups) && negb (nPart =? 1) && ((nGroups - nPart) mod 2 =? 1)
     then (ge - 1, aFreq - zget mtfFreq ge) else (ge, aFreq)) in
  let len := sm_setrow (Z.to_nat alphaSize) (ip_len s) (nPart - 1) (ip_gs s) ge 0 in
  SIP len (nPart - 1) (ip_remF s - aFreq) (ge + 1).
Fixpoint sm_init_tables (fuel : nat) (mtfFreq : zarr) (nGroups alphaSize : Z) (s : sip) : sip :=
  match fuel with
  | O => s
  | S f => if 0 <? ip_nPart s then sm_init_tables f mtfFreq nGroups alphaSize (sm_init_iter mtfFreq nGroups alphaSize s) else s
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint sm_rfreq_zero (n : nat) (rf : zarr) (alphaSize t : Z) : zarr :=
  match n with O => rf | S n' => sm_rfreq_zero n' (zfill0 (Z.to_nat alphaSize) rf (258 * t)) alphaSize (t + 1) end.
(* [comment removed for export] *)
Fixpoint sm_lenpack (n : nat) (lp len : zarr) (v : Z) : zarr :=
  match n with
  | O => lp
  | S n' =>
      let lp := zset lp (4 * v) (Z.lor (Z.shiftl (zget len (258 * 1 + v)) 16) (zget len (258 * 0 + v))) in
      let lp := zset lp (4 * v + 1) (Z.lor (Z.shiftl (zget len (258 * 3 + v)) 16) (zget len (258 * 2 + v))) in
      let lp := zset lp (4 * v + 2) (Z.lor (Z.shiftl (zget len (258 * 5 + v)) 16) (zget len (258 * 4 + v))) in
      sm_lenpack n' lp len (v + 1)
  end.

(* [comment removed for export] *)
Definition mtfv_at (arr1 : zarr) (i : Z) : Z := rd16 arr1 (2 * i).

(* [comment removed for export] *)
Fixpoint sm_cost_fast (n : nat) (arr1 lp : zarr) (i c01 c23 c45 : Z) : Z * Z * Z :=
  match n with
  | O => (c01, c23, c45)
  | S n' => let icv := mtfv_at arr1 i in
            sm_cost_fast n' arr1 lp (i + 1) ((c01 + zget lp (4 * icv)) mod 4294967296) ((c23 + zget lp (4 * icv + 1)) mod 4294967296) ((c45 + zget lp (4 * icv + 2)) mod 4294967296)
  end.
(* [comment removed for export] *)
Fixpoint sm_cost_slow_t (n : nat) (cost len : zarr) (icv t : Z) : zarr :=
  match n with O => cost | S n' => sm_cost_slow_t n' (zset cost t ((zget cost t + zget len (258 * t + icv)) mod 65536)) len icv (t + 1) end.
Fixpoint sm_cost_slow (n : nat) (cost len arr1 : zarr) (nGroups i : Z) : zarr :=
  match n with O => cost | S n' => sm_cost_slow n' (sm_cost_slow_t (Z.to_nat nGroups) cost len (mtfv_at arr1 i) 0) len arr1 nGroups (i + 1) end.
(* [comment removed for export] *)
Fixpoint sm_best (n : nat) (cost : zarr) (t bc bt : Z) : Z * Z :=
  match n with O => (bc, bt) | S n' => if zget cost t <? bc then sm_best n' cost (t + 1) (zget cost t) t else sm_best n' cost (t + 1) bc bt end.
(* [comment removed for export] *)
Fixpoint sm_rfreq_inc (n : nat) (rf arr1 : zarr) (bt i : Z) : zarr :=
  match n with O => rf | S n' => sm_rfreq_inc n' (zincr rf (258 * bt + mtfv_at arr1 i)) arr1 bt (i + 1) end.
(* [comment removed for export] *)
Definition zero6 (a : zarr) : zarr := zfill0 6%nat a 0.

(* [comment removed for export] *)
Record sgs := SGS { g_rfreq : zarr; g_sel : zarr; g_cost : zarr; g_fave : zarr; g_nSel : Z; g_totc : Z; g_gs : Z }.
Definition sm_group_iter (arr1 len lp : zarr) (nGroups nMTF : Z) (s : sgs) : sgs :=
  let gs := g_gs s in
  let ge := gs + BZ_G_SIZE - 1 in
  let ge := if nMTF <=? ge then nMTF - 1 else ge in
  let cost := zero6 (g_cost s) in
  let cost :=
    (if (nGroups =? 6) && (ge - gs + 1 =? 50) then
       let '(c01, c23, c45) := sm_cost_fast 50%nat arr1 lp gs 0 0 0 in
       let cost := zset cost 0 (Z.land c01 65535) in let cost := zset cost 1 (Z.shiftr c01 16) in
       let cost := zset cost 2 (Z.land c23 65535) in let cost := zset cost 3 (Z.shiftr c23 16) in
       let cost := zset cost 4 (Z.land c45 65535) in zset cost 5 (Z.shiftr c45 16)
     else sm_cost_slow (Z.to_nat (ge - gs + 1)) cost len arr1 nGroups gs) in
  let '(bc, bt) := sm_best (Z.to_nat nGroups) cost 0 999999999 (-1) in
  let fave := zincr (g_fave s) bt in
  let sel := zset (g_sel s) (g_nSel s) (bt mod 256) in
  let rf := sm_rfreq_inc (Z.to_nat (ge - gs + 1)) (g_rfreq s) arr1 bt gs in
  SGS rf sel cost fave (g_nSel s + 1) (g_totc s + bc) (ge + 1).
Fixpoint sm_groups (fuel : nat) (arr1 len lp : zarr) (nGroups nMTF : Z) (s : sgs) : sgs :=
  match fuel with
  | O => s
  | S f => if nMTF <=? g_gs s then s else sm_groups f arr1 len lp nGroups nMTF (sm_group_iter arr1 len lp nGroups nMTF s)
  end.

(* [comment removed for export] *)
Fixpoint sm_mklens (n : nat) (len rf heap weight parent : zarr) (alphaSize t : Z) : zarr * zarr * zarr * zarr :=
  match n with
  | O => (len, heap, weight, parent)
  | S n' => let h := hbMakeCodeLengths len rf heap weight parent (258 * t) (258 * t) alphaSize 17 in
            sm_mklens n' (hs_len h) rf (hs_heap h) (hs_weight h) (hs_parent h) alphaSize (t + 1)
  end.

(* [comment removed for export] *)
Record sits := SITS { it_len : zarr; it_rfreq : zarr; it_lp : zarr; it_sel : zarr; it_cost : zarr; it_fave : zarr;
                      it_nSel : Z; it_heap : zarr; it_weight : zarr; it_parent : zarr }.
Definition sm_iter (arr1 : zarr) (nGroups alphaSize nMTF : Z) (s : sits) : sits :=
  let fave := zero6 (it_fave s) in
  let rf := sm_rfreq_zero (Z.to_nat nGroups) (it_rfreq s) alphaSize 0 in
  let lp := if nGroups =? 6 then sm_lenpack (Z.to_nat alphaSize) (it_lp s) (it_len s) 0 else it_lp s in
  let g := sm_groups (Z.to_nat (nMTF + 1)) arr1 (it_len s) lp nGroups nMTF (SGS rf (it_sel s) (it_cost s) fave 0 0 0) in
  let '(len, heap, weight, parent) := sm_mklens (Z.to_nat nGroups) (it_len s) (g_rfreq g) (it_heap s) (it_weight s) (it_parent s) alphaSize 0 in
  SITS len (g_rfreq g) lp (g_sel g) (g_cost g) (g_fave g) (g_nSel g) heap weight parent.
Fixpoint sm_iters (n : nat) (arr1 : zarr) (nGroups alphaSize nMTF : Z) (s : sits) : sits :=
  match n with O => s | S n' => sm_iters n' arr1 nGroups alphaSize nMTF (sm_iter arr1 nGroups alphaSize nMTF s) end.

(* [comment removed for export] *)
Fixpoint sm_pos_search (fuel : nat) (pos : zarr) (ll_i tmp j : Z) : zarr * Z * Z :=
  match fuel with
  | O => (pos, tmp, j)
  | S f => if ll_i =? tmp then (pos, tmp, j)
           else let j := j + 1 in let tmp2 := tmp in let tmp' := zget pos j in
                sm_pos_search f (zset pos j tmp2) ll_i tmp' j
  end.
Fixpoint sm_selmtf (n : nat) (pos sel selMtf : zarr) (i : Z) : zarr * zarr :=
  match n with
  | O => (pos, selMtf)
  | S n' => let ll_i := zget sel i in
            let '(pos, tmp, j) := sm_pos_search 8%nat pos ll_i (zget pos 0) 0 in
            let pos := zset pos 0 tmp in
            sm_selmtf n' pos sel (zset selMtf i j) (i + 1)
  end.

(* [comment removed for export] *)
Fixpoint sm_minmax (n : nat) (len : zarr) (t i minLen maxLen : Z) : Z * Z :=
  match n with
  | O => (minLen, maxLen)
  | S n' => let l := zget len (258 * t + i) in
            let maxLen := if maxLen <? l then l else maxLen in
            let minLen := if l <? minLen then l else minLen in
            sm_minmax n' len t (i + 1) minLen maxLen
  end.
Fixpoint sm_assign (n : nat) (code len : zarr) (alphaSize t : Z) : zarr :=
  match n with
  | O => code
  | S n' => let '(minLen, maxLen) := sm_minmax (Z.to_nat alphaSize) len t 0 32 0 in
            sm_assign n' (hbAssignCodes code len (258 * t) (258 * t) minLen maxLen alphaSize) len alphaSize (t + 1)
  end.

(* [comment removed for export] *)
Fixpoint sm_in16_row (n : nat) (inUse : zarr) (i j : Z) (acc : Z) : Z :=
  match n with O => acc | S n' => sm_in16_row n' inUse i (j + 1) (if negb (zget inUse (i * 16 + j) =? 0) then 1 else acc) end.
Fixpoint sm_in16 (n : nat) (in16 inUse : zarr) (i : Z) : zarr :=
  match n with O => in16 | S n' => sm_in16 n' (zset in16 i (sm_in16_row 16%nat inUse i 0 0)) inUse (i + 1) end.
(* [comment removed for export] *)
Fixpoint sm_put_in16 (n : nat) (b : bw) (in16 : zarr) (i : Z) : bw :=
  match n with O => b | S n' => sm_put_in16 n' (bsW b 1 (if negb (zget in16 i =? 0) then 1 else 0)) in16 (i + 1) end.
(* [comment removed for export] *)
Fixpoint sm_put_inuse_row (n : nat) (b : bw) (inUse : zarr) (i j : Z) : bw :=
  match n with O => b | S n' => sm_put_inuse_row n' (bsW b 1 (if negb (zget inUse (i * 16 + j) =? 0) then 1 else 0)) inUse i (j + 1) end.
Fixpoint sm_put_inuse (n : nat) (b : bw) (in16 inUse : zarr) (i : Z) : bw :=
  match n with
  | O => b
  | S n' => let b := if negb (zget in16 i =? 0) then sm_put_inuse_row 16%nat b inUse i 0 else b in
            sm_put_inuse n' b in16 inUse (i + 1)
  end.
(* [comment removed for export] *)
Fixpoint sm_put_ones (n : nat) (b : bw) : bw := match n with O => b | S n' => sm_put_ones n' (bsW b 1 1) end.
Fixpoint sm_put_sels (n : nat) (b : bw) (selMtf : zarr) (i : Z) : bw :=
  match n with O => b | S n' => sm_put_sels n' (bsW (sm_put_ones (Z.to_nat (zget selMtf i)) b) 1 0) selMtf (i + 1) end.
(* [comment removed for export] *)
Fixpoint sm_put_up (fuel : nat) (b : bw) (curr tgt : Z) : bw * Z :=
  match fuel with O => (b, curr) | S f => if curr <? tgt then sm_put_up f (bsW b 2 2) (curr + 1) tgt else (b, curr) end.
Fixpoint sm_put_down (fuel : nat) (b : bw) (curr tgt : Z) : bw * Z :=
  match fuel with O => (b, curr) | S f => if tgt <? curr then sm_put_down f (bsW b 2 3) (curr - 1) tgt else (b, curr) end.
Fixpoint sm_put_lens_row (n : nat) (b : bw) (len : zarr) (t i curr : Z) : bw * Z :=
  match n with
  | O => (b, curr)
  | S n' => let tgt := zget len (258 * t + i) in
            let '(b, curr) := sm_put_up 40%nat b curr tgt in
            let '(b, curr) := sm_put_down 40%nat b curr tgt in
            sm_put_lens_row n' (bsW b 1 0) len t (i + 1) curr
  end.
Fixpoint sm_put_lens (n : nat) (b : bw) (len : zarr) (alphaSize t : Z) : bw :=
  match n with
  | O => b
  | S n' => let curr := zget len (258 * t + 0) in
            let '(b, _) := sm_put_lens_row (Z.to_nat alphaSize) (bsW b 5 curr) len t 0 curr in
            sm_put_lens n' b len alphaSize (t + 1)
  end.
(* [comment removed for export] *)
Fixpoint sm_put_syms (n : nat) (b : bw) (len code arr1 : zarr) (sel i : Z) : bw :=
  match n with
  | O => b
  | S n' => let v := mtfv_at arr1 i in
            sm_put_syms n' (bsW b (zget len (258 * sel + v)) (zget code (258 * sel + v))) len code arr1 sel (i + 1)
  end.
Fixpoint sm_put_data (fuel : nat) (b : bw) (len code arr1 sel : zarr) (nMTF gs selCtr : Z) : bw * Z :=
  match fuel with
  | O => (b, selCtr)
  | S f => if nMTF <=? gs then (b, selCtr) else
           let ge := gs + BZ_G_SIZE - 1 in
           let ge := if nMTF <=? ge then nMTF - 1 else ge in
           let b := sm_put_syms (Z.to_nat (ge - gs + 1)) b len code arr1 (zget sel selCtr) gs in
           sm_put_data f b len code arr1 sel nMTF (ge + 1) (selCtr + 1)
  end.

(* [comment removed for export] *)
Record smloc := SML { sl_cost : zarr; sl_fave : zarr; sl_pos : zarr; sl_in16 : zarr; sl_heap : zarr; sl_weight : zarr; sl_parent : zarr;
                      sl_nGroups : Z; sl_nSelectors : Z; sl_alphaSize : Z }.

Definition sendMTFValues (e : est) (cost0 fave0 pos0 in160 heap0 weight0 parent0 : zarr) : est * smloc :=
  let alphaSize := e_nInUse e + 2 in
  let nMTF := e_nMTF e in
  let len := sm_len_init 6%nat (e_len e) alphaSize 0 in
  let nGroups := sm_nGroups nMTF in
  let ip := sm_init_tables 8%nat (e_mtfFreq e) nGroups alphaSize (SIP len nGroups nMTF 0) in
  let it := sm_iters BZ_N_ITERS (e_arr1 e) nGroups alphaSize nMTF
              (SITS (ip_len ip) (e_rfreq e) (e_len_pack e) (e_selector e) cost0 fave0 0 heap0 weight0 parent0) in
  let nSelectors := it_nSel it in
  let pos := yy_init (Z.to_nat nGroups) pos0 0 in
  let '(pos, selMtf) := sm_selmtf (Z.to_nat nSelectors) pos (it_sel it) (e_selectorMtf e) 0 in
  let code := sm_assign (Z.to_nat nGroups) (e_code e) (it_len it) alphaSize 0 in
  let in16 := sm_in16 16%nat in160 (e_inUse e) 0 in
  let b := sm_put_in16 16%nat (e_bw e) in16 0 in
  let b := sm_put_inuse 16%nat b in16 (e_inUse e) 0 in
  let b := bsW b 3 nGroups in
  let b := bsW b 15 nSelectors in
  let b := sm_put_sels (Z.to_nat nSelectors) b selMtf 0 in
  let b := sm_put_lens (Z.to_nat nGroups) b (it_len it) alphaSize 0 in
  let '(b, selCtr) := sm_put_data (Z.to_nat (nMTF + 1)) b (it_len it) code (e_arr1 e) (it_sel it) nMTF 0 0 in
  (EST (e_mode e) (e_state e) (e_avail_in_expect e) (e_arr1 e) (e_arr2 e) (e_ftab e) (e_origPtr e)
       (e_state_in_ch e) (e_state_in_len e) (e_nblock e) (e_state_out_pos e) (e_nInUse e) (e_inUse e) (e_unseqToSeq e)
       b (e_blockCRC e) (e_combinedCRC e) (e_blockNo e) nMTF (e_mtfFreq e) (it_sel it) selMtf
       (it_len it) code (it_rfreq it) (it_lp it),
   SML (it_cost it) (it_fave it) pos in16 (it_heap it) (it_weight it) (it_parent it) nGroups nSelectors alphaSize).
