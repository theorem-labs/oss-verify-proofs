(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec Image FP.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import ImageA.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import Layout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit D_iface D_defs D_libiface Lept_iface LeptB_guard.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition e_reallocNew : Z := 0xe9530.
Definition e_numaFindExtrema : Z := 0xef31c.
Definition e_numaCreate : Z := 0xef780.
Definition e_numaDestroy : Z := 0xef9dc.
Definition e_numaAddNumber : Z := 0xefb30.
Definition e_numaGetCount : Z := 0xefd88.
Definition e_numaExtendArray : Z := 0xefe44.
Definition e_numaGetFValue : Z := 0xf006c.
Definition e_numaGetIValue : Z := 0xf0294.
Definition e_pixGetPixel : Z := 0xf691c.
Definition e_pixMeasureEdgeSmoothness : Z := 0x12c1d0.
Definition e_pixGetEdgeProfile : Z := 0x12c8dc.
(* [comment removed for export] *)
Definition e_pixGetLastOffPixelInRun : Z := 0x12d0ec.
Definition e_pixGetLastOnPixelInRun : Z := 0x12d610.

(* [comment removed for export] *)
Definition RA_FUZZ_MEASURE : Z := 0xe7418.      (* [comment removed for export] *)
Definition RA_MEASURE_PROFILE : Z := 0x12c3c0.  (* [comment removed for export] *)
Definition RA_MEASURE_EXTREMA : Z := 0x12c778.  (* [comment removed for export] *)
Definition RA_NUMACREATE_CALLOC1 : Z := 0xef7c8. (* [comment removed for export] *)
(* [comment removed for export] *)
Definition numaCreate_trace_ok (ch : list Z) : Prop := Forall (fun r => 4096 <= r < 2^64) ch.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition RO_SIGN_TAB : Z := 0x2dc48.          (* [comment removed for export] *)
Definition RO_HALF : Z := 0x10538.
(* [comment removed for export] *)
Definition RO_GUARD_LO : Z := 0x10580.
Definition RO_GUARD_HI : Z := 0x10438.
Definition D_GUARD_LO : word := Z_to_bv 64 0xc1e0000000200000.
Definition D_GUARD_HI : word := Z_to_bv 64 0x41e0000000000000.
Definition D_ONE : word := Z_to_bv 64 0x3ff0000000000000.
Definition D_MONE : word := Z_to_bv 64 0xbff0000000000000.
Definition D_HALF : word := Z_to_bv 64 0x3fe0000000000000.
Definition ED_RO (m : mem) : Prop :=
  ro_cells asegs m RO_SIGN_TAB [C8 D_ONE; C8 D_MONE] /\ ro_cells asegs m RO_HALF [C8 D_HALF]
  /\ ro_cells asegs m RO_GUARD_LO [C8 D_GUARD_LO] /\ ro_cells asegs m RO_GUARD_HI [C8 D_GUARD_HI].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ival_w (k : Z) : word := fcvt_s_w RNE (Z_to_bv 64 k).
(* [comment removed for export] *)
Definition DELTA_W : word := fcvt_s_wu RNE (Z_to_bv 64 1).
(* [comment removed for export] *)
Definition FZERO_W : word := nan_box (Z_to_bv 32 0).
(* [comment removed for export] *)
Definition fa0 : bv 5 := Z_to_bv 5 10.
Definition freg_is (F : bvmap 5 word) (r : bv 5) (v : word) : Prop := reg_get F r = v.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition GETPIXEL_COST : Z := 1.
(* [comment removed for export] *)
Definition PROFILE_COST (w h : Z) : Z := h * (w + 3) + mcost (4 * h) + 2.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition EXTREMA_GROWTH_COST : Z := mcost 102400.
Definition EXTREMA_COST : Z := EXTREMA_GROWTH_COST + 4.
(* [comment removed for export] *)
Definition MEASURE_COST (w h : Z) : Z := PROFILE_COST w h + EXTREMA_COST + 4.
(* [comment removed for export] *)
Definition ED_FUZZ_NEED (w h : Z) : Z := (RASTER_COST + 64) + MEASURE_COST w h + 4.
Lemma measure_cost_bound : forall w h, 0 < w <= 20000 -> 0 < h <= 20000 -> MEASURE_COST w h <= 2^29.
Proof.
  intros w h Hw Hh. unfold MEASURE_COST, PROFILE_COST, EXTREMA_COST, EXTREMA_GROWTH_COST, mcost.
  destruct (4 * h <=? 64512); cbn -[Z.mul Z.add Z.le Z.pow]; nia.
Qed.
Lemma ed_fuzz_need_ok : forall w h, 0 < w <= 20000 -> 0 < h <= 20000 -> ED_FUZZ_NEED w h <= FUZZ_COST.
Proof.
  intros w h Hw Hh. unfold ED_FUZZ_NEED. pose proof (measure_cost_bound w h Hw Hh).
  unfold RASTER_COST, FUZZ_COST. lia.
Qed.
(* [comment removed for export] *)
Definition CALLOC_SEC_MAX : Z := 0x20000.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition numa_cells (cap n arr : Z) (pad : list byte) : list cell :=
  [C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 n); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0x3f800000); CB 4 pad; C8 (Z_to_bv 64 arr)].
(* [comment removed for export] *)
Definition numa_arr_cells (cap : Z) (vals : list word) (junk : list byte) : list cell :=
  map C4 vals ++ [CB (Z.to_nat (4 * cap - 4 * Z.of_nat (length vals))) junk].
Definition numa_obj (live : list (Z * Z)) (m : mem) (na cap arr : Z) (vals : list word) : Prop :=
  (exists pad, rw_cells asegs m na (numa_cells cap (Z.of_nat (length vals)) arr pad))
  /\ (exists junk, rw_cells asegs m arr (numa_arr_cells cap vals junk))
  /\ chunk live na 32 /\ chunk live arr (4 * cap) /\ arr <> na
  /\ 1 <= cap <= 25600 /\ Z.of_nat (length vals) <= cap.
(* [comment removed for export] *)
Definition numa_live (na cap arr : Z) (live : list (Z * Z)) : list (Z * Z) := (arr, 4 * cap) :: (na, 32) :: live.
(* [comment removed for export] *)
Definition numa_gone (na arr : Z) (live : list (Z * Z)) : list (Z * Z) := live_remove na (live_remove arr live).
(* [comment removed for export] *)
Definition LOC_LO : Z := -1.      (* [comment removed for export] *)
Definition LOC_HI : Z := 20000.
Definition loc_ok (k : Z) : Prop := LOC_LO <= k <= LOC_HI.
Definition numa_ints (vals : list word) (ks : list Z) : Prop := vals = map ival_w ks /\ Forall loc_ok ks.

(* [comment removed for export] *)
Definition in_pix (v : pixv) (x y : Z) : Prop := 0 <= x < p_w v /\ 0 <= y < p_h v.
Definition in_pixb (v : pixv) (x y : Z) : bool := (0 <=? x) && (x <? p_w v) && (0 <=? y) && (y <? p_h v).
Definition pixel_word_addr (v : pixv) (x y : Z) : Z := p_data v + 4 * (y * p_wpl v + x / 32).
Definition pixel_val (m : mem) (v : pixv) (x y b : Z) : Prop :=
  exists wd : word, rw_cells asegs m (pixel_word_addr v x y) [C4 wd] /\ b = Z.b2z (Z.testbit (bv_unsigned wd) (31 - x mod 32)).

Section EdIface.
Variable RT : rt_sig.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition calloc_contract_sec : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (nmemb size lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  0 < nmemb -> 0 < size -> CALLOC_MAX < nmemb * size <= CALLOC_SEC_MAX -> a0 = Z_to_bv 64 nmemb -> a1 = Z_to_bv 64 size -> tp = Z_to_bv 64 TP_A ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost (nmemb * size) <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> unwind_okC m ra s0 sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_calloc m)))
    (fun c => exists (Σ' : rts RT) (p : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
         /\ wr_at asegs m' p (nmemb * size) /\ acc asegs m' p (nmemb * size)) c
       /\ rt_live RT Σ' = (p, nmemb * size) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - mcost (nmemb * size) /\ 0 < p /\ p mod 16 = 0 /\ p + nmemb * size < USTACK_TOP).

(* [comment removed for export] *)
Definition ret_stF (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (v : word)
    (m' : mem) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra) fc None m' (seg_rom asegs).
Definition stack_malloc_contractF (k : nat) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> (k <= 10)%nat -> tp = Z_to_bv 64 TP_A ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc (e_stack_malloc k) m)))
    (fun c => exists (Σ' : rts RT) (f : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
                                             (ms_fcsr (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc 0 m))
                                             (Z_to_bv 64 f) m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
         /\ wr_at asegs m' f (fs_size k - 8) /\ wr_at asegs m' (shad f) (fs_size k / 8)) c
       /\ rt_frames RT Σ' = (f, k) :: rt_frames RT Σ /\ rt_live RT Σ' = rt_live RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - 1 /\ 0 < f /\ f mod 64 = 0 /\ f + fs_size k < USTACK_TOP).
(* [comment removed for export] *)

Record ed_gaps : Prop := mkEdGaps {
  eg_calloc_sec : calloc_contract_sec;
  eg_stack_malloc0F : stack_malloc_contractF 0
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition numa_cap (n : Z) : Z := if n =? 0 then 50 else n.
Definition numaCreate_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (n : Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  s32 a0 n -> 0 <= n <= 20000 ->
  uctx m sp s0 ras -> numaCreate_trace_ok ras ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 0 2 (mcost (4 * numa_cap n)) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_numaCreate m)))
    (fun c => exists (Σ' : rts RT) (na arr : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 na) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ numa_obj (rt_live RT Σ') m' na (numa_cap n) arr []) c
       /\ rt_live RT Σ' = numa_live na (numa_cap n) arr (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - mcost (4 * numa_cap n) <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition numaDestroy_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pna na cap arr : Z) (vals : list word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pna -> optrF RT Σ m pna 8 -> rw_cells asegs m pna [C8 (Z_to_bv 64 na)] ->
  numa_obj (rt_live RT Σ) m na cap arr vals ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 0 0 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_numaDestroy m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pna, pna + 8)] m m' /\ rw_cells asegs m' pna [C8 (Z_to_bv 64 0)]) c
       /\ rt_live RT Σ' = numa_gone na arr (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition numaDestroy_null_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pna : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pna -> optrF RT Σ m pna 8 -> rw_cells asegs m pna [C8 (Z_to_bv 64 0)] ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 0 0 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_numaDestroy m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [] m m') c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition reallocNew_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pind old oldsz newsz : Z) (vals : list word) (junk : list byte),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pind -> a1 = Z_to_bv 64 oldsz -> a2 = Z_to_bv 64 newsz ->
  optr RT Σ m pind 8 -> rw_cells asegs m pind [C8 (Z_to_bv 64 old)] ->
  chunk (rt_live RT Σ) old oldsz -> (old + oldsz <= pind \/ pind + 8 <= old) ->
  rw_cells asegs m old (map C4 vals ++ [CB (Z.to_nat (oldsz - 4 * Z.of_nat (length vals))) junk]) -> 4 * Z.of_nat (length vals) <= oldsz ->
  0 < oldsz <= newsz -> newsz <= CALLOC_SEC_MAX ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 0 1 (mcost newsz) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_reallocNew m)))
    (fun c => exists (Σ' : rts RT) (nw : Z),
       ASTA RT Σ' PMc (fun ms => exists m' junk', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 nw) m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keepsL RT (live_remove old (rt_live RT Σ)) Σ sp [(pind, pind + 8)] m m'
          /\ rw_cells asegs m' pind [C8 (Z_to_bv 64 0)]
          /\ rw_cells asegs m' nw (map C4 vals ++ [CB (Z.to_nat (newsz - 4 * Z.of_nat (length vals))) junk'])
          /\ chunk (rt_live RT Σ') nw newsz) c
       /\ rt_live RT Σ' = (nw, newsz) :: live_remove old (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - mcost newsz <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition numaAddNumber_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (na cap arr : Z) (vals : list word) (v : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 na -> freg_is F fa0 v ->
  numa_obj (rt_live RT Σ) m na cap arr vals -> 2 * cap <= 25600 ->
  lenv RT Σ m sp lo (LSTK 5) -> lres RT Σ 0 1 (mcost (8 * cap)) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_numaAddNumber m)))
    (fun c => exists (Σ' : rts RT) (cap' arr' : Z) (v' : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo
          /\ keepsL RT (live_remove arr (rt_live RT Σ)) Σ sp [(na, na + 32)] m m'
          /\ numa_obj (rt_live RT Σ') m' na cap' arr' (vals ++ [v'])) c
       /\ ((Z.of_nat (length vals) < cap /\ cap' = cap /\ arr' = arr /\ v' = v /\ rt_live RT Σ' = rt_live RT Σ)
           \/ (Z.of_nat (length vals) = cap /\ cap' = 2 * cap /\ rt_live RT Σ' = (arr', 4 * cap') :: live_remove arr (rt_live RT Σ)))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - mcost (8 * cap) <= rt_credit RT Σ').
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition numaAddNumber_fast_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (na cap arr : Z) (vals : list word) (v : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 na -> freg_is F fa0 v ->
  numa_obj (rt_live RT Σ) m na cap arr vals -> Z.of_nat (length vals) < cap ->
  lenv RT Σ m sp lo (LSTK 5) -> lres RT Σ 0 0 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_numaAddNumber m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
          /\ lpost RT Σ Σ' m m' sp lo
          /\ keeps RT Σ Σ' sp [(na, na + 32); (arr, arr + 4 * cap)] m m'
          /\ numa_obj (rt_live RT Σ') m' na cap arr (vals ++ [v])) c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ <= rt_credit RT Σ').

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition getpixel_ret (v : pixv) (x y : Z) : Z := if in_pixb v x y then 0 else 2.
Definition pixGetPixel1_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix pval x y : Z) (v : pixv) (cv : cmapv) (old : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> s32 a1 x -> s32 a2 y -> a3 = Z_to_bv 64 pval ->
  pix_obj (rt_live RT Σ) m pix v cv -> p_d v = 1 -> p_data v <> 0 ->
  optrF RT Σ m pval 4 -> rw_cells asegs m pval [C4 old] ->
  lenv RT Σ m sp lo (LSTK 4) -> lres RT Σ 1 0 GETPIXEL_COST ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixGetPixel m)))
    (fun c => exists (Σ' : rts RT) (b : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (getpixel_ret v x y)) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pval, pval + 4)] m m'
          /\ rw_cells asegs m' pval [C4 (Z_to_bv 64 b)]
          /\ (in_pix v x y -> pixel_val m v x y b) /\ (~ in_pix v x y -> b = 0) /\ (b = 0 \/ b = 1)) c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - GETPIXEL_COST <= rt_credit RT Σ').

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition optrS (sp : word) (p n : Z) : Prop :=
  bv_unsigned sp <= p /\ p + n <= USTACK_TOP /\ p mod 4 = 0.

(* [comment removed for export] *)
Definition SCANOFF_COST (x : Z) : Z := x + 3.
Definition SCANON_COST (w x : Z) : Z := w - x + 2.
Definition pixGetLastOffPixelInRunR_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix ploc x y : Z) (v : pixv) (cv : cmapv) (old : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> s32 a1 x -> s32 a2 y -> a3 = Z_to_bv 64 1 -> a4 = Z_to_bv 64 ploc ->
  pix_obj (rt_live RT Σ) m pix v cv -> p_d v = 1 -> p_data v <> 0 -> -1 <= x <= p_w v - 1 -> 0 <= y < p_h v ->
  optrS sp ploc 4 -> rw_cells asegs m ploc [C4 old] ->
  lenv RT Σ m sp lo (LSTK 5) -> lres RT Σ 2 0 (SCANOFF_COST x) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
                                         e_pixGetLastOffPixelInRun m)))
    (fun c => exists (Σ' : rts RT) (r : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(ploc, ploc + 4)] m m'
          /\ rw_cells asegs m' ploc [C4 (Z_to_bv 64 r)] /\ 0 <= r <= x + 1) c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - SCANOFF_COST x <= rt_credit RT Σ').
Definition pixGetLastOnPixelInRunL_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix ploc x y : Z) (v : pixv) (cv : cmapv) (old : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> s32 a1 x -> s32 a2 y -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 ploc ->
  pix_obj (rt_live RT Σ) m pix v cv -> p_d v = 1 -> p_data v <> 0 -> 0 <= x <= p_w v - 1 -> 0 <= y < p_h v ->
  optrS sp ploc 4 -> rw_cells asegs m ploc [C4 old] ->
  lenv RT Σ m sp lo (LSTK 5) -> lres RT Σ 2 0 (SCANON_COST (p_w v) x) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
                                         e_pixGetLastOnPixelInRun m)))
    (fun c => exists (Σ' : rts RT) (r : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(ploc, ploc + 4)] m m'
          /\ rw_cells asegs m' ploc [C4 (Z_to_bv 64 r)] /\ x - 1 <= r <= p_w v - 1) c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - SCANON_COST (p_w v) x <= rt_credit RT Σ').

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pixGetEdgeProfile_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (cv : cmapv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 0 ->
  pix_obj (rt_live RT Σ) m pix v cv -> p_d v = 1 -> p_data v <> 0 ->
  uctx m sp s0 ras -> numaCreate_trace_ok (bv_unsigned ra :: ras) ->
  lenv RT Σ m sp lo (LSTK 6) -> lres RT Σ 4 2 (PROFILE_COST (p_w v) (p_h v)) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixGetEdgeProfile m)))
    (fun c => exists (Σ' : rts RT) (na arr : Z) (ks : list Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 na) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ numa_obj (rt_live RT Σ') m' na (p_h v) arr (map ival_w ks)) c
       /\ Z.of_nat (length ks) = p_h v /\ Forall (fun k => loc_ok k /\ k <= p_w v - 1) ks
       /\ rt_live RT Σ' = numa_live na (p_h v) arr (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - PROFILE_COST (p_w v) (p_h v) <= rt_credit RT Σ').

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition numaFindExtrema_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (nas cap arr : Z) (vals : list word) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 nas -> freg_is F fa0 DELTA_W -> a1 = Z_to_bv 64 0 ->
  numa_obj (rt_live RT Σ) m nas cap arr vals -> 1 <= Z.of_nat (length vals) <= 20000 ->
  uctx m sp s0 ras -> numaCreate_trace_ok (bv_unsigned ra :: ras) ->
  lenv RT Σ m sp lo (LSTK 6) -> lres RT Σ 2 3 EXTREMA_COST ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_numaFindExtrema m)))
    (fun c => exists (Σ' : rts RT) (nad capd arrd : Z) (vd : list word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 nad) m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ numa_obj (rt_live RT Σ') m' nad capd arrd vd) c
       /\ Z.of_nat (length vd) + 1 <= Z.max 1 (Z.of_nat (length vals))
       /\ rt_live RT Σ' = numa_live nad capd arrd (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - EXTREMA_COST <= rt_credit RT Σ').
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pixMeasureEdgeSmoothness_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix p1 p2 p3 : Z) (v : pixv) (cv : cmapv) (o1 o2 o3 : word) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 1 ->
  a4 = Z_to_bv 64 p1 -> a5 = Z_to_bv 64 p2 -> a6 = Z_to_bv 64 p3 -> a7 = Z_to_bv 64 0 ->
  pix_obj (rt_live RT Σ) m pix v cv -> p_data v <> 0 ->
  optrF RT Σ m p1 4 -> optrF RT Σ m p2 4 -> optrF RT Σ m p3 4 ->
  rw_cells asegs m p1 [C4 o1] -> rw_cells asegs m p2 [C4 o2] -> rw_cells asegs m p3 [C4 o3] ->
  p1 + 4 <= p2 -> p2 + 4 <= p3 ->
  uctx m sp s0 ras -> bv_unsigned ra = RA_FUZZ_MEASURE -> ras = [RA_TOP] ->
  lenv RT Σ m sp lo (LSTK 7) -> lres RT Σ 5 6 (MEASURE_COST (p_w v) (p_h v)) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
                                         e_pixMeasureEdgeSmoothness m)))
    (fun c => exists (Σ' : rts RT) (rv y1 y2 y3 : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(p1, p1 + 4); (p2, p2 + 4); (p3, p3 + 4)] m m'
          /\ rw_cells asegs m' p1 [C4 y1] /\ rw_cells asegs m' p2 [C4 y2] /\ rw_cells asegs m' p3 [C4 y3]) c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - MEASURE_COST (p_w v) (p_h v) <= rt_credit RT Σ').

End EdIface.
