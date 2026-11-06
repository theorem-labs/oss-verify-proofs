(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import ImageA.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import RzCPS NodesA Arr FP.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import Layout.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface Km_setelem D_iface D_defs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition e_kernelCreate : Z := 0x9187c.
Definition e_kernelDestroy : Z := 0x91ce0.
Definition e_kernelCreateFromPix : Z := 0x92150.
Definition e_pixGetPixel : Z := 0x8ebf0.

Section KmIface.
Variable RT : rt_sig.

(* [comment removed for export] *)
Definition ret_st_fc (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v : word) (fc : bv 32) (m' : mem) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word),
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F' (ret_pc ra) fc None m' (seg_rom asegs).

(* [comment removed for export] *)
Definition kel_obj (live : list (Z * Z)) (m : mem) (kel sy sx cy cx data : Z) (rows : list Z) : Prop :=
  rw_cells asegs m kel (kel_cells sy sx cy cx data) /\ chunk live kel 24
  /\ u64arr asegs m data (map (Z_to_bv 64) rows) /\ chunk live data (8 * sy) /\ Z.of_nat (length rows) = sy
  /\ Forall (fun r => chunk live r (4 * sx) /\ wr_at asegs m r (4 * sx)) rows
  /\ List.NoDup (kel :: data :: rows) /\ 0 < sy < 2^31 /\ 0 < sx < 2^31.

(* [comment removed for export] *)
Definition km_live (kel data sy sx : Z) (rows : list Z) (live : list (Z * Z)) : list (Z * Z) :=
  rev (map (fun r => (r, 4 * sx)) rows) ++ (data, 8 * sy) :: (kel, 24) :: live.
(* [comment removed for export] *)
Definition rows_remove (rs : list Z) (live : list (Z * Z)) : list (Z * Z) := fold_left (fun l r => live_remove r l) rs live.
Definition km_unlive (kel data : Z) (rows : list Z) (live : list (Z * Z)) : list (Z * Z) :=
  live_remove kel (live_remove data (rows_remove rows live)).

(* [comment removed for export] *)
Definition km_cost (h w : Z) : Z := mcost (8 * h) + h * mcost (4 * w).

(* [comment removed for export] *)
Definition kernelCreate_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (h w : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 h -> a1 = Z_to_bv 64 w -> 3 <= h <= 20000 -> 3 <= w <= 20000 -> h * w <= 2^26 ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 0 (h + 2) (km_cost h w) ->
  sec_bytes (rt_live RT Σ) + 8 * h + 4 * (w * h) <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_kernelCreate m)))
    (fun c => exists (Σ' : rts RT) (kel data : Z) (rows : list Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 kel) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ kel_obj (rt_live RT Σ') m' kel h w 0 0 data rows) c
       /\ rt_live RT Σ' = km_live kel data h w rows (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - km_cost h w <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition kernelDestroy_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pp kel sy sx cy cx data : Z) (rows : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pp -> optrF RT Σ m pp 8 -> rw_cells asegs m pp [C8 (Z_to_bv 64 kel)] ->
  (kel = 0 \/ kel_obj (rt_live RT Σ) m kel sy sx cy cx data rows) ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 0 0 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_kernelDestroy m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pp, pp + 8)] m m' /\ rw_cells asegs m' pp [C8 (Z_to_bv 64 0)]) c
       /\ rt_live RT Σ' = (if kel =? 0 then rt_live RT Σ else km_unlive kel data rows (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition pixGetPixel_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (cv : cmapv) (x y pv : Z) (x0 : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 x -> a2 = Z_to_bv 64 y -> a3 = Z_to_bv 64 pv ->
  pix_obj (rt_live RT Σ) m pix v cv -> p_d v = 8 -> p_data v <> 0 -> 0 <= x < p_w v -> 0 <= y < p_h v ->
  optrF RT Σ m pv 4 -> rw_cells asegs m pv [C4 x0] ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 1 0 1 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixGetPixel m)))
    (fun c => exists (Σ' : rts RT) (val : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pv, pv + 4)] m m'
          /\ rw_cells asegs m' pv [C4 (Z_to_bv 64 val)] /\ 0 <= val < 256) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - 1 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition kernelCreateFromPix_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (cv : cmapv),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 2 -> a2 = Z_to_bv 64 2 ->
  pix_obj (rt_live RT Σ) m pix v cv -> p_data v <> 0 ->
  lenv RT Σ m sp lo (LSTK 5) -> lres RT Σ 2 (p_h v + 2) (2 ^ 30) ->
  (p_d v = 8 -> sec_bytes (rt_live RT Σ) + 8 * p_h v + 4 * (p_w v * p_h v) <= SEC_BYTES) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_kernelCreateFromPix m)))
    (fun c => exists (Σ' : rts RT) (kel : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 kel) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix_obj (rt_live RT Σ') m' pix v cv
          /\ (kel = 0 \/ exists data rows, p_d v = 8 /\ kel_obj (rt_live RT Σ') m' kel (p_h v) (p_w v) 2 2 data rows
                                         /\ rt_live RT Σ' = km_live kel data (p_h v) (p_w v) rows (rt_live RT Σ))) c
       /\ (kel = 0 -> rt_live RT Σ' = rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 2 ^ 30 <= rt_credit RT Σ').
(* [comment removed for export] *)
Definition e_km_fuzz : Z := 0x8cc30.
Definition KM_FUZZ_LIVE : Z := 20032.
Definition KM_FUZZ_SECB : Z := 3 * 2^27.
Definition km_fuzz_one_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d : Z) (bs : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 (Z.of_nat (length bs)) -> tp = Z_to_bv 64 TP_A -> bv_unsigned ra = RA_TOP ->
  0 < d -> Z.of_nat (length bs) < 2^26 -> bytes_at asegs m d bs ->
  ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n /\ d mod 8 = 0) \/ bs = []) ->
  rt_frames RT Σ = [] -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  Z.of_nat (length (rt_live RT Σ)) + KM_FUZZ_LIVE <= LIVE_MAX -> FUZZ_COST <= rt_credit RT Σ ->
  sec_bytes (rt_live RT Σ) + KM_FUZZ_SECB <= SEC_BYTES ->
  (bv_unsigned s0 < bv_unsigned sp \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0) ->
  LIB m -> io_ssp m -> ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + FUZZ_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= rt_sp0 RT Σ ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_km_fuzz m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) LIB_FP m m' /\ LIB m') c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = [] /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - FUZZ_COST <= rt_credit RT Σ').
End KmIface.
