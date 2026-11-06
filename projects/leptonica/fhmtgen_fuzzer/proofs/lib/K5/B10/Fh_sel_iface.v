(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec Image.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit D_iface D_defs D_libiface Lept_iface Gm_iface Fh_iface LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition HM_DIMS : list (Z * Z * Z * Z) :=
  [(3,3,1,1); (2,3,0,1); (2,3,1,1); (3,2,1,0); (3,2,1,1); (13,6,6,2); (4,4,1,1); (4,4,1,2); (4,4,2,1); (4,4,2,2)].

(* [comment removed for export] *)
Record selv : Type := mkSelv { s_sy : Z; s_sx : Z; s_cy : Z; s_cx : Z; s_data : Z; s_name : Z; s_rows : list Z }.
Definition sel_cells (v : selv) : list cell :=
  [C4 (Z_to_bv 64 (s_sy v)); C4 (Z_to_bv 64 (s_sx v)); C4 (Z_to_bv 64 (s_cy v)); C4 (Z_to_bv 64 (s_cx v));
   C8 (Z_to_bv 64 (s_data v)); C8 (Z_to_bv 64 (s_name v))].
(* [comment removed for export] *)
Definition sel_body (live : list (Z * Z)) (m : mem) (sel : Z) (v : selv) : Prop :=
  rw_cells asegs m sel (sel_cells v) /\ chunk live sel 32
  /\ 0 < s_sy v <= 13 /\ 0 < s_sx v <= 6 /\ Z.of_nat (length (s_rows v)) = s_sy v
  /\ rw_cells asegs m (s_data v) (map (fun r => C8 (Z_to_bv 64 r)) (s_rows v)) /\ chunk live (s_data v) (8 * s_sy v)
  /\ Forall (fun r => chunk live r (4 * s_sx v)) (s_rows v)
  /\ List.NoDup (sel :: s_data v :: s_rows v).
Definition sel_obj (live : list (Z * Z)) (m : mem) (sel : Z) (v : selv) (nm : list byte) : Prop :=
  sel_body live m sel v /\ bytes_at asegs m (s_name v) nm /\ chunk live (s_name v) 8 /\ length nm = 8%nat.

(* [comment removed for export] *)
Definition sela_cells (n arr : Z) : list cell := [C4 (Z_to_bv 64 n); C4 (Z_to_bv 64 50); C8 (Z_to_bv 64 arr)].
Definition sela_obj (live : list (Z * Z)) (m : mem) (sela arr : Z) (sels : list (Z * selv * list byte)) : Prop :=
  rw_cells asegs m sela (sela_cells (Z.of_nat (length sels)) arr) /\ chunk live sela 16 /\ chunk live arr 400
  /\ (length sels <= 50)%nat
  /\ rw_cells asegs m arr (map (fun e => C8 (Z_to_bv 64 (fst (fst e)))) sels ++ repeat (C8 (Z_to_bv 64 0)) (50 - length sels))
  /\ Forall (fun e => sel_obj live m (fst (fst e)) (snd (fst e)) (snd e)) sels.

(* [comment removed for export] *)
Definition sel_live (sel : Z) (v : selv) : list (Z * Z) :=
  (s_name v, 8) :: rev (map (fun r => (r, 4 * s_sx v)) (s_rows v)) ++ [(s_data v, 8 * s_sy v); (sel, 32)].
Definition sela_live (sela arr : Z) (sels : list (Z * selv * list byte)) : list (Z * Z) :=
  flat_map (fun e => sel_live (fst (fst e)) (snd (fst e))) (rev sels) ++ [(arr, 400); (sela, 16)].
(* [comment removed for export] *)
Definition sel_frees (sel : Z) (v : selv) : list Z := s_rows v ++ [s_data v; s_name v; sel].
Definition sela_frees (sela arr : Z) (sels : list (Z * selv * list byte)) : list Z :=
  flat_map (fun e => sel_frees (fst (fst e)) (snd (fst e))) sels ++ [arr; sela].
Definition live_remove_all (ps : list Z) (live : list (Z * Z)) : list (Z * Z) := fold_left (fun l p => live_remove p l) ps live.

(* [comment removed for export] *)
Definition hm_sels_ok (sels : list (Z * selv * list byte)) : Prop :=
  length sels = 10%nat
  /\ forall i, (i < 10)%nat ->
       let e := nth i sels (0, mkSelv 0 0 0 0 0 0 [], []) in let d := nth i HM_DIMS (0, 0, 0, 0) in
       s_sy (snd (fst e)) = fst (fst (fst d)) /\ s_sx (snd (fst e)) = snd (fst (fst d)) /\ snd e = hm_name i.


Section FhSelIface.
Variable RT : rt_sig.

Definition s0_nolink (sp s0 : word) : Prop :=
  bv_unsigned s0 + 4096 <= bv_unsigned sp \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition stringNew_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (src : Z) (str : list byte),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 src -> 0x10000 <= src -> src + 8 <= SEGTOP_A -> src mod 8 = 0 -> length str = 7%nat ->
  ro_bytes asegs src (str ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str -> In (src, 8) ACC_LITS ->
  lenv RT Σ m sp lo (LSTK 2) -> lres RT Σ 0 1 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_stringNew m)))
    (fun c => exists (Σ' : rts RT) (dest : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 dest) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ bytes_at asegs m' dest (str ++ [Z_to_bv 8 0])) c
       /\ rt_live RT Σ' = (dest, 8) :: rt_live RT Σ /\ 0 < dest /\ dest mod 16 = 0
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition selaCreate_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A -> a0 = Z_to_bv 64 0 ->
  s0_nolink sp s0 ->   (* [comment removed for export] *)
  lenv RT Σ m sp lo (LSTK 1) -> lres RT Σ 0 2 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_selaCreate m)))
    (fun c => exists (Σ' : rts RT) (sela arr : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 sela) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ sela_obj (rt_live RT Σ') m' sela arr []) c
       /\ rt_live RT Σ' = sela_live sela arr [] ++ rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition selCreate_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (sy sx : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 sy -> a1 = Z_to_bv 64 sx -> a2 = Z_to_bv 64 0 -> 0 < sy <= 13 -> 0 < sx <= 6 -> s0_nolink sp s0 ->
  lenv RT Σ m sp lo (LSTK 1) -> lres RT Σ 0 (sy + 2) 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_selCreate m)))
    (fun c => exists (Σ' : rts RT) (sel : Z) (v : selv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 sel) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ sel_body (rt_live RT Σ') m' sel v) c
       /\ s_sy v = sy /\ s_sx v = sx /\ s_cy v = 0 /\ s_cx v = 0 /\ s_name v = 0
       /\ rt_live RT Σ' = tl (sel_live sel v) ++ rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition selCreateBrick_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (sy sx cy cx ty : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 sy -> a1 = Z_to_bv 64 sx -> a2 = Z_to_bv 64 cy -> a3 = Z_to_bv 64 cx -> a4 = Z_to_bv 64 ty ->
  0 < sy <= 13 -> 0 < sx <= 6 -> 0 <= cy < sy -> 0 <= cx < sx -> 0 <= ty <= 2 ->
  lenv RT Σ m sp lo (LSTK 2) -> lres RT Σ 0 (sy + 2) 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_selCreateBrick m)))
    (fun c => exists (Σ' : rts RT) (sel : Z) (v : selv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 sel) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ sel_body (rt_live RT Σ') m' sel v) c
       /\ s_sy v = sy /\ s_sx v = sx /\ s_cy v = cy /\ s_cx v = cx /\ s_name v = 0
       /\ rt_live RT Σ' = tl (sel_live sel v) ++ rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition selSetElement_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (sel : Z) (v : selv) (row col ty : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 sel -> a1 = Z_to_bv 64 row -> a2 = Z_to_bv 64 col -> a3 = Z_to_bv 64 ty ->
  sel_body (rt_live RT Σ) m sel v -> 0 <= row < s_sy v -> 0 <= col < s_sx v -> 0 <= ty <= 2 ->
  lenv RT Σ m sp lo (LSTK 1) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_selSetElement m)))
    (fun c => exists (rv : word),
       ASTA RT Σ PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost RT Σ Σ m m' sp lo
          /\ keeps RT Σ Σ sp [(nth (Z.to_nat row) (s_rows v) 0, nth (Z.to_nat row) (s_rows v) 0 + 4 * s_sx v)] m m'
          /\ sel_body (rt_live RT Σ) m' sel v) c).

(* [comment removed for export] *)
Definition selaAddSel_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (sela arr sel : Z) (sels : list (Z * selv * list byte)) (v : selv) (i : Z) (live0 : list (Z * Z)),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 sela -> a1 = Z_to_bv 64 sel -> a2 = Z_to_bv 64 (HM_NAME_LIT i) -> a3 = Z_to_bv 64 0 -> 0 <= i < 10 ->
  sela_obj (rt_live RT Σ) m sela arr sels -> (length sels < 10)%nat -> sel_body (rt_live RT Σ) m sel v -> s_name v = 0 ->
  rt_live RT Σ = tl (sel_live sel v) ++ sela_live sela arr sels ++ live0 ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 0 1 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_selaAddSel m)))
    (fun c => exists (Σ' : rts RT) (nmp : Z),
       let v' := mkSelv (s_sy v) (s_sx v) (s_cy v) (s_cx v) (s_data v) nmp (s_rows v) in
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
          /\ lpost RT Σ Σ' m m' sp lo
          /\ keepsL RT (rt_live RT Σ) Σ sp [(sel + 24, sel + 32); (sela, sela + 4); (arr, arr + 400)] m m'
          /\ sela_obj (rt_live RT Σ') m' sela arr (sels ++ [(sel, v', hm_name (Z.to_nat i))])) c
       /\ rt_live RT Σ' = (nmp, 8) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition selaAddHitMiss_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A -> a0 = Z_to_bv 64 0 ->
  lenv RT Σ m sp lo (LSTK 4) -> lres RT Σ 0 74 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_selaAddHitMiss m)))
    (fun c => exists (Σ' : rts RT) (sela arr : Z) (sels : list (Z * selv * list byte)),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 sela) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ sela_obj (rt_live RT Σ') m' sela arr sels) c
       /\ hm_sels_ok sels /\ rt_live RT Σ' = sela_live sela arr sels ++ rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition selDestroy_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pp sel : Z) (v : selv) (nm : list byte) (q qn : Z) (l1 l2 : list (Z * Z)),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pp -> In (q, qn) (live_remove_all (sel_frees sel v) (rt_live RT Σ)) -> q <= pp -> pp + 8 <= q + qn -> pp mod 8 = 0 ->
  rw_cells asegs m pp [C8 (Z_to_bv 64 sel)] -> sel_obj (rt_live RT Σ) m sel v nm ->
  rt_live RT Σ = l1 ++ sel_live sel v ++ l2 -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  lenv RT Σ m sp lo (LSTK 2) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_selDestroy m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pp, pp + 8)] m m'
          /\ rw_cells asegs m' pp [C8 (Z_to_bv 64 0)]) c
       /\ rt_live RT Σ' = live_remove_all (sel_frees sel v) (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition selaDestroy_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pp sela arr : Z) (sels : list (Z * selv * list byte)) (l1 l2 : list (Z * Z)),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pp -> optrL RT (live_remove_all (sela_frees sela arr sels) (rt_live RT Σ)) Σ m pp 8 ->
  rw_cells asegs m pp [C8 (Z_to_bv 64 sela)] -> sela_obj (rt_live RT Σ) m sela arr sels ->
  rt_live RT Σ = l1 ++ sela_live sela arr sels ++ l2 -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  lenv RT Σ m sp lo (LSTK 3) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_selaDestroy m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pp, pp + 8)] m m'
          /\ rw_cells asegs m' pp [C8 (Z_to_bv 64 0)]) c
       /\ rt_live RT Σ' = live_remove_all (sela_frees sela arr sels) (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ <= rt_credit RT Σ').

End FhSelIface.
