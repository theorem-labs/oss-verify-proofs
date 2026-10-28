(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HXB Require Export HxaIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition e_fuzz : Z := 0x1ee35c.             (* [comment removed for export] *)

(* [comment removed for export] *)
Definition LIB_FP : list (Z * Z) :=
  [(0x5e6660, 0x5e7140); (0xbd6050, 0xbd6051); (0xbd6080, 0xbda540); (0xbdadba, 0xbdadbb); (0xbdadf0, 0xbdadf8); (0xbfbdb8, 0xbfc1f8); (0xbfc200, 0xbfc5f8)].
Definition LIB_FPE : list (Z * Z) := (0xbdadac, 0xbdadb0) :: LIB_FP.

(* [comment removed for export] *)
Definition lib_startA (m : mem) : Prop := lib_pristineA m /\ rw_cells bsegs m 0xbd6050 [C1 (Z_to_bv 8 0)].

(* [comment removed for export] *)
Definition OSSL_BASE_INITED : Z := 0xbd65e0.
Definition OSSL_DO_GLOBAL_CLEANUP : Z := 0xbd6600.
Definition lib_exit_cells (m : mem) : Prop :=
  exists b0 : byte, rw_cells bsegs m OSSL_BASE_INITED [C1 b0] /\ rw_cells bsegs m OSSL_DO_GLOBAL_CLEANUP [C1 (Z_to_bv 8 0)].

(* [comment removed for export] *)
Definition FUZZ_COST : Z := 2^31.
(* [comment removed for export] *)
Definition FUZZ_LIVE : Z := 32.
(* [comment removed for export] *)
Definition FUZZ_STACK : Z := 0x20000.

Section LibIface.
Variable RT : rt_sig.
(* [comment removed for export] *)
Variable LIBA : rts RT -> list (Z * Z) -> mem -> Prop.

(* [comment removed for export] *)
Definition fuzz_one_cps' : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d : Z) (bs : list byte) (lo : Z) (LW CL : list (Z * Z)),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 (Z.of_nat (length bs)) -> tp = Z_to_bv 64 0xbdae50 ->
  0 < d < 2^64 -> d <= lo ->          (* [comment removed for export] *)
  Z.of_nat (length bs) < 2^26 -> bytes_at bsegs m d bs ->
  ((exists p n, In (p, n) CL /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ bs = []) ->
  Permutation (rt_live RT Σ) (LW ++ CL) -> LIBA Σ LW m ->
  rt_frames RT Σ = [] -> (forall p n, In (p, n) CL -> 0 < n) ->
  Z.of_nat (length (rt_live RT Σ)) + FUZZ_LIVE <= LIVE_MAX -> FUZZ_COST <= rt_credit RT Σ ->
  (bv_unsigned s0 <= lo \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0) ->          (* [comment removed for export] *)
  ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + FUZZ_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= rt_sp0 RT Σ ->
  cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_fuzz m)))
    (fun c => exists (Σ' : rts RT) (LW' : list (Z * Z)),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp CL [] (bv_unsigned sp) LIB_FPE m m' /\ LIBA Σ' LW' m') c
       /\ Permutation (rt_live RT Σ') (LW' ++ CL) /\ rt_frames RT Σ' = [] /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - FUZZ_COST <= rt_credit RT Σ'
       /\ Z.of_nat (length (rt_live RT Σ')) <= Z.of_nat (length (rt_live RT Σ)) + FUZZ_LIVE).

(* [comment removed for export] *)
Definition liba_frame : Prop :=
  forall (Σ Σ' : rts RT) (LW : list (Z * Z)) (m m' : mem), LIBA Σ LW m ->
    (forall a : word, in_ranges LIB_FP (bv_unsigned a) \/ in_live LW (bv_unsigned a) -> m' a = m a) -> LIBA Σ' LW m'.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition liba_exit : Prop := forall (Σ : rts RT) (LW : list (Z * Z)) (m : mem), LIBA Σ LW m -> lib_exit_cells m.
(* [comment removed for export] *)
Definition liba_pos : Prop := forall (Σ : rts RT) (LW : list (Z * Z)) (m : mem), LIBA Σ LW m -> forall p n, In (p, n) LW -> 0 < n.

End LibIface.
