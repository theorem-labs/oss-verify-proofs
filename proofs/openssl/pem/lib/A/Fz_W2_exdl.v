(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_mkit Fz_env Th_mutex Th_once Th_tsd Fz_T_once Fz_T_local Fz_T_lock Fz_M_free Fz_W1_defs Fz_W3_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Notation z64 := (Z_to_bv 64 0) (only parsing).
(* [comment removed for export] *)
Definition DC_INITED : Z := 0xb9f560.       (* [comment removed for export] *)
Definition DC_CTX : Z := 0xb9f580.          (* [comment removed for export] *)
Definition DC_KEY : Z := 0xb9f720.          (* [comment removed for export] *)
Definition DC_ONCE1 : Z := 0xb9f740.        (* [comment removed for export] *)
Definition DC_RET1 : Z := 0xb9f760.         (* [comment removed for export] *)
Definition DC_ONCE2 : Z := 0xb9f780.        (* [comment removed for export] *)
Definition DC_RET2 : Z := 0xb9f7a0.         (* [comment removed for export] *)
Definition DC_GLOBAL_LOCK : Z := DC_CTX + 8.
Definition DC_IP12 : Z := DC_CTX + 112.     (* [comment removed for export] *)
Definition e_get_default_context : Z := 0x1f76c0.
Definition e_get_ex_data_global : Z := 0x1f7a20.
Definition e_get_and_lock : Z := 0x1f83bc.
Definition e_sk_num : Z := 0x1fbb44.
Definition e_new_ex_data : Z := 0x1f8e64.   (* [comment removed for export] *)
Definition e_free_ex_data : Z := 0x1f9620.  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition T_defctx_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo T kd sb : Z),
    ro_cells asegs m DC_INITED [C1 (Z_to_bv 8 1)] ->
    ro_cells asegs m DC_KEY [C4 (Z_to_bv 64 kd)] -> 0 <= kd < 128 ->
    ro_cells asegs m (DC_KEY / 8 + 2147450880) [C1 (Z_to_bv 8 sb)] -> (sb = 0 \/ sb = 4) ->
    img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
    ro_cells asegs m DC_ONCE1 [C4 (Z_to_bv 64 2)] -> ro_cells asegs m DC_RET1 [C4 (Z_to_bv 64 1)] ->
    ro_cells asegs m DC_ONCE2 [C4 (Z_to_bv 64 2)] -> ro_cells asegs m DC_RET2 [C4 (Z_to_bv 64 1)] ->
    ro_cells asegs m (bv_unsigned tp + -88) [C8 (Z_to_bv 64 T)] -> 88 <= bv_unsigned tp -> bv_unsigned tp <= lo -> 0 <= T ->
    ro_cells asegs m (T + 8 * kd) [C8 z64] -> T + 8 * kd + 8 <= lo ->
    stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp <= 2 ^ 47 ->
    mem_inv asegs m ->
    evt asegs (fun ms' => exists (t1' a1' a2' a3' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1' t2 s0 s1 (Z_to_bv 64 DC_CTX) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom asegs)
                 /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ stk asegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_get_default_context) fc None m (seg_rom asegs)).

Theorem T_defctx_proof : T_defctx_stmt.
Proof.
  unfold T_defctx_stmt. intros until sb.
  intros INI KC HK SBC SBV UT SHC O1 R1 O2 R2 TS TP TPLO T0 SLOTC SLO ST GLO LO SPH MI.
  unfold DC_INITED, DC_KEY, DC_ONCE1, DC_RET1, DC_ONCE2, DC_RET2, DC_CTX, e_get_default_context, g_shadow_memory_dynamic_address in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  set (Pk := T + 8 * kd) in *.
  th_frame 16%nat [8; 8]%nat ST.
  do 8 zstep.
  zstep.
  tcall (T_run_once_done_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo).
  all: try (rewrite ?unsigned_lit by lia); try first [eassumption | lia].
  cbv beta delta [mkR].
  zstep. th_if_lit.
  zstep. zstep. zstep. th_if_lit.
  zstep. zstep. zstep. zstep.
  zstep.
  tcall (T_run_once_done_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo).
  all: try (rewrite ?unsigned_lit by lia); try first [eassumption | lia].
  cbv beta delta [mkR].
  zstep. th_if_lit.
  zstep. zstep. zstep. th_if_lit.
  zstep. zstep.
  zstep.
  tcall (T_get_local_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo T kd sb (Z_to_bv 64 0)).
  all: try (rewrite ?unsigned_lit by lia); try first [eassumption | reflexivity | lia].
  all: try (eapply ut_munch; [exact UT | eassumption | exact HWU]).
  cbv beta delta [mkR].
  zstep. th_if_lit.
  zstep. zstep. zstep. zstep. zstep. zstep.
  zstep. zstep. zstep. th_release FR (bv_unsigned sp). zstep.
  finish.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition T_exg_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo T kd sb : Z),
    ro_cells asegs m DC_INITED [C1 (Z_to_bv 8 1)] ->
    ro_cells asegs m DC_KEY [C4 (Z_to_bv 64 kd)] -> 0 <= kd < 128 ->
    ro_cells asegs m (DC_KEY / 8 + 2147450880) [C1 (Z_to_bv 8 sb)] -> (sb = 0 \/ sb = 4) ->
    img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
    ro_cells asegs m DC_ONCE1 [C4 (Z_to_bv 64 2)] -> ro_cells asegs m DC_RET1 [C4 (Z_to_bv 64 1)] ->
    ro_cells asegs m DC_ONCE2 [C4 (Z_to_bv 64 2)] -> ro_cells asegs m DC_RET2 [C4 (Z_to_bv 64 1)] ->
    ro_cells asegs m (bv_unsigned tp + -88) [C8 (Z_to_bv 64 T)] -> 88 <= bv_unsigned tp -> bv_unsigned tp <= lo -> 0 <= T ->
    ro_cells asegs m (T + 8 * kd) [C8 z64] -> T + 8 * kd + 8 <= lo ->
    stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 48 -> bv_unsigned sp <= 2 ^ 47 ->
    mem_inv asegs m ->
    evt asegs (fun ms' => exists (t1' a1' a2' a3' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1' t2 s0 s1 (Z_to_bv 64 DC_GLOBAL_LOCK) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom asegs)
                 /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ stk asegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_get_ex_data_global) fc None m (seg_rom asegs)).

Theorem T_exg_proof : T_exg_stmt.
Proof.
  unfold T_exg_stmt. intros until sb.
  intros INI KC HK SBC SBV UT SHC O1 R1 O2 R2 TS TP TPLO T0 SLOTC SLO ST GLO LO SPH MI.
  unfold DC_GLOBAL_LOCK, DC_INITED, DC_KEY, DC_ONCE1, DC_RET1, DC_ONCE2, DC_RET2, DC_CTX, e_get_ex_data_global, g_shadow_memory_dynamic_address in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  set (Pk := T + 8 * kd) in *.
  th_frame 16%nat [8; 8]%nat ST.
  do 4 zstep. zstep. th_if_lit.
  zstep.
  pose proof T_defctx_proof as X. unfold T_defctx_stmt, DC_INITED, DC_KEY, DC_ONCE1, DC_RET1, DC_ONCE2, DC_RET2, DC_CTX, e_get_default_context, g_shadow_memory_dynamic_address in X.
  tcall (X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo T kd sb).
  all: try (rewrite ?unsigned_lit by lia); try first [eassumption | lia].
  all: try (eapply ut_munch; [exact UT | eassumption | exact HWU]).
  clear X. cbv beta delta [mkR].
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.
  zstep. zstep. zstep. th_release FR (bv_unsigned sp). zstep.
  finish.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition T_gal_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo LK : Z),
    ro_cells asegs m DC_GLOBAL_LOCK [C8 (Z_to_bv 64 LK)] -> 0x10007fff8000 <= LK -> LK mod 16 = 0 -> LK + 40 <= lo ->
    rw_cells asegs m LK (mutex_cells z64 z64) ->
    ro_cells asegs m (DC_GLOBAL_LOCK / 8 + 2147450880) [C1 (Z_to_bv 8 0)] ->
    img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
    stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 48 -> bv_unsigned sp <= 2 ^ 47 ->
    mem_inv asegs m ->
    evt asegs (fun ms' => exists (a1' a2' a3' a4' a5' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DC_IP12) a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom asegs)
                 /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (LK + 4, LK + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ stk asegs m' lo (bv_unsigned sp)
                 /\ rw_cells asegs m' LK (mutex_cells z64 (Z_to_bv 64 16)))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DC_GLOBAL_LOCK) (Z_to_bv 64 12) (Z_to_bv 64 1) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_get_and_lock) fc None m (seg_rom asegs)).

Theorem T_gal_proof : T_gal_stmt.
Proof.
  unfold T_gal_stmt. intros until LK.
  intros GL LK0 LKAL SEP MC GSH UT SHC ST GLO LO SPH MI.
  unfold DC_IP12, DC_GLOBAL_LOCK, DC_CTX, e_get_and_lock, g_shadow_memory_dynamic_address, SHB in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (rw_cells_bound _ _ _ _ MC) as LKB. cbn [cells_size mutex_cells csize Nat.add] in LKB.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (LK + 4, LK + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  replace ((12187008 + 8) / 8 + 2147450880) with 2148974257 in GSH by reflexivity.
  change (12187008 + 8) with 12187016 in *. change (12187008 + 112) with 12187120.
  unfold mutex_cells in MC.
  th_frame 32%nat [8; 8; 8; 8]%nat ST.
  do 6 zstep.
  zstep. zstep. zstep. th_if_lit.
  (* [comment removed for export] *)
  zstep.
  zstep. zstep. zstep. zstep. zstep. zstep.
  cbv beta. zstep. th_if_lit.
  zstep. zstep.
  if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  zstep. th_if_lit.
  zstep.
  pose proof T_read_lock_proof as X. unfold T_lock_stmt, mutex_cells in X.
  tcall (X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo).
  all: try (rewrite ?unsigned_lit by lia); try first [eassumption | lia].
  clear X. cbv beta delta [mkR].
  (* [comment removed for export] *)
  zstep. th_if_lit.
  zstep. zstep. zstep.
  do 5 zstep. th_release FR (bv_unsigned sp). zstep.
  finish.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition T_sknum_null_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
    stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
    evt asegs (fun ms' => exists (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom asegs)
                 /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ stk asegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_sk_num) fc None m (seg_rom asegs)).

Theorem T_sknum_null_proof : T_sknum_null_stmt.
Proof.
  unfold T_sknum_null_stmt, e_sk_num. intros until lo. intros ST GLO LO SPH MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  th_frame 16%nat [8; 8]%nat ST.
  do 4 zstep. zstep. th_if_lit. zstep.
  zstep. zstep. zstep. th_release FR (bv_unsigned sp). zstep.
  finish.
Qed.
Definition e_sk_free : Z := 0x1fa8d4.
(* [comment removed for export] *)
Definition T_skfree_null_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
    stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
    evt asegs (fun ms' => exists (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom asegs)
                 /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ stk asegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_sk_free) fc None m (seg_rom asegs)).

Theorem T_skfree_null_proof : T_skfree_null_stmt.
Proof.
  unfold T_skfree_null_stmt, e_sk_free. intros until lo. intros ST GLO LO SPH MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  th_frame 32%nat [8; 8; 8; 8]%nat ST.
  do 6 zstep. zstep. th_if_lit.
  zstep. zstep. zstep. zstep. zstep. th_release FR (bv_unsigned sp). zstep.
  finish.
Qed.
