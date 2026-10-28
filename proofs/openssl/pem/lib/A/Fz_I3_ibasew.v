(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Malloc Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout PLayout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_mkit Fz_G_kit Fz_ckit Fz_env Fz_M_malloc Fz_M_zalloc Fz_M_locknew Fz_W5_icb Th_errno Th_tsd Th_key Th_once Th_mutex Fz_T_local Fz_T_initthread Fz_T_master1 Fz_G_OPENSSL_cpuid_setup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation TP_A := (0xba3ef0)%Z (only parsing).
Notation DTOR_KEY := (0x5a9f20)%Z (only parsing).
Notation DTOR_FN := (0x1f3fb8)%Z (only parsing).

Definition e_ibase : Z := 0x1f3b08.
Definition SITE_ib_lk1 : Z := 0x1f3b24.         (* [comment removed for export] *)
Definition SITE_ib_lk2 : Z := 0x1f3b38.         (* [comment removed for export] *)
Definition SITE_ib_cpu : Z := 0x1f3b48.         (* [comment removed for export] *)
Definition SITE_ib_ith : Z := 0x1f3b4c.         (* [comment removed for export] *)
Definition SITE_ib_itl : Z := 0x1f3b60.         (* [comment removed for export] *)
Definition e_init_thread : Z := 0x1f3f80.
Definition e_init_local : Z := 0x1f6134.
Definition G_IC_OPTS_LOCK : Z := 0xb9f220.      (* [comment removed for export] *)
Definition G_IC_INIT_LOCK : Z := 0xb9f240.      (* [comment removed for export] *)
Definition G_IC_IICL_KEY : Z := 0xb9f260.       (* [comment removed for export] *)
Definition G_IC_BASE_INITED : Z := 0xb9f1c0.    (* [comment removed for export] *)
Definition IB_S2 : Z := 0xb9eb24.               (* [comment removed for export] *)
Definition IB_S1 : Z := 0xb9eb2c.               (* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ib_w0 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp <= 2^47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists m' : mem,
       ms = MS (mkR (Z_to_bv 64 SITE_ib_lk1) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_lock_new) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ rw_cells asegs m' (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] /\ stk asegs m' lo (bv_unsigned sp + -32))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_ibase) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO0 LO HTOP MI. unfold e_ibase, SITE_ib_lk1, e_lock_new in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  th_frame 32%nat [8; 8; 8; 8]%nat ST.
  do 5 zstep. zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption| assumption].
Qed.

(* [comment removed for export] *)
Lemma ib_w1 : forall sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (lo p1 : Z) (o1 : word),
  0 < p1 < 2^64 -> rw_cells asegs m G_IC_OPTS_LOCK [C8 o1] -> img_untouched m ->
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2^47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists m' : mem,
       ms = MS (mkR (Z_to_bv 64 SITE_ib_lk2) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 IB_S1) (Z_to_bv 64 p1) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 IB_S2) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_lock_new) fc None m' (seg_rom asegs)
       /\ munch [(G_IC_OPTS_LOCK, G_IC_OPTS_LOCK + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ rw_cells asegs m' G_IC_OPTS_LOCK [C8 (Z_to_bv 64 p1)] /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR (Z_to_bv 64 SITE_ib_lk1) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 SITE_ib_lk1)) fc None m (seg_rom asegs)).
Proof.
  intros until o1. intros HP1 OLC UT ST LO0 LO HTOP MI. unfold SITE_ib_lk1, SITE_ib_lk2, e_lock_new, G_IC_OPTS_LOCK, IB_S1, IB_S2 in *.
  rewrite (ret_pc_even 0x1f3b24) by lia.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  pose proof (munch_refl [(0xb9f220, 0xb9f220 + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  assert (EU1 : bv_unsigned (Z_to_bv 64 p1) = p1) by (apply unsigned_lit; lia).
  zstep. zstep. zstep. zstep. if_false. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption| assumption].
Qed.

(* [comment removed for export] *)
Lemma ib_w2 : forall sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (lo p2 : Z) (o2 : word),
  0 < p2 < 2^64 -> rw_cells asegs m G_IC_INIT_LOCK [C8 o2] -> img_untouched m ->
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2^47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (ra' : word) (m' : mem),
       ms = MS (mkR ra' sp gp tp t0 t1 t2 s0 (Z_to_bv 64 IB_S1) (Z_to_bv 64 p2) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 IB_S2) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_OPENSSL_cpuid_setup) fc None m' (seg_rom asegs) /\ bv_unsigned ra' = SITE_ib_cpu
       /\ munch [(G_IC_INIT_LOCK, G_IC_INIT_LOCK + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ rw_cells asegs m' G_IC_INIT_LOCK [C8 (Z_to_bv 64 p2)] /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR (Z_to_bv 64 SITE_ib_lk2) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 IB_S1) (Z_to_bv 64 p2) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 IB_S2) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 SITE_ib_lk2)) fc None m (seg_rom asegs)).
Proof.
  intros until o2. intros HP2 ILC UT ST LO0 LO HTOP MI. unfold SITE_ib_lk2, SITE_ib_cpu, e_OPENSSL_cpuid_setup, G_IC_INIT_LOCK, IB_S1, IB_S2 in *.
  rewrite (ret_pc_even 0x1f3b38) by lia.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  pose proof (munch_refl [(0xb9f240, 0xb9f240 + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  assert (EU2 : bv_unsigned (Z_to_bv 64 p2) = p2) by (apply unsigned_lit; lia).
  zstep. zstep. if_false. zstep.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|]. split; [apply unsigned_lit; lia|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption| assumption].
Qed.
(* [comment removed for export] *)
Definition init_thread_main_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo nk j : Z) (sh kold w : word),
    tp = Z_to_bv 64 TP_A ->
    rw_cells asegs m DTOR_KEY [C4 kold] ->
    ro_cells asegs m (TP_A + -88) [C8 (Z_to_bv 64 TSD_MAIN)] ->
    rw_cells asegs m NEXT_KEY [C4 (Z_to_bv 64 nk)] -> 0 <= nk < 128 ->
    rw_cells asegs m KEY_LOCK [C4 z64; C4 z64; C4 sh] ->
    rw_cells asegs m (KEYS + 8 * j) [C8 z64] ->
    ro_cells asegs m (KEYS + 8 * nk) [C8 w] ->
    ((j = nk /\ w = z64) \/ (j = (nk + 1) mod 128 /\ bv_unsigned w <> 0)) ->
    stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 128 -> bv_unsigned sp <= 2 ^ 47 ->
    mem_inv asegs m ->
    evt asegs (fun ms' => exists (t0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom asegs)
                 /\ munch [(bv_unsigned sp - 128, bv_unsigned sp); (DTOR_KEY, DTOR_KEY + 4); (NEXT_KEY, NEXT_KEY + 12); (KEYS + 8 * j, KEYS + 8 * j + 8)] m m'
                 /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ stk asegs m' lo (bv_unsigned sp)
                 /\ rw_cells asegs m' DTOR_KEY [C4 (Z_to_bv 64 j)]
                 /\ rw_cells asegs m' NEXT_KEY [C4 (Z_to_bv 64 j)]
                 /\ rw_cells asegs m' KEY_LOCK [C4 z64; C4 z64; C4 sh]
                 /\ rw_cells asegs m' (KEYS + 8 * j) [C8 (Z_to_bv 64 DTOR_FN)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_init_thread) fc None m (seg_rom asegs)).

Theorem init_thread_main_proof : init_thread_main_stmt.
Proof.
  unfold init_thread_main_stmt, e_init_thread. intros until w. intros -> KC TC NK HNK KL KJ PROBE CASE ST LO0 LO HTOP MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (HJ : 0 <= j < 128) by (destruct CASE as [[-> _] | [-> _]]; [lia | apply Z.mod_pos_bound; lia]).
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (DTOR_KEY, DTOR_KEY + 4); (NEXT_KEY, NEXT_KEY + 12); (KEYS + 8 * j, KEYS + 8 * j + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  th_frame 16%nat [8; 8]%nat ST.
  do 9 ths.
  pose proof init_local_main_proof as ILM. unfold init_local_main_stmt in ILM.
  tcall (ILM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo nk j sh kold w).
  all: try first [eassumption | reflexivity | rewrite unsigned_lit by lia; lia | lia].
  clear ILM. cbv beta delta [mkR].
  do 5 ths.
  th_release FR (bv_unsigned sp).
  change (if bv_eqb (Z_to_bv 64 DTOR_FN) (Z_to_bv 64 0) then Z_to_bv 64 NODTOR else Z_to_bv 64 DTOR_FN) with (Z_to_bv 64 DTOR_FN) in POST.
  finish.
Qed.
(* [comment removed for export] *)
Lemma ib_w3 : forall sp gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (rax rav s0v s1v s2v : word) (F : bvmap 5 word) fc (m : mem)
    (lo nk j1 j2 : Z) (sh kold1 kold2 w r0 : word) (b0 : byte),
  rw_cells asegs m DTOR_KEY [C4 kold1] -> rw_cells asegs m G_IC_IICL_KEY [C4 kold2] ->
  ro_cells asegs m (TP_A + -88) [C8 (Z_to_bv 64 TSD_MAIN)] ->
  rw_cells asegs m NEXT_KEY [C4 (Z_to_bv 64 nk)] -> 0 <= nk < 128 -> rw_cells asegs m KEY_LOCK [C4 z64; C4 z64; C4 sh] ->
  rw_cells asegs m (KEYS + 8 * j1) [C8 z64] -> ro_cells asegs m (KEYS + 8 * nk) [C8 w] -> ((j1 = nk /\ w = z64) \/ (j1 = (nk + 1) mod 128 /\ bv_unsigned w <> 0)) ->
  j2 = (j1 + 1) mod 128 -> rw_cells asegs m (KEYS + 8 * j2) [C8 z64] ->
  rw_cells asegs m G_IC_BASE_INITED [C1 b0] -> rw_cells asegs m G_IC_BASE_RET [C4 r0] ->
  rw_cells asegs m (bv_unsigned sp + -32) [C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk asegs m lo (bv_unsigned sp + -32) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 160 -> bv_unsigned sp <= 2^47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
       ms = MS (mkR rav sp gp (Z_to_bv 64 TP_A) t0' t1' t2' s0v s1v (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc rav) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp - 160, bv_unsigned sp); (DTOR_KEY, DTOR_KEY + 4); (G_IC_IICL_KEY, G_IC_IICL_KEY + 4); (NEXT_KEY, NEXT_KEY + 12);
                 (KEYS + 8 * j1, KEYS + 8 * j1 + 8); (KEYS + 8 * j2, KEYS + 8 * j2 + 8);
                 (G_IC_BASE_INITED, G_IC_BASE_INITED + 1); (G_IC_BASE_RET, G_IC_BASE_RET + 4)] m m'
       /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
       /\ rw_cells asegs m' DTOR_KEY [C4 (Z_to_bv 64 j1)] /\ rw_cells asegs m' G_IC_IICL_KEY [C4 (Z_to_bv 64 j2)]
       /\ rw_cells asegs m' NEXT_KEY [C4 (Z_to_bv 64 j2)] /\ rw_cells asegs m' KEY_LOCK [C4 z64; C4 z64; C4 sh]
       /\ rw_cells asegs m' (KEYS + 8 * j1) [C8 (Z_to_bv 64 DTOR_FN)] /\ rw_cells asegs m' (KEYS + 8 * j2) [C8 (Z_to_bv 64 NODTOR)]
       /\ rw_cells asegs m' G_IC_BASE_INITED [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m' G_IC_BASE_RET [C4 (Z_to_bv 64 1)])
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp (Z_to_bv 64 IB_S1) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 IB_S2) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (ret_pc (Z_to_bv 64 SITE_ib_cpu)) fc None m (seg_rom asegs)).
Proof.
  intros until b0. intros DK IK TC NK HNK KL KJ1 PROBE CASE EJ2 KJ2 BI BR FR ST LO0 LO HTOP MI.
  unfold SITE_ib_cpu, G_IC_IICL_KEY, G_IC_BASE_INITED, G_IC_BASE_RET, IB_S1, IB_S2 in *. rewrite (ret_pc_even 0x1f3b48) by lia.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  assert (HJ1 : 0 <= j1 < 128) by (destruct CASE as [[-> _] | [-> _]]; [lia | apply Z.mod_pos_bound; lia]).
  assert (HJ2 : 0 <= j2 < 128 /\ j2 <> j1) by (subst j2; split; [apply Z.mod_pos_bound; lia | Z.div_mod_to_equations; lia]).
  pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp); (DTOR_KEY, DTOR_KEY + 4); (0xb9f260, 0xb9f260 + 4); (NEXT_KEY, NEXT_KEY + 12);
                 (KEYS + 8 * j1, KEYS + 8 * j1 + 8); (KEYS + 8 * j2, KEYS + 8 * j2 + 8); (0xb9f1c0, 0xb9f1c0 + 1); (0xb9f2e0, 0xb9f2e0 + 4)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  cl_eu (bv_unsigned sp) (-32) EU1.
  zstep.
  pose proof init_thread_main_proof as ITH. unfold init_thread_main_stmt, e_init_thread in ITH.
  tcall (ITH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo nk j1 sh kold1 w).
  all: try first [eassumption | reflexivity | lia].
  clear ITH. cbv beta delta [mkR].
  zstep. th_if_lit. zstep. zstep. zstep. zstep.
  pose proof init_local_main_proof as ITL. unfold init_local_main_stmt in ITL.
  tcall (ITL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo j1 j2 sh kold2 (Z_to_bv 64 DTOR_FN)).
  all: try first [eassumption | reflexivity | rewrite unsigned_lit by lia; lia | lia | right; split; [exact EJ2 | rewrite unsigned_lit by lia; lia]].
  { exact (proj1 POST). }
  clear ITL. cbv beta delta [mkR].
  zstep. th_if_lit. zstep. zstep. (zstep; lfix). zstep. zstep. (zstep; lfix).
  do 4 zstep. th_release FR (bv_unsigned sp). zstep. zstep.
  change (if bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0) then Z_to_bv 64 NODTOR else Z_to_bv 64 0) with (Z_to_bv 64 NODTOR) in POST0.
  apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  repeat match goal with |- _ /\ _ => split end; eassumption.
Qed.
