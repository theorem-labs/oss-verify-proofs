(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Malloc Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout PLayout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_mkit Fz_G_kit Fz_ckit Fz_env Fz_M_malloc Fz_M_zalloc Fz_G_CRYPTO_calloc Fz_G_ossl_sa_new Th_tsd Th_key Th_once Fz_T_once Fz_T_local Fz_T_sa Fz_T_sa_set Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation zeros n := (repeat (Z_to_bv 8 0) n) (only parsing).
Notation TP_A := (0xba3ef0)%Z (only parsing).
Notation MK_ONCE := (0xb9f500)%Z (only parsing).
Notation MK_KEY := (0xb9f520)%Z (only parsing).
Definition e_slx : Z := 0x1f6804.
Definition SITE_slx_calloc : Z := 0x1f6910.
Definition SITE_slx_sanew : Z := 0x1f68b0.
Definition SLX_FILE : Z := 0x492a0.

(* [comment removed for export] *)
Lemma slx_w0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo T k sb : Z),
  tp = Z_to_bv 64 TP_A ->
  ro_cells asegs m MK_ONCE [C4 (Z_to_bv 64 2)] ->
  ro_cells asegs m MK_KEY [C4 (Z_to_bv 64 k)] -> 0 <= k < 128 ->
  ro_cells asegs m (MK_KEY / 8 + 2147450880) [C1 (Z_to_bv 8 sb)] -> (sb = 0 \/ sb = 4) ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  ro_cells asegs m (TP_A + -88) [C8 (Z_to_bv 64 T)] -> 0 <= T -> T + 8 * k + 8 <= lo ->
  ro_cells asegs m (T + 8 * k) [C8 z64] ->
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 80 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (t1' : word) (j : list byte) (m' : mem),
       ms = MS (mkR (Z_to_bv 64 SITE_slx_calloc) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1' t2 sp a2 (Z_to_bv 64 9) (Z_to_bv 64 8) (Z_to_bv 64 SLX_FILE) (Z_to_bv 64 362) a4 a5 a6 a7
                    z64 (Z_to_bv 64 3) z64 (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_CRYPTO_calloc) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ rw_cells asegs m' (bv_unsigned sp + -64) [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
       /\ stk asegs m' lo (bv_unsigned sp + -64))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 3) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_slx) fc None m (seg_rom asegs)).
Proof.
  intros until sb. intros -> OC KC HK KSB HSB UT SHC TSD T0 TLO SLOT ST LO0 LO HTOP MI.
  unfold e_slx, g_shadow_memory_dynamic_address, SHB, SITE_slx_calloc, SLX_FILE, e_CRYPTO_calloc in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  set (Pk := T + 8 * k) in *.
  th_frame 64%nat [8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  do 9 zstep. zstep. do 3 zstep. do 2 zstep. zstep. th_if_lit. zstep.
  do 4 zstep. zstep.
  tcall (T_run_once_done_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo);
    [exact OC | exact ST | lia | lia | lia | exact MI |].
  cbv delta [mkR].
  do 2 zstep. th_if_lit.
  zstep. th_if_lit.
  do 2 zstep. zstep.
  tcall (T_get_local_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo T k sb (Z_to_bv 64 0));
    [exact KC | exact HK | reflexivity | lia | lia | exact KSB | exact HSB | exact (ut_munch _ m _ UT MU HWU) | exact SHC | exact TSD | lia | lia | exact SLOT | lia | lia
    | eassumption | lia | lia | lia | assumption |].
  cbv delta [mkR].
  zstep. zstep. th_if_lit.
  do 5 zstep. zstep.
  apply evt_done. do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption | assumption].
Qed.

(* [comment removed for export] *)
Lemma slx_w1 : forall (sp gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 val : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo k sb MK : Z) (u : byte) (j : list byte) (rav s0v s1v s2v s3v s4v s5v : word),
  ro_cells asegs m MK_KEY [C4 (Z_to_bv 64 k)] -> 0 <= k < 128 ->
  ro_cells asegs m (MK_KEY / 8 + 2147450880) [C1 (Z_to_bv 8 sb)] -> (sb = 0 \/ sb = 4) ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  ro_cells asegs m (TP_A + -88) [C8 (Z_to_bv 64 TSD_MAIN)] ->
  rw_cells asegs m (TSD_MAIN + 8 * k) [C8 z64] -> rw_cells asegs m (TP_A + -150) [C1 u] ->
  0x10007fff8000 <= MK -> MK mod 8 = 0 -> MK + 72 <= lo -> rw_cells asegs m MK [CB 24 (zeros 24); C8 z64; CB 40 (zeros 40)] -> acc asegs m MK 72 ->
  rw_cells asegs m (bv_unsigned sp + -64) [CB 8 j; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk asegs m lo (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 80 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (a2' a3' : word) (u' : byte) (m' : mem),
       ms = MS (mkR (Z_to_bv 64 SITE_slx_sanew) (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp val z64 (Z_to_bv 64 MK) a2' a3' a4 a5 a6 a7
                    z64 (Z_to_bv 64 (MK + 24)) (Z_to_bv 64 MK) (Z_to_bv 64 (Z.shiftr (MK + 24) 3 + SHB)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_ossl_sa_new) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (TSD_MAIN + 8 * k, TSD_MAIN + 8 * k + 8); (TP_A + -150, TP_A + -149)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ rw_cells asegs m' (bv_unsigned sp + -64) [CB 8 j; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]
       /\ stk asegs m' lo (bv_unsigned sp + -64)
       /\ rw_cells asegs m' (TSD_MAIN + 8 * k) [C8 (Z_to_bv 64 MK)] /\ rw_cells asegs m' (TP_A + -150) [C1 u']
       /\ rw_cells asegs m' MK [CB 24 (zeros 24); C8 z64; CB 40 (zeros 40)])
    (MS (mkR (Z_to_bv 64 SITE_slx_calloc) (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp val (Z_to_bv 64 MK) a1 a2 a3 a4 a5 a6 a7
            z64 (Z_to_bv 64 3) z64 (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_slx_calloc) fc None m (seg_rom asegs)).
Proof.
  intros until s5v. intros KC HK KSB HSB UT SHC TSD SLOT UC MKHI MKAL MKLO MKC ACCM FR ST LO0 LO HTOP MI.
  unfold g_shadow_memory_dynamic_address, SHB, SITE_slx_calloc, SITE_slx_sanew, e_ossl_sa_new in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (TSD_MAIN + 8 * k, TSD_MAIN + 8 * k + 8); (TP_A + -150, TP_A + -149)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (UTN : IMG_UT_HI + 150 <= TP_A /\ IMG_UT_HI <= TSD_MAIN) by (unfold IMG_UT_HI; lia).
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  set (Pk := TSD_MAIN + 8 * k) in *. assert (HPk : TSD_MAIN <= Pk /\ Pk + 8 <= TSD_MAIN + 1024) by (unfold Pk; lia).
  cl_eu (bv_unsigned sp) (-64) EU1.
  zstep. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  do 4 zstep. zstep.
  tcall (T_set_local_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo TSD_MAIN k sb (Z_to_bv 64 0) u);
    [exact KC | exact HK | reflexivity | lia | lia | exact KSB | exact HSB | exact (ut_munch _ m _ UT MU HWU) | exact SHC | exact TSD | lia | lia | exact SLOT | lia | lia | exact UC
    | lia | lia | lia | lia | exact (proj2 UTN) | exact (proj1 UTN) | eassumption | lia | lia | lia | assumption |].
  cbv delta [mkR].
  zstep. th_if_lit.                                                                       (* [comment removed for export] *)
  do 2 zstep.
  do 2 zstep. zstep. zstep. th_if_lit.
  zstep. zstep. th_if_lit.                                                                (* [comment removed for export] *)
  zstep.
  finish. eassumption.
Qed.

(* [comment removed for export] *)
Lemma slx_w2 : forall (sp gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 val : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo MK SA : Z) (j : list byte) (rav s0v s1v s2v s3v s4v s5v : word),
  0x10007fff8000 <= MK -> MK mod 8 = 0 -> MK + 72 <= lo -> rw_cells asegs m MK [CB 24 (zeros 24); C8 z64; CB 40 (zeros 40)] -> acc asegs m MK 72 ->
  0x10007fff8000 <= SA -> SA + 32 <= lo ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  rw_cells asegs m (bv_unsigned sp + -64) [CB 8 j; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk asegs m lo (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 80 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (a3' : word) (m' : mem),
       ms = MS (mkR rav sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0v s1v (Z_to_bv 64 SA) z64 val a3' a4 a5 a6 a7 s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_sa_set) fc None m' (seg_rom asegs)
       /\ munch [(MK + 24, MK + 32)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ stk asegs m' lo (bv_unsigned sp)
       /\ rw_cells asegs m' MK [CB 24 (zeros 24); C8 (Z_to_bv 64 SA); CB 40 (zeros 40)])
    (MS (mkR (Z_to_bv 64 SITE_slx_sanew) (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp val (Z_to_bv 64 SA) a1 a2 a3 a4 a5 a6 a7
            z64 (Z_to_bv 64 (MK + 24)) (Z_to_bv 64 MK) (Z_to_bv 64 (Z.shiftr (MK + 24) 3 + SHB)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_slx_sanew) fc None m (seg_rom asegs)).
Proof.
  intros until s5v. intros MKHI MKAL MKLO MKC ACCM SAHI SALO UT SHC FR ST LO0 LO HTOP MI.
  unfold g_shadow_memory_dynamic_address, SHB, SITE_slx_sanew, e_sa_set in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(MK + 24, MK + 32)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  cl_eu (bv_unsigned sp) (-64) EU1.
  zstep. zstep. th_if_lit.
  zstep.
  zstep. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  zstep. zstep. th_if_lit.
  zstep. do 2 zstep. do 7 zstep.
  th_release FR (bv_unsigned sp).
  do 2 zstep.
  finish.
Qed.

Section CSlx.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_CALLOC : CRYPTO_calloc_stmt RT.
Hypothesis C_SANEW : ossl_sa_new_stmt RT.
Hypothesis C_SAS : sa_set_fresh_stmt RT.
Hypothesis GO_mkey : GOBJ MK_KEY 4.
(* [comment removed for export] *)
Hypothesis TSD : forall Σ m, ART RT Σ m -> rw_cells asegs m (TP_A + -88) [C8 (Z_to_bv 64 TSD_MAIN)].

Definition SLX_SITES : list (Z * Z) := [(SITE_slx_calloc, e_slx); (SITE_slx_sanew, e_slx)] ++ SAS_SITES.
Definition SLX_CALLS : list (Z * Z) := [(SITE_slx_calloc, e_CRYPTO_calloc); (SITE_slx_calloc, e_CRYPTO_zalloc); (SITE_slx_sanew, e_ossl_sa_new); (SITE_slx_sanew, e_CRYPTO_zalloc)] ++ SAS_CALLS.
Definition SLX_W (k : Z) : list (Z * Z) := [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (TSD_MAIN + 8 * k, TSD_MAIN + 8 * k + 8); (TP_A + -150, TP_A + -149)].

(* [comment removed for export] *)
Definition slx_first_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (k : Z) (u : byte),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 3 -> a1 = Z_to_bv 64 1 -> bv_unsigned a2 <> 0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x190 <= bv_unsigned sp ->      (* [comment removed for export] *)
  cg_ctx (rt_cg RT Σ) e_slx (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> In (bv_unsigned ra, e_sa_set) (cg_call (rt_cg RT Σ)) ->
  cg_has (rt_cg RT Σ) SLX_SITES SLX_CALLS ->
  Z.of_nat (length (rt_live RT Σ)) + 2 < LIVE_MAX -> 0 <= rt_credit RT Σ -> cl_env m lb canary ->
  rw_cells asegs m MK_ONCE [C4 (Z_to_bv 64 2)] -> rw_cells asegs m MK_KEY [C4 (Z_to_bv 64 k)] -> 1 <= k < 128 ->
  rw_cells asegs m (TSD_MAIN + 8 * k) [C8 z64] -> rw_cells asegs m (TP_A + -150) [C1 u] ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_slx m)))
    (fun c => exists (Σ' : rts RT) (MK SA P : Z) (u' : byte),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (SLX_W k) m m'
           /\ cl_env m' (Z_to_bv 8 1) canary
           /\ rw_cells asegs m' (TSD_MAIN + 8 * k) [C8 (Z_to_bv 64 MK)] /\ rw_cells asegs m' (TP_A + -150) [C1 u']
           /\ rw_cells asegs m' MK [CB 24 (zeros 24); C8 (Z_to_bv 64 SA); CB 40 (zeros 40)]
           /\ rw_cells asegs m' SA (sa_hdr (Z_to_bv 64 1) z64 z64 (Z_to_bv 64 1) (Z_to_bv 64 P))
           /\ rw_cells asegs m' P [C8 a2; CB 120 (zeros 120)]) c
       /\ rt_live RT Σ' = (P, 128) :: (SA, 32) :: (MK, 72) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_cg RT Σ' = rt_cg RT Σ
       /\ 0 < MK /\ MK mod 16 = 0 /\ MK + 72 < USTACK_TOP /\ 0 < SA /\ SA mod 16 = 0 /\ SA + 32 < USTACK_TOP /\ 0 < P /\ P mod 16 = 0 /\ P + 128 < USTACK_TOP).

Theorem slx_first_cps : slx_first_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary k u
    FDO MST -> -> -> HV ART0 MI0 CALL HSTK CTX UWC TCALL CGH Hlen Hcr CLE OC KC HK SLOT UC.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 384 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -64).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (HLO1 : lo <= usp - 80) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (afp_gsh_byte RT GOBJ AFP Σ m _ _ MK_KEY ART0 GO_mkey ltac:(lia) ltac:(lia) ltac:(reflexivity)) as KSB0. cbn [Z.ltb Z.sub Z.add Z.leb] in KSB0.
  (* [comment removed for export] *)
  pose proof (slx_w0 ra sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo TSD_MAIN k 4
                eq_refl (proj1 OC) (proj1 KC) ltac:(lia) KSB0 ltac:(right; reflexivity) UT SHC (proj1 (TSD Σ m ART0)) ltac:(lia) ltac:(clear - HLOS HK; lia) (proj1 SLOT) ST HLOS HLO1 SPH MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (u1 & j & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 80 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 80 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG01 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  assert (BELOW1 : forall P : Z -> Prop, (forall x, P x -> x < usp - 80) -> agree_on P m m1) by (intros P HP a Ha; apply MU1; cbn [outside]; pose proof (HP _ Ha); split; [lia| exact I]).
  pose proof (cl_env_seg _ m m1 lb canary CLE MU1 ltac:(cl_fp_lia)) as CLE1.
  assert (STAT1 : forall a cs, rw_cells asegs m a cs -> a + Z.of_nat (cells_size cs) <= 0xbc6000 -> rw_cells asegs m1 a cs).
  { intros a cs H H1. apply (rw_cells_agree asegs m m1 _ _ H); [| exact WM1]. apply BELOW1. intros; lia. }
  pose proof (STAT1 _ _ KC ltac:(cbn; lia)) as KC1.
  pose proof (STAT1 _ _ SLOT ltac:(cbn; lia)) as SLOT1. pose proof (STAT1 _ _ UC ltac:(cbn; lia)) as UC1.
  assert (FRR1 : rw_cells asegs m1 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp1 + Z.of_nat (cells_size [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; unfold usp1; lia).
    exact (rw_cells_skip m1 usp1 [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR1). }
  destruct (cl_chain_call (rt_cg RT Σ) e_slx e_CRYPTO_calloc SITE_slx_calloc m m1 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH _ ltac:(left; reflexivity)) (proj2 CGH _ ltac:(left; reflexivity)) UWC AG01 FRR1 ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTX1 & UWC1).
  pose proof (uw_chain_agree outer m m1 sp s0 UWC AG01) as UWCm1.
  (* [comment removed for export] *)
  apply (C_CALLOC Σ PMc (Z_to_bv 64 SITE_slx_calloc) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) t0 u1 t2 sp a2 (Z_to_bv 64 9) (Z_to_bv 64 8) (Z_to_bv 64 SLX_FILE) (Z_to_bv 64 362) a4 a5 a6 a7
           (Z_to_bv 64 0) (Z_to_bv 64 3) (Z_to_bv 64 0) (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo (bv_unsigned ra :: outer) lb canary
           FDO MST eq_refl ltac:(rewrite !unsigned_lit by lia; lia) ltac:(vm_compute; reflexivity) ART1 MI1).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 4. }
  { rewrite EU1. unfold usp1, RT_STACK in *. clear - HSTK. lia. }
  { rewrite (unsigned_lit SITE_slx_calloc) by (unfold SITE_slx_calloc; lia). exact CTX1. }
  { exact UWC1. }
  { rewrite (unsigned_lit SITE_slx_calloc) by (unfold SITE_slx_calloc; lia). apply (proj2 CGH). cbn [SLX_CALLS SAS_CALLS In app]. tauto. }
  { split; intros x Hx; [apply (proj1 CGH) | apply (proj2 CGH)]; cbn [SLX_SITES SLX_CALLS SAS_SITES SAS_CALLS In app] in Hx |- *; clear - Hx; tauto. }
  { lia. } { rewrite !unsigned_lit by lia. change (mcost (9 * 8)) with 0. exact Hcr. } { exact CLE1. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & MK & Hc2 & LV1 & FRS1 & SP1 & CR1 & MK0 & MK16 & MKU & CG1).
  rewrite !unsigned_lit in LV1, CR1, MKU, Hc2 by lia. change (9 * 8) with 72 in *. change (mcost 72) with 0 in CR1.
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & CLE2 & WRB & ACCB & ZB) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & q1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite (ret_pc_even SITE_slx_calloc) in Hc2' by (unfold SITE_slx_calloc; lia). change (Z.to_nat 72) with 72%nat in ZB.
  assert (INMK : In (MK, 72) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
  pose proof (af_live_range RT AF Σ1 m2 MK 72 ART2 INMK) as (_ & MKLO & _). rewrite SP1 in MKLO.
  pose proof (afp_live_hi RT GOBJ AFP Σ1 m2 MK 72 ART2 INMK ltac:(lia)) as MKHI.
  assert (AG2 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp1 x /\ x <> G_ALLOW_CUST) -> agree_on P m1 m2).
  { intros P HP a Ha. destruct (HP _ Ha) as (X1 & X2). apply PRES2; [exact X1|]. unfold G_ALLOW_CUST in *. cbn [outside]. split; [lia | exact I]. }
  assert (STAT2 : forall a cs, rw_cells asegs m1 a cs ->
            (0xb8f190 <= a /\ a + Z.of_nat (cells_size cs) <= 0xba3e98 /\ (a + Z.of_nat (cells_size cs) <= 0xb9f7c0 \/ 0xb9f7c1 <= a))
            \/ (0xbc52a0 <= a /\ a + Z.of_nat (cells_size cs) <= 0xbc57d0) -> rw_cells asegs m2 a cs).
  { intros a cs H H1. apply (rw_cells_agree asegs m1 m2 _ _ H); [| exact WM2]. apply AG2. intros x Hx. split; [right; left; apply client_static_intro; lia | unfold G_ALLOW_CUST; lia]. }
  pose proof (STAT2 _ _ KC1 ltac:(cbn; lia)) as KC2. pose proof (STAT2 _ _ SLOT1 ltac:(cbn; lia)) as SLOT2. pose proof (STAT2 _ _ UC1 ltac:(cbn; lia)) as UC2.
  eassert (FR2 : rw_cells asegs m2 usp1 _).
  { apply (rw_cells_agree asegs m1 m2 _ _ FR1); [| exact WM2]. apply AG2. cbn [cells_size csize Nat.add]. intros x Hx. split; [left; unfold usp1, USTACK_TOP in *; lia | unfold G_ALLOW_CUST, usp1, STACK_WIN, RT_STACK in *; lia]. }
  assert (MKC2 : rw_cells asegs m2 MK [CB 24 (zeros 24); C8 (Z_to_bv 64 0); CB 40 (zeros 40)]) by (split; [split; [cbn; repeat split; reflexivity | exact ZB] | exact WRB]).
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & SHC2 & _ & _ & UT2).
  pose proof (afp_gsh_byte RT GOBJ AFP Σ1 m2 _ _ MK_KEY ART2 GO_mkey ltac:(lia) ltac:(lia) ltac:(reflexivity)) as KSB2. cbn [Z.ltb Z.sub Z.add Z.leb] in KSB2.
  (* [comment removed for export] *)
  pose proof (slx_w1 sp gp u0 q1 u2 b1 b2 b3 b4 b5 b6 b7 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 a2 F2 fc2 m2 lo k 4 MK u j ra s0 s1 s2 s3 s4 s5
                (proj1 KC2) ltac:(lia) KSB2 ltac:(right; reflexivity) UT2 SHC2 (proj1 (TSD Σ1 m2 ART2)) SLOT2 UC2 MKHI ltac:(clear - MK16; Z.div_mod_to_equations; lia) ltac:(clear - MKLO LOW; lia) MKC2 ACCB
                FR2 ST2 HLOS HLO1 SPH MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (e2 & e3 & u' & m3 & -> & MU3 & WM3 & MI3 & FR3 & ST3 & SLOT3 & UC3 & MKC3) & Hc3'). clear Hc3.
  fold usp in MU3, ST3, FR3. fold usp1 in ST3, FR3.
  assert (MU3' : munch ([(TSD_MAIN + 8 * k, TSD_MAIN + 8 * k + 8); (TP_A + -150, TP_A + -149)] ++ [(usp - 80, usp)]) m2 m3) by (eapply munch_weaken; [| exact MU3]; unfold sub_fp; cbn [outside app]; intros; lia).
  pose proof (cl_seg_ART RT AF Σ1 m2 m3 usp 80 _ ART2 ltac:(rewrite SP1; lia) ltac:(unfold USTACK_TOP in *; lia) MU3' ltac:(intros x Hx; apply client_static_intro; cbn [outside app] in Hx; lia) WM3) as ART3.
  assert (AG23 : agree_on (fun x => usp <= x < USTACK_TOP) m2 m3) by (intros a Ha; apply MU3; cbn [outside]; cbv beta in Ha; unfold USTACK_TOP in *; repeat split; try exact I; lia).
  pose proof (cl_env_seg _ m2 m3 _ canary CLE2 MU3 ltac:(cl_fp_lia)) as CLE3.
  assert (FRR3 : rw_cells asegs m3 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp1 + Z.of_nat (cells_size [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; unfold usp1; lia).
    exact (rw_cells_skip m3 usp1 [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR3). }
  rewrite <- CG1 in CTX, CGH, TCALL.
  pose proof (uw_chain_agree outer m1 m2 sp s0 UWCm1 ltac:(apply AG2; intros x Hx; cbv beta in Hx; split; [left; unfold usp1; lia | unfold G_ALLOW_CUST, USTACK_TOP, STACK_WIN, RT_STACK in *; lia])) as UWCm2.
  pose proof (uw_chain_agree outer m2 m3 sp s0 UWCm2 AG23) as UWCm3.
  destruct (cl_chain_call (rt_cg RT Σ1) e_slx e_ossl_sa_new SITE_slx_sanew m3 m3 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH _ ltac:(right; left; reflexivity)) (proj2 CGH _ ltac:(right; right; left; reflexivity))
              UWCm3 ltac:(intros a _; reflexivity) FRR3 ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTX3 & UWC3).
  (* [comment removed for export] *)
  assert (LOW1 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SP1; exact LOW).
  apply (C_SANEW Σ1 PMc (Z_to_bv 64 SITE_slx_sanew) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) u0 q1 u2 sp a2 (Z_to_bv 64 0) (Z_to_bv 64 MK) e2 e3 b4 b5 b6 b7
           (Z_to_bv 64 0) (Z_to_bv 64 (MK + 24)) (Z_to_bv 64 MK) (Z_to_bv 64 (Z.shiftr (MK + 24) 3 + SHB)) s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m3 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary
           FDO MST eq_refl ART3 MI3).
  { fold usp in SPA. cl_call_ok EU1 ST3 LOW1 SPA 4. }
  { rewrite EU1. unfold usp1, RT_STACK in *. clear - HSTK. lia. }
  { rewrite (unsigned_lit SITE_slx_sanew) by (unfold SITE_slx_sanew; lia). exact CTX3. }
  { exact UWC3. }
  { rewrite (unsigned_lit SITE_slx_sanew) by (unfold SITE_slx_sanew; lia). apply (proj2 CGH). cbn [SLX_CALLS SAS_CALLS In app]. tauto. }
  { split; intros x Hx; [apply (proj1 CGH) | apply (proj2 CGH)]; cbn [SLX_SITES SLX_CALLS SAS_SITES SAS_CALLS In app] in Hx |- *; clear - Hx; tauto. }
  { rewrite LV1. cbn [length]. lia. } { rewrite CR1. change (mcost 32) with 0. lia. } { exact CLE3. }
  { exact Hc3'. }
  clear Hc3'. intros c4 (Σ2 & SA & Hc4 & LV2 & FRS2 & SP2 & CR2 & SA0 & SA16 & SAU & CG2). change (mcost 32) with 0 in CR2.
  destruct (ASTA_unpack RT Σ2 _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & CLE4 & WRS & ACCS & ZS) & Hc4'). clear Hc4.
  destruct RS4 as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F4 & fc4 & ->).
  rewrite EU1 in ST4, PRES4. rewrite (ret_pc_even SITE_slx_sanew) in Hc4' by (unfold SITE_slx_sanew; lia). change (Z.to_nat 32) with 32%nat in ZS.
  assert (INSA : In (SA, 32) (rt_live RT Σ2)) by (rewrite LV2; left; reflexivity).
  assert (INMK2 : In (MK, 72) (rt_live RT Σ2)) by (rewrite LV2; right; exact INMK).
  pose proof (af_live_range RT AF Σ2 m4 SA 32 ART4 INSA) as (_ & SALO & _). rewrite SP2, SP1 in SALO.
  pose proof (afp_live_hi RT GOBJ AFP Σ2 m4 SA 32 ART4 INSA ltac:(lia)) as SAHI.
  pose proof (af_live_disj RT AF Σ2 m4 SA 32 MK 72 [] (rt_live RT Σ1) ART4 LV2 INMK) as DISJ.
  assert (AG4 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp1 x /\ x <> G_ALLOW_CUST) -> agree_on P m3 m4).
  { intros P HP a Ha. destruct (HP _ Ha) as (X1 & X2). apply PRES4; [exact X1|]. unfold G_ALLOW_CUST in *. cbn [outside]. split; [lia | exact I]. }
  eassert (FR4 : rw_cells asegs m4 usp1 _).
  { apply (rw_cells_agree asegs m3 m4 _ _ FR3); [| exact WM4]. apply AG4. cbn [cells_size csize Nat.add]. intros x Hx. split; [left; unfold usp1, USTACK_TOP in *; lia | unfold G_ALLOW_CUST, usp1, STACK_WIN, RT_STACK in *; lia]. }
  assert (MKC4 : rw_cells asegs m4 MK [CB 24 (zeros 24); C8 (Z_to_bv 64 0); CB 40 (zeros 40)]).
  { apply (rw_cells_agree asegs m3 m4 _ _ MKC3); [| exact WM4]. apply AG4. cbn [cells_size csize Nat.add]. intros x Hx. split; [apply (acl_live _ _ _ MK 72); [exact INMK | lia] | unfold G_ALLOW_CUST; lia]. }
  assert (SLOT4 : rw_cells asegs m4 (TSD_MAIN + 8 * k) [C8 (Z_to_bv 64 MK)]).
  { apply (rw_cells_agree asegs m3 m4 _ _ SLOT3); [| exact WM4]. apply AG4. cbn [cells_size csize Nat.add]. intros x Hx. split; [right; left; apply client_static_intro; lia | unfold G_ALLOW_CUST; lia]. }
  assert (UC4 : rw_cells asegs m4 (TP_A + -150) [C1 u']).
  { apply (rw_cells_agree asegs m3 m4 _ _ UC3); [| exact WM4]. apply AG4. cbn [cells_size csize Nat.add]. intros x Hx. split; [right; left; apply client_static_intro; lia | unfold G_ALLOW_CUST; lia]. }
  assert (SAC4 : rw_cells asegs m4 SA (sa_hdr (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0))) by (unfold sa_hdr; split; [split; [cbn; repeat split; reflexivity | exact ZS] | exact WRS]).
  destruct (af_client_consts RT AF Σ2 m4 ART4) as (_ & SHC4 & _ & _ & UT4).
  pose proof (proj2 (af_acc_live RT AF Σ2 m4 MK 72 ART4 INMK2)) as ACCM4.
  (* [comment removed for export] *)
  pose proof (slx_w2 sp gp v0 v1 v2 d1 d2 d3 d4 d5 d6 d7 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 a2 F4 fc4 m4 lo MK SA j ra s0 s1 s2 s3 s4 s5
                MKHI ltac:(clear - MK16; Z.div_mod_to_equations; lia) ltac:(clear - MKLO LOW; lia) MKC4 ACCM4 SAHI ltac:(clear - SALO LOW; lia) UT4 SHC4 FR4 ST4 HLOS HLO1 SPH MI4) as W2.
  fold usp usp1 in W2.
  cl_lift W2 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ2 _ _ c5 Hc5) as (ms5 & (e4 & m5 & -> & MU5 & WM5 & MI5 & ST5 & MKC5) & Hc5'). clear Hc5. fold usp in ST5.
  assert (ART5 : ART RT Σ2 m5).
  { apply (af_frame RT AF Σ2 m4 m5 usp1 ART4 ltac:(rewrite SP2, SP1; unfold usp1; lia)); [| exact WM5].
    intros x Hx. apply MU5. cbn [outside]. split; [| exact I]. intros Hin; apply Hx. apply (acl_live _ _ _ MK 72); [exact INMK2 | clear - Hin; lia]. }
  pose proof (cl_env_seg _ m4 m5 _ canary CLE4 MU5 ltac:(cl_fp_lia)) as CLE5.
  assert (AG45 : agree_on (fun x => usp <= x < USTACK_TOP) m4 m5) by (intros a Ha; apply MU5; cbn [outside]; cbv beta in Ha; clear - Ha MKLO LOW HSTK; unfold RT_STACK in *; split; [lia | exact I]).
  pose proof (uw_chain_agree outer m3 m4 sp s0 UWCm3 ltac:(apply AG4; intros x Hx; cbv beta in Hx; split; [left; unfold usp1; lia | unfold G_ALLOW_CUST, USTACK_TOP, STACK_WIN, RT_STACK in *; lia])) as UWCm4.
  pose proof (uw_chain_agree outer m4 m5 sp s0 UWCm4 AG45) as UWCm5.
  assert (SAC5 : rw_cells asegs m5 SA (sa_hdr (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { apply (rw_cells_agree asegs m4 m5 _ _ SAC4); [| exact WM5]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add sa_hdr] in Hx. apply MU5. cbn [outside]. clear - Hx DISJ. split; [lia | exact I]. }
  rewrite <- CG2 in TCALL, CGH, CTX.
  (* [comment removed for export] *)
  apply (C_SAS Σ2 PMc ra sp gp (Z_to_bv 64 TP_A) v0 v1 v2 s0 s1 (Z_to_bv 64 SA) (Z_to_bv 64 0) a2 e4 d4 d5 d6 d7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6
           F4 fc4 m5 lo outer (Z_to_bv 8 1) canary SA FDO MST eq_refl eq_refl eq_refl HV ART5 MI5).
  { unfold call_ok. fold usp. split; [exact ST5|]. split; [rewrite SP2, SP1; exact LOW|]. split; [exact LOR|]. split; [exact SPT | exact SPA]. }
  { fold usp. clear - HSTK. unfold RT_STACK in *. lia. }
  { destruct CTX as [_ LK]. split; [exact TCALL | exact LK]. }
  { exact UWCm5. }
  { split; intros x Hx; [apply (proj1 CGH) | apply (proj2 CGH)]; cbn [SLX_SITES SLX_CALLS In app] in Hx |- *; clear - Hx; tauto. }
  { rewrite LV2, LV1. cbn [length]. lia. } { rewrite CR2, CR1. lia. } { exact CLE5. }
  { exact INSA. } { clear - SA16. Z.div_mod_to_equations. lia. } { exact SAC5. }
  { exact Hc5'. }
  clear Hc5'. intros c6 (Σ3 & P & Hc6 & LV3 & FRS3 & SP3 & CR3 & P0 & P16 & PU & CG3).
  apply Hk. exists Σ3, MK, SA, P, u'.
  split.
  2:{ split; [rewrite LV3, LV2, LV1; reflexivity|]. split; [rewrite FRS3, FRS2; exact FRS1|]. split; [rewrite SP3, SP2; exact SP1|]. split; [rewrite CR3, CR2, CR1; lia|].
      split; [rewrite CG3, CG2; exact CG1|]. repeat split; assumption. }
  apply (ASTA_conseq RT Σ3 PMc _ _ c6 Hc6). intros ms6 (m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & CLE6 & SAC6 & PC6). exists m6.
  split; [exact RS6|].
  split; [split; [exact ART6|]; split; [exact MI6|]; split; [exact (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 (wmono_trans asegs _ _ _ WM3 (wmono_trans asegs _ _ _ WM4 (wmono_trans asegs _ _ _ WM5 WM6))))) | exact ST6]|].
  assert (NMK : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) usp x -> ~ (MK <= x < MK + 72)) by (intros x Hx; exact (newchunk_apart RT AF Σ Σ1 m2 MK 72 usp _ ART2 LV1 FRS1 SP1 ltac:(lia) ltac:(lia) Hx)).
  assert (NSA : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) usp x -> ~ (SA <= x < SA + 32)).
  { intros x Hx. apply (newchunk_apart RT AF Σ1 Σ2 m4 SA 32 usp _ ART4 LV2 FRS2 SP2 ltac:(rewrite SP1; lia) ltac:(lia)).
    apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e He; rewrite LV1; right; exact He | rewrite FRS1; intros e He; exact He | lia]. }
  assert (ACL1 : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) usp x -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp1 x).
  { intros x Hx. apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e He; rewrite LV1; right; exact He | rewrite FRS1; intros e He; exact He | unfold usp1; lia]. }
  assert (ACL2 : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) usp x -> aclient (rt_live RT Σ2) (rt_frames RT Σ2) usp x).
  { intros x Hx. apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e He; rewrite LV2, LV1; right; right; exact He | rewrite FRS2, FRS1; intros e He; exact He | lia]. }
  split.
  { intros a Ha Ho. pose proof (cl_split RT AF Σ m usp 80 _ ART0 ltac:(lia) ltac:(lia) Ha) as SPL. cbn [outside] in Ho. destruct Ho as (O1 & O2 & O3 & _).
    rewrite (PRES6 a (ACL2 _ Ha) ltac:(cbn [outside]; pose proof (NSA _ Ha); repeat split; try exact I; lia)).
    rewrite (MU5 a ltac:(cbn [outside]; pose proof (NMK _ Ha); split; [lia | exact I])).
    rewrite (PRES4 a (ACL1 _ Ha) ltac:(cbn [outside]; split; [lia | exact I])).
    rewrite (MU3 a ltac:(cbn [outside]; unfold usp in *; repeat split; try exact I; lia)).
    rewrite (PRES2 a ltac:(apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He | intros e He; exact He | unfold usp1; lia]) ltac:(cbn [outside]; split; [lia | exact I])).
    apply PR1; [exact Ha | exact I]. }
  split; [exact CLE6|].
  assert (AG6 : forall Q : Z -> Prop, (forall x, Q x -> aclient (rt_live RT Σ2) (rt_frames RT Σ2) usp x /\ x <> G_ALLOW_CUST /\ ~ (SA <= x < SA + 32)) -> agree_on Q m5 m6).
  { intros Q HQ a Ha. destruct (HQ _ Ha) as (X1 & X2 & X3). apply PRES6; [exact X1|]. unfold G_ALLOW_CUST in *. cbn [outside]. repeat split; try exact I; lia. }
  split. { apply (rw_cells_agree asegs m4 m6 _ _ SLOT4); [| exact (wmono_trans asegs _ _ _ WM5 WM6)]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
           rewrite (AG6 (fun y => y = bv_unsigned x) ltac:(intros y ->; split; [right; left; apply client_static_intro; lia|]; unfold G_ALLOW_CUST; lia) x eq_refl).
           apply MU5. cbn [outside]. split; [lia | exact I]. }
  split. { apply (rw_cells_agree asegs m4 m6 _ _ UC4); [| exact (wmono_trans asegs _ _ _ WM5 WM6)]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
           rewrite (AG6 (fun y => y = bv_unsigned x) ltac:(intros y ->; split; [right; left; apply client_static_intro; lia|]; unfold G_ALLOW_CUST; lia) x eq_refl).
           apply MU5. cbn [outside]. split; [lia | exact I]. }
  split. { apply (rw_cells_agree_nw asegs m5 m6 _ _ MKC5). apply AG6. cbn [cells_size csize Nat.add]. intros x Hx.
           split; [apply (acl_live _ _ _ MK 72); [exact INMK2 | lia]|]. unfold G_ALLOW_CUST. clear - Hx MKHI DISJ. lia. }
  exact (conj SAC6 PC6).
Qed.
End CSlx.
