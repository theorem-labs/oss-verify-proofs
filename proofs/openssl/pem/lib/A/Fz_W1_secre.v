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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_W4_kit Fz_env Fz_M_malloc Fz_M_free Fz_M_cleanse Fz_M_secure Fz_W1_defs Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition SITE_sr_sm : Z := 0x24a174.       (* [comment removed for export] *)
Definition SITE_sr_cpy : Z := 0x24a1bc.      (* [comment removed for export] *)
Definition SITE_sr_scf : Z := 0x24a1d4.      (* [comment removed for export] *)
Definition BUFFER_FILE : Z := 0x73520.       (* [comment removed for export] *)
(* [comment removed for export] *)
Definition sr_frame (s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell := [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition sr_s0_post (sp gp tp t0 t1 t2 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' s3' s4' s5' s6' : word) (BM n lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_sr_sm) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp s1' (Z_to_bv 64 n) (Z_to_bv 64 BUFFER_FILE) (Z_to_bv 64 60) (Z_to_bv 64 n)
                 a4 a5 a6 a7 s2' (Z_to_bv 64 BM) s4' s5' (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_CRYPTO_secure_malloc) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -64) (sr_frame s6' s5' s4' s3' s2' s1' s0' ra0) /\ stk asegs m' lo (bv_unsigned sp + -64).

Lemma sr_s0_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BM n : Z),
  lo <= bv_unsigned sp - 64 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] -> 0 <= BM < 2^64 -> 0 <= n < 2^64 -> mem_inv asegs m ->
  evt asegs (sr_s0_post sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ra0 s0' s1' s2' s3' s4' s5' s6' BM n lo m)
    (MS (mkR ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' (Z_to_bv 64 BM) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_sec_alloc_realloc) fc None m (seg_rom asegs)).
Proof.
  intros until n. intros HLO HLOS SPH ST UT SHC HBM HN MI.
  unfold e_sec_alloc_realloc, g_shadow_memory_dynamic_address in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 64, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 64, SP)]) by ut_fp_lia. assert (HWS : sh_fp [(SP - 64, SP)]) by sh_fp_lia.
  th_frame 64%nat [8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  zstep. do 8 zstep. zstep.
  zstep. zstep. zstep. zstep.
  zstep. zstep. zstep. zstep. zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold sr_s0_post, SITE_sr_sm, e_CRYPTO_secure_malloc, BUFFER_FILE, sr_frame. apply evt_done. eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact FR | assumption].
Qed.

(* [comment removed for export] *)
Definition sr_s1_post (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (BM q D L : Z) (m : mem) : machine_state -> Prop :=
  fun ms =>
    ms = MS (mkR (Z_to_bv 64 SITE_sr_cpy) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp (Z_to_bv 64 (BM + 8)) (Z_to_bv 64 q) (Z_to_bv 64 D) (Z_to_bv 64 L) a3
                 a4 a5 a6 a7 (Z_to_bv 64 q) (Z_to_bv 64 L) (Z_to_bv 64 D) (Z_to_bv 64 ((BM + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_asan_memcpy) fc None m (seg_rom asegs).

Lemma sr_s1_walk : forall ra1 sp gp t0 t1 t2 s1x a1 a2 a3 a4 a5 a6 a7 s2x s4x s5x s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (BM q D L max : Z) (flw : word),
  bv_unsigned sp <= 2^47 -> img_untouched m ->
  rw_cells asegs m BM [C8 (Z_to_bv 64 L); C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 max); C8 flw] -> acc asegs m BM 32 -> 0 < BM -> BM mod 16 = 0 -> 0x10007fff8000 <= BM -> BM + 32 <= 2^47 ->
  0 < q < 2^64 -> 0 < D < 2^64 -> 0 <= L < 2^64 -> mem_inv asegs m ->
  evt asegs (sr_s1_post sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc BM q D L m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1x (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7
             s2x (Z_to_bv 64 BM) s4x s5x (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_sr_sm) fc None m (seg_rom asegs)).
Proof.
  intros until flw. intros SPH UT BMC ACCBM BM0 BMAL BMHI BMU HQ HD HL MI.
  unfold SITE_sr_sm in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (BMAL8 : BM mod 8 = 0) by (clear - BMAL; Z.div_mod_to_equations; lia).
  zstep. do 2 zstep. zstep. zstep. th_if_lit.
  zstep. zstep.
  zstep. if_cases Kd; zify_cond Kd; try (exfalso; rewrite ?unsigned_lit in Kd by lia; lia). try clear Kd.
  zstep. if_cases Kq; zify_cond Kq; try (exfalso; rewrite ?unsigned_lit in Kq by lia; lia). try clear Kq.
  do 3 zstep. zstep. th_if_lit.
  zstep. zstep. zstep. zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold sr_s1_post, SITE_sr_cpy, e_asan_memcpy. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Definition sr_s2_post (sp gp tp t0 t1 t2 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (BM q D L : Z) (m : mem) : machine_state -> Prop :=
  fun ms =>
    ms = MS (mkR (Z_to_bv 64 SITE_sr_scf) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp (Z_to_bv 64 (BM + 8)) (Z_to_bv 64 D) (Z_to_bv 64 L) (Z_to_bv 64 BUFFER_FILE) (Z_to_bv 64 64)
                 a4 a5 a6 a7 (Z_to_bv 64 q) (Z_to_bv 64 L) (Z_to_bv 64 D) (Z_to_bv 64 ((BM + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_CRYPTO_secure_clear_free) fc None m (seg_rom asegs).

Lemma sr_s2_walk : forall ra1 sp gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (BM q D L : Z),
  bv_unsigned sp <= 2^47 -> 0 <= D < 2^64 -> 0 <= L < 2^64 -> mem_inv asegs m ->
  evt asegs (sr_s2_post sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc BM q D L m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 (BM + 8)) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 q) (Z_to_bv 64 L) (Z_to_bv 64 D) (Z_to_bv 64 ((BM + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_sr_cpy) fc None m (seg_rom asegs)).
Proof.
  intros until L. intros SPH HD HL MI.
  unfold SITE_sr_cpy in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep. zstep. zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold sr_s2_post, SITE_sr_scf, e_CRYPTO_secure_clear_free, BUFFER_FILE. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Definition sr_s3_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (BM q lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(BM + 8, BM + 16)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (BM + 8) [C8 (Z_to_bv 64 0)].

Lemma sr_s3_walk : forall ra0 ra1 sp gp t0 t1 t2 s0' s1' s2' s3' s4' s5' s6' a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 (s3x s4x : word)
    (F : bvmap 5 word) fc (m : mem) (lo BM q : Z) (dw : word),
  lo <= bv_unsigned sp - 64 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp + -64) -> img_untouched m ->
  rw_cells asegs m (bv_unsigned sp + -64) (sr_frame s6' s5' s4' s3' s2' s1' s0' ra0) ->
  rw_cells asegs m (BM + 8) [C8 dw] -> acc asegs m BM 32 -> 0 < BM -> BM mod 16 = 0 -> 0x10007fff8000 <= BM -> BM + 32 <= lo -> 0 <= q < 2^64 -> mem_inv asegs m ->
  evt asegs (sr_s3_post ra0 sp gp (Z_to_bv 64 0xba3ef0) s0' s1' s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 F fc BM q lo m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 (BM + 8)) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 q) s3x s4x (Z_to_bv 64 ((BM + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_sr_scf) fc None m (seg_rom asegs)).
Proof.
  intros until dw. intros HLO HLOS SPH ST UT FR DWC ACCBM BM0 BMAL BMHI BMLO HQ MI.
  unfold SITE_sr_scf, sr_frame in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(BM + 8, BM + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(BM + 8, BM + 16)]) by ut_fp_lia. assert (HWS : sh_fp [(BM + 8, BM + 16)]) by sh_fp_lia.
  assert (BMAL8 : BM mod 8 = 0) by (clear - BMAL; Z.div_mod_to_equations; lia).
  assert (EU : bv_unsigned (Z_to_bv 64 (SP + -64)) = SP + -64) by (apply unsigned_lit; lia).
  zstep. zstep. th_if_lit.
  zstep. th_fix_lit_store.
  zstep.
  do 8 zstep. zstep. th_release FR SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold sr_s3_post. apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
Definition sr_nd_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (q lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma sr_nd_walk : forall ra0 ra1 sp gp t0 t1 t2 s0' s1' s2' s3' s4' s5' s6' a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 (s1x s2x s4x s5x : word)
    (F : bvmap 5 word) fc (m : mem) (lo BM q L max : Z) (flw : word),
  lo <= bv_unsigned sp - 64 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp + -64) -> img_untouched m ->
  rw_cells asegs m (bv_unsigned sp + -64) (sr_frame s6' s5' s4' s3' s2' s1' s0' ra0) ->
  rw_cells asegs m BM [C8 (Z_to_bv 64 L); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 max); C8 flw] -> acc asegs m BM 32 -> 0 < BM -> BM mod 16 = 0 -> 0x10007fff8000 <= BM -> BM + 32 <= lo ->
  0 <= q < 2^64 -> mem_inv asegs m ->
  evt asegs (sr_nd_post ra0 sp gp (Z_to_bv 64 0xba3ef0) s0' s1' s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 F fc q lo m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1x (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7
             s2x (Z_to_bv 64 BM) s4x s5x (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_sr_sm) fc None m (seg_rom asegs)).
Proof.
  intros until flw. intros HLO HLOS SPH ST UT FR BMC ACCBM BM0 BMAL BMHI BMLO HQ MI.
  unfold SITE_sr_sm, sr_frame in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (BMAL8 : BM mod 8 = 0) by (clear - BMAL; Z.div_mod_to_equations; lia).
  assert (EU : bv_unsigned (Z_to_bv 64 (SP + -64)) = SP + -64) by (apply unsigned_lit; lia).
  zstep. do 2 zstep. zstep. zstep. th_if_lit.
  zstep. zstep.
  zstep. th_if_lit.
  zstep.
  do 8 zstep. zstep. th_release FR SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold sr_nd_post. apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

Section CSecre.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_SM : crypto_secure_malloc_env_stmt RT.
Hypothesis MCP : memcpy_icontract RT e_asan_memcpy.
Hypothesis C_SCF : crypto_secure_clear_free_env_stmt RT.

Definition SR_SITES : list (Z * Z) := [(SITE_sr_sm, e_sec_alloc_realloc); (SITE_sr_scf, e_sec_alloc_realloc); (SITE_cm_malloc, e_CRYPTO_malloc)].
Definition SR_CALLS : list (Z * Z) :=
  [(SITE_sr_sm, e_CRYPTO_secure_malloc); (SITE_sr_sm, e_CRYPTO_malloc); (SITE_sr_scf, e_CRYPTO_secure_clear_free); (SITE_sr_scf, e_CRYPTO_free);
   (SITE_sr_scf, e_free); (SITE_cm_malloc, e_malloc)].
Definition SR_W (BM : Z) : list (Z * Z) := [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (BM + 8, BM + 16)].

(* [comment removed for export] *)
Definition secre_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BM D L max n : Z) (flw : word) (bs : list byte) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BM -> a1 = Z_to_bv 64 n ->
  In (BM, 32) (rt_live RT Σ) -> BM mod 16 = 0 -> rw_cells asegs m BM [C8 (Z_to_bv 64 L); C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 max); C8 flw] ->
  In (D, max) (rt_live RT Σ) -> D <> BM -> 0 <= L <= max -> 1 <= max -> L <= n -> max < 2 ^ 40 -> 1 <= n <= 0x8000000 ->
  bytes_at asegs m D bs -> Z.of_nat (length bs) = L ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 112 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_sec_alloc_realloc (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) SR_SITES SR_CALLS ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost n <= rt_credit RT Σ -> cl_env m lb canary -> sec_off m ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_sec_alloc_realloc m)))
    (fun c => exists (Σ' : rts RT) (q : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 q) m' ms
           /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) (bv_unsigned sp) (SR_W BM) m m'
           /\ cl_env m' (Z_to_bv 8 1) canary /\ sec_off m' /\ rw_cells asegs m' (BM + 8) [C8 (Z_to_bv 64 0)]
           /\ bytes_at asegs m' q bs /\ wr_at asegs m' q n /\ acc asegs m' q n) c
       /\ rt_live RT Σ' = (q, n) :: live_remove D (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - mcost n /\ 0 < q /\ q mod 16 = 0 /\ q + n < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem secre_cps : secre_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BM D L max n flw bs outer lb canary
    FDO MST -> -> -> INBM BMAL BMC IND NDBM HL HMAX1 HLN HMAX Hn SB LBS ART0 MI0 CALL HSTK CTX UWC CGH Hlen Hcr CLE SEC.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 64 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -64).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (HLO1 : lo <= usp - 64) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  assert (HLOI : SEGTOP_A <= lo) by (unfold SEGTOP_A, STACK_WIN in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (af_live_range RT AF Σ m BM 32 ART0 INBM) as (BM0 & BMLO' & _). assert (BMLO : BM + 32 <= lo) by (clear - BMLO' LOW; lia). clear BMLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BM 32 ART0 INBM ltac:(lia)) as BMHI.
  pose proof (af_live_range RT AF Σ m D max ART0 IND) as (D0 & DLO' & DIMG). assert (DLO : D + max <= lo) by (clear - DLO' LOW; lia).
  pose proof (live_ne_apart RT AF Σ m D max BM 32 ART0 IND INBM ltac:(intros E; injection E; intros _; exact NDBM)) as APDM.
  (* [comment removed for export] *)
  pose proof (sr_s0_walk ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BM n
                HLO1 HLOS SPH ST UT SHC ltac:(clear - BM0 BMLO HLO1 SPH; lia) ltac:(clear - Hn; lia) MI0) as W0.
  fold usp in W0. fold usp1 in W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 64 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 64 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  assert (AGL1 : forall a k, a + k <= lo -> agree_on (fun x => a <= x < a + k) m m1) by (intros a' k H x Hx; cbv beta in Hx; apply MU1; cbn [outside]; clear - H Hx HLO1; lia).
  pose proof (cl_env_seg _ m m1 lb canary CLE MU1 ltac:(cl_fp_lia)) as CLE1.
  assert (SEC1 : sec_off m1) by (apply (sec_off_agree m m1 SEC); intros a Ha; apply MU1; cbn [outside]; rewrite Ha; unfold SEC_INIT; split; [clear - HLO1 HLOS; lia | exact I]).
  assert (CO1 : call_ok RT Σ m1 (Z_to_bv 64 usp1) lo).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 4. }
  assert (FRR1 : rw_cells asegs m1 (usp - 16) [C8 s0; C8 ra]).
  { unfold sr_frame in FR1. replace (usp - 16) with (usp1 + Z.of_nat (cells_size [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; unfold usp1; lia).
    exact (rw_cells_skip m1 usp1 [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR1). }
  destruct (cl_chain_call (rt_cg RT Σ) e_sec_alloc_realloc e_CRYPTO_secure_malloc SITE_sr_sm m m1 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH (SITE_sr_sm, e_sec_alloc_realloc) (or_introl eq_refl)) (proj2 CGH (SITE_sr_sm, e_CRYPTO_secure_malloc) (or_introl eq_refl)) UWC AG1 FRR1
              ltac:(rewrite EU1; unfold usp1; lia) SPT) as (CTXa & UWCa).
  (* [comment removed for export] *)
  apply (C_SM Σ PMc (Z_to_bv 64 SITE_sr_sm) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 (Z_to_bv 64 n) (Z_to_bv 64 BUFFER_FILE) (Z_to_bv 64 60) (Z_to_bv 64 n)
           a4 a5 a6 a7 s2 (Z_to_bv 64 BM) s4 s5 (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 n lo (bv_unsigned ra :: outer) lb canary
           FDO MST eq_refl eq_refl Hn ART1 MI1 CO1 ltac:(rewrite EU1; unfold usp1, RT_STACK in *; clear - HSTK; lia)).
  { rewrite (unsigned_lit SITE_sr_sm) by (unfold SITE_sr_sm; lia). exact CTXa. }
  { exact UWCa. }
  { rewrite (unsigned_lit SITE_sr_sm) by (unfold SITE_sr_sm; lia). apply (proj2 CGH). right; left; reflexivity. }
  { apply (cg_has_sub _ _ _ _ _ CGH); intros e He; unfold SR_SITES, SR_CALLS; cbn [In] in He |- *; [do 2 right | do 5 right]; exact He. }
  { exact Hlen. } { exact Hcr. } { exact CLE1. } { exact SEC1. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & q & Hc2 & LV1 & FRS1 & SP1 & CR1 & Q0 & Q16 & QU & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & CLE2 & SEC2 & WR2 & ACC2) & Hc2'). clear Hc2.
  destruct RS2 as (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_sr_sm) in Hc2' by (unfold SITE_sr_sm; lia).
  assert (INQ1 : In (q, n) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
  pose proof (af_live_range RT AF Σ1 m2 q n ART2 INQ1) as (_ & QLO' & QI). rewrite SP1 in QLO'. assert (QLO : q + n <= lo) by (clear - QLO' LOW; lia). clear QLO'.
  assert (INBM1 : In (BM, 32) (rt_live RT Σ1)) by (rewrite LV1; right; exact INBM).
  assert (IND1 : In (D, max) (rt_live RT Σ1)) by (rewrite LV1; right; exact IND).
  pose proof (live_ne_apart RT AF Σ1 m2 q n D max ART2 INQ1 IND1 ltac:(intros E; injection E; intros _ Eq; rewrite Eq in QU; pose proof (newchunk_apart RT AF Σ Σ1 m2 q n usp D ART2 LV1 FRS1 SP1 ltac:(lia) ltac:(lia) ltac:(apply (acl_live _ _ _ D max); [exact IND | clear - HMAX1; lia])); lia)) as APQD.
  pose proof (live_ne_apart RT AF Σ1 m2 q n BM 32 ART2 INQ1 INBM1 ltac:(intros E; injection E; intros _ Eq; pose proof (newchunk_apart RT AF Σ Σ1 m2 q n usp BM ART2 LV1 FRS1 SP1 ltac:(lia) ltac:(lia) ltac:(apply (acl_live _ _ _ BM 32); [exact INBM | lia])); lia)) as APQM.
  assert (P2 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> bv_unsigned x <> G_ALLOW_CUST -> m2 x = m x).
  { intros x Hx HG. rewrite (PRES2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; clear; lia]) ltac:(cbn [outside]; split; [clear - HG; lia | exact I])).
    apply PR1; [exact Hx | exact I]. }
  assert (BMC2 : rw_cells asegs m2 BM [C8 (Z_to_bv 64 L); C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 max); C8 flw]).
  { apply (rw_cells_agree_nw asegs m m2 _ _ BMC). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply P2; [apply (acl_live _ _ _ BM 32); [exact INBM | clear - Hx; lia] | unfold G_ALLOW_CUST; clear - Hx BMHI; lia]. }
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & _ & _ & _ & UT2).
  (* [comment removed for export] *)
  pose proof (sr_s1_walk (Z_to_bv 64 SITE_sr_sm) sp gp y0 y1 y2 s1 h1 h2 h3 h4 h5 h6 h7 s2 s4 s5 s7 s8 s9 s10 s11 y3 y4 y5 y6 F2 fc2 m2 BM q D L max flw
                SPH UT2 BMC2 (proj2 (af_acc_live RT AF Σ1 m2 BM 32 ART2 INBM1)) BM0 BMAL BMHI ltac:(clear - BMLO HLO1 SPH; lia)
                ltac:(clear - Q0 QU Hn; unfold USTACK_TOP in *; lia) ltac:(clear - D0 DLO HLO1 SPH HL; lia) ltac:(clear - HL HMAX; lia) MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & -> & Hc3'). clear Hc3.
  (* [comment removed for export] *)
  assert (SB2 : bytes_at asegs m2 D bs).
  { apply (bytes_at_agree asegs m m2 _ _ SB). intros x Hx. cbv beta in Hx. rewrite LBS in Hx.
    apply P2; [apply (acl_live _ _ _ D max); [exact IND | clear - Hx HL; lia] | unfold G_ALLOW_CUST; pose proof (afp_live_hi RT GOBJ AFP Σ m BM 32 ART0 INBM ltac:(lia)); clear - Hx HL DIMG D0; unfold SEGTOP_A in *; lia]. }
  assert (CO2 : call_ok RT Σ1 m2 (Z_to_bv 64 usp1) lo).
  { fold usp in SPA. rewrite <- SP1 in LOW. cl_call_ok EU1 ST2 LOW SPA 4. }
  apply (MCP Σ1 PMc (Z_to_bv 64 SITE_sr_cpy) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) y0 y1 y2 sp (Z_to_bv 64 (BM + 8)) (Z_to_bv 64 q) (Z_to_bv 64 D) (Z_to_bv 64 L) h3
           h4 h5 h6 h7 (Z_to_bv 64 q) (Z_to_bv 64 L) (Z_to_bv 64 D) (Z_to_bv 64 ((BM + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 y3 y4 y5 y6 F2 fc2 m2 q D bs lo
           FDO MST eq_refl eq_refl ltac:(rewrite LBS; reflexivity) ltac:(clear - Q0 QU Hn; unfold USTACK_TOP in *; lia) ltac:(clear - D0 DLO HLO1 SPH HL; lia) ltac:(rewrite LBS; clear - HL HMAX; lia) SB2).
  { rewrite LBS. split; [| left; clear - DLO HL; lia]. intros HL0. split.
    - exact (acc_sub asegs m2 D max D L (proj2 (af_acc_live RT AF Σ1 m2 D max ART2 IND1)) ltac:(lia) ltac:(clear - HL; lia)).
    - left. exists D, max. split; [exact IND1 | clear - HL; lia]. }
  { rewrite LBS. exact (live_checked_dst RT AF Σ1 m2 _ q n q L ART2 INQ1 ltac:(lia) ltac:(clear - HLN; lia) ltac:(clear - HL; lia)). }
  { rewrite LBS. clear - APQD HL HLN. lia. }
  { exact ART2. } { exact MI2. } { exact CO2. }
  { exact Hc3'. }
  clear Hc3'. intros c4 Hc4.
  destruct (ASTA_unpack RT Σ1 _ _ c4 Hc4) as (ms4 & (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3 & CPY3) & Hc4'). clear Hc4.
  destruct RS3 as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F3 & fc3 & ->).
  rewrite EU1 in ST3, PRES3. rewrite LBS in PRES3. rewrite (ret_pc_even SITE_sr_cpy) in Hc4' by (unfold SITE_sr_cpy; lia).
  assert (P3 : forall x : word, aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp1 (bv_unsigned x) -> ~ (q <= bv_unsigned x < q + L) -> m3 x = m2 x) by (intros x Hx Hno; exact (PRES3 x Hx Hno)).
  (* [comment removed for export] *)
  pose proof (sr_s2_walk (Z_to_bv 64 SITE_sr_cpy) sp gp w0 w1 w2 (Z_to_bv 64 q) e1 e2 e3 e4 e5 e6 e7 s7 s8 s9 s10 s11 w3 w4 w5 w6 F3 fc3 m3 BM q D L
                SPH ltac:(clear - D0 DLO HLO1 SPH HL; lia) ltac:(clear - HL HMAX; lia) MI3) as W2.
  fold usp usp1 in W2.
  cl_lift W2 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ1 _ _ c5 Hc5) as (ms5 & -> & Hc5'). clear Hc5.
  (* [comment removed for export] *)
  assert (CO3 : call_ok RT Σ1 m3 (Z_to_bv 64 usp1) lo).
  { fold usp in SPA. pose proof LOW as LOW1. rewrite <- SP1 in LOW1. cl_call_ok EU1 ST3 LOW1 SPA 4. }
  assert (AG13 : forall x : word, usp1 <= bv_unsigned x < USTACK_TOP -> m3 x = m1 x).
  { intros x Hx. rewrite (P3 x ltac:(left; exact Hx) ltac:(clear - Hx QLO HLO1 HLN; unfold usp1 in *; lia)).
    apply PRES2; [left; exact Hx|]. cbn [outside]. unfold G_ALLOW_CUST, usp1 in *. split; [clear - Hx HLO1 HLOS; lia | exact I]. }
  assert (FRR3 : rw_cells asegs m3 (usp - 16) [C8 s0; C8 ra]).
  { apply (rw_cells_agree_nw asegs m1 m3 _ _ FRR1). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply AG13. unfold usp1, USTACK_TOP in *. clear - Hx NUM. lia. }
  assert (AG03 : agree_on (fun x => usp <= x < USTACK_TOP) m m3) by (intros x Hx; cbv beta in Hx; rewrite (AG13 x ltac:(unfold usp1; clear - Hx; lia)); exact (AG1 x Hx)).
  destruct (cl_chain_call (rt_cg RT Σ) e_sec_alloc_realloc e_CRYPTO_secure_clear_free SITE_sr_scf m m3 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH (SITE_sr_scf, e_sec_alloc_realloc) (or_intror (or_introl eq_refl))) (proj2 CGH (SITE_sr_scf, e_CRYPTO_secure_clear_free) (or_intror (or_intror (or_introl eq_refl)))) UWC AG03 FRR3
              ltac:(rewrite EU1; unfold usp1; lia) SPT) as (CTXb & UWCb).
  assert (CLE3 : cl_env m3 (Z_to_bv 8 1) canary).
  { apply (cl_env_pres_ex _ _ _ q L m2 m3 _ canary CLE2 PRES3). intros x Hx. pose proof (client_static_range x (cl_cell_static x Hx)).
    unfold SEGTOP_A in *. clear - H QI Q0 HLN HL. lia. }
  assert (SEC3 : sec_off m3).
  { apply (sec_off_agree m2 m3 SEC2). intros a Ha. apply P3; [right; left; rewrite Ha; exact sec_init_static|]. rewrite Ha.
    unfold SEC_INIT, SEGTOP_A in *. clear - QI Q0 HLN HL. lia. }
  apply (C_SCF Σ1 PMc (Z_to_bv 64 SITE_sr_scf) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 sp (Z_to_bv 64 (BM + 8)) (Z_to_bv 64 D) (Z_to_bv 64 L) (Z_to_bv 64 BUFFER_FILE) (Z_to_bv 64 64)
           e4 e5 e6 e7 (Z_to_bv 64 q) (Z_to_bv 64 L) (Z_to_bv 64 D) (Z_to_bv 64 ((BM + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 w3 w4 w5 w6 F3 fc3 m3
           D max L lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl eq_refl eq_refl IND1 ltac:(clear - HL; lia) HMAX1 ltac:(clear - HL HMAX; lia) ART3 MI3 CO3
           ltac:(rewrite EU1; unfold usp1, RT_STACK in *; clear - HSTK; lia)).
  { rewrite CG1, (unsigned_lit SITE_sr_scf) by (unfold SITE_sr_scf; lia). exact CTXb. }
  { exact UWCb. }
  { rewrite CG1, (unsigned_lit SITE_sr_scf) by (unfold SITE_sr_scf; lia). apply (proj2 CGH). do 3 right; left; reflexivity. }
  { rewrite CG1, (unsigned_lit SITE_sr_scf) by (unfold SITE_sr_scf; lia). apply (proj2 CGH). do 4 right; left; reflexivity. }
  { exact CLE3. } { exact SEC3. }
  { exact Hc5'. }
  clear Hc5'. intros c6 (Σ2 & v2 & Hc6 & LV2 & FRS2 & SP2 & CR2 & CG2).
  destruct (ASTA_unpack RT Σ2 _ _ c6 Hc6) as (ms6 & (m4 & RS4 & (ART4 & MI4 & ST4) & PRES4 & CLE4 & SEC4) & Hc6'). clear Hc6.
  destruct RS4 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F4 & fc4 & ->).
  rewrite EU1 in ST4, PRES4. rewrite (ret_pc_even SITE_sr_scf) in Hc6' by (unfold SITE_sr_scf; lia).
  assert (INBM2 : In (BM, 32) (rt_live RT Σ2)) by (rewrite LV2; apply live_remove_keep; [exact INBM1 | cbn [fst]; intros E; exact (NDBM (eq_sym E))]).
  assert (INQ2 : In (q, n) (rt_live RT Σ2)) by (rewrite LV2; apply live_remove_keep; [exact INQ1 | cbn [fst]; clear - APQD HMAX1 Hn; intros E; lia]).
  assert (AG34 : forall x : word, aclient (rt_live RT Σ2) (rt_frames RT Σ1) usp1 (bv_unsigned x) -> m4 x = m3 x) by (intros x Hx; exact (PRES4 x Hx)).
  assert (FR4 : rw_cells asegs m4 usp1 (sr_frame s6 s5 s4 s3 s2 s1 s0 ra)).
  { apply (rw_cells_agree_nw asegs m1 m4 _ _ FR1). intros x Hx. cbv beta in Hx. unfold sr_frame in Hx. cbn [cells_size csize Nat.add] in Hx.
    rewrite (AG34 x ltac:(left; unfold usp1, USTACK_TOP in *; clear - Hx NUM; lia)). apply AG13. unfold usp1, USTACK_TOP in *. clear - Hx NUM. lia. }
  assert (DW4 : rw_cells asegs m4 (BM + 8) [C8 (Z_to_bv 64 D)]).
  { apply (rw_cells_agree_nw asegs m2 m4 _ _ (rw_cells_skip m2 BM [C8 (Z_to_bv 64 L)] [C8 (Z_to_bv 64 D)] (proj1 (proj1 (rw_cells_app m2 BM [C8 (Z_to_bv 64 L); C8 (Z_to_bv 64 D)] [C8 (Z_to_bv 64 max); C8 flw]) BMC2)))).
    intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    rewrite (AG34 x ltac:(apply (acl_live _ _ _ BM 32); [exact INBM2 | clear - Hx; lia])).
    apply P3; [apply (acl_live _ _ _ BM 32); [exact INBM1 | clear - Hx; lia] | clear - Hx APQM HLN HL; lia]. }
  destruct (af_client_consts RT AF Σ2 m4 ART4) as (_ & _ & _ & _ & UT4).
  (* [comment removed for export] *)
  pose proof (sr_s3_walk ra (Z_to_bv 64 SITE_sr_scf) sp gp u0 u1 u2 s0 s1 s2 s3 s4 s5 s6 v2 b1 b2 b3 b4 b5 b6 b7 s7 s8 s9 s10 s11 u3 u4 u5 u6 (Z_to_bv 64 L) (Z_to_bv 64 D)
                F4 fc4 m4 lo BM q (Z_to_bv 64 D) HLO1 HLOS SPH ST4 UT4 FR4 DW4 (proj2 (af_acc_live RT AF Σ2 m4 BM 32 ART4 INBM2)) BM0 BMAL BMHI BMLO
                ltac:(clear - Q0 QU Hn; unfold USTACK_TOP in *; lia) MI4) as W3.
  fold usp usp1 in W3.
  cl_lift W3 Hc6' c7 Hc7.
  apply Hk. exists Σ2, q.
  split; [| rewrite LV2, FRS2, SP2, CR2, CG2, LV1, FRS1, SP1, CR1, CG1, (live_remove_cons_ne D q n) by (clear - APQD HMAX1 Hn; intros E; lia); repeat split; try reflexivity; try exact Q0; try exact Q16; exact QU].
  eapply ASTA_conseq; [exact Hc7|]. cbv beta. intros ms (x0 & x1 & x2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & x3 & x4 & x5 & x6 & m5 & -> & MU5 & WM5 & MI5 & ST5 & DW5).
  fold usp in ST5. exists m5. split; [do 16 eexists; reflexivity|].
  assert (E5 : forall x : word, outside [(BM + 8, BM + 16)] (bv_unsigned x) -> m5 x = m4 x) by (intros x Hx; exact (MU5 x Hx)).
  assert (ART5 : ART RT Σ2 m5).
  { apply (af_frame RT AF Σ2 m4 m5 usp1 ART4 ltac:(rewrite SP2, SP1; unfold usp1; clear - NUM; lia)); [| exact WM5].
    intros x Hx. apply E5. cbn [outside]. split; [| exact I]. intros Hin. apply Hx. apply (acl_live _ _ _ BM 32); [exact INBM2 | clear - Hin; lia]. }
  split; [exact (conj ART5 (conj MI5 ST5))|].
  assert (AG05 : forall x : word, aclient (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) usp (bv_unsigned x) -> outside (SR_W BM) (bv_unsigned x) -> m5 x = m x).
  { intros a Ha Ho. unfold SR_W in Ho. cbn [outside] in Ho.
    assert (Ha0 : aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact (live_remove_sub _ _ _ He) | auto | lia]).
    pose proof (newchunk_apart RT AF Σ Σ1 m2 q n usp _ ART2 LV1 FRS1 SP1 ltac:(lia) ltac:(lia) Ha0) as NQ.
    pose proof (removed_apart RT AF Σ m D max usp _ ART0 IND ltac:(lia) Ha) as ND.
    rewrite (E5 a ltac:(cbn [outside]; split; [clear - Ho; lia | exact I])).
    rewrite (AG34 a ltac:(rewrite LV2, LV1, FRS1; apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; rewrite (live_remove_cons_ne D q n) by (clear - APQD HMAX1 Hn; intros E; lia); right; exact He | auto | unfold usp1; clear; lia])).
    rewrite (P3 a ltac:(rewrite LV1, FRS1; apply (aclient_mono _ _ _ _ _ _ _ Ha0); [intros e He; right; exact He | auto | unfold usp1; clear; lia]) ltac:(clear - NQ HL HLN; lia)).
    apply P2; [exact Ha0 | clear - Ho; lia]. }
  split; [exact AG05|].
  split; [apply (cl_env_agree m4 m5 _ canary CLE4); intros a Ha; apply E5; pose proof (client_static_range _ (cl_cell_static _ Ha)); cbn [outside]; unfold SEGTOP_A in *; split; [clear - H BMHI; lia | exact I]|].
  split; [apply (sec_off_agree m4 m5 SEC4); intros a Ha; apply E5; rewrite Ha; cbn [outside]; unfold SEC_INIT; split; [clear - BMHI; lia | exact I]|].
  split; [exact DW5|].
  pose proof (af_acc_live RT AF Σ2 m5 q n ART5 INQ2) as (WR5 & ACC5).
  split; [| exact (conj WR5 ACC5)].
  apply (bytes_at_agree asegs m3 m5 _ _ CPY3). intros x Hx. cbv beta in Hx. rewrite LBS in Hx.
  rewrite (E5 x ltac:(cbn [outside]; split; [clear - Hx APQM HL HLN; lia | exact I])).
  apply AG34. apply (acl_live _ _ _ q n); [exact INQ2 | clear - Hx HLN; lia].
Qed.
End CSecre.

Section CSecreND.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_SM : crypto_secure_malloc_env_stmt RT.

(* [comment removed for export] *)
Definition secre_nd_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BM L max n : Z) (flw : word) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BM -> a1 = Z_to_bv 64 n ->
  In (BM, 32) (rt_live RT Σ) -> BM mod 16 = 0 -> rw_cells asegs m BM [C8 (Z_to_bv 64 L); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 max); C8 flw] ->
  1 <= n <= 0x8000000 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 112 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_sec_alloc_realloc (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) [(SITE_sr_sm, e_sec_alloc_realloc); (SITE_cm_malloc, e_CRYPTO_malloc)] [(SITE_sr_sm, e_CRYPTO_secure_malloc); (SITE_sr_sm, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)] ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost n <= rt_credit RT Σ -> cl_env m lb canary -> sec_off m ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_sec_alloc_realloc m)))
    (fun c => exists (Σ' : rts RT) (q : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 q) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
           /\ cl_env m' (Z_to_bv 8 1) canary /\ sec_off m' /\ wr_at asegs m' q n /\ acc asegs m' q n) c
       /\ rt_live RT Σ' = (q, n) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - mcost n /\ 0 < q /\ q mod 16 = 0 /\ q + n < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem secre_nd_cps : secre_nd_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BM L max n flw outer lb canary
    FDO MST -> -> -> INBM BMAL BMC Hn ART0 MI0 CALL HSTK CTX UWC CGH Hlen Hcr CLE SEC.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 64 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -64).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (HLO1 : lo <= usp - 64) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (af_live_range RT AF Σ m BM 32 ART0 INBM) as (BM0 & BMLO' & _). assert (BMLO : BM + 32 <= lo) by (clear - BMLO' LOW; lia). clear BMLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BM 32 ART0 INBM ltac:(lia)) as BMHI.
  (* [comment removed for export] *)
  pose proof (sr_s0_walk ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BM n
                HLO1 HLOS SPH ST UT SHC ltac:(clear - BM0 BMLO HLO1 SPH; lia) ltac:(clear - Hn; lia) MI0) as W0.
  fold usp in W0. fold usp1 in W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 64 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 64 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  assert (AGL1 : forall a k, a + k <= lo -> agree_on (fun x => a <= x < a + k) m m1) by (intros a' k H x Hx; cbv beta in Hx; apply MU1; cbn [outside]; clear - H Hx HLO1; lia).
  pose proof (cl_env_seg _ m m1 lb canary CLE MU1 ltac:(cl_fp_lia)) as CLE1.
  assert (SEC1 : sec_off m1) by (apply (sec_off_agree m m1 SEC); intros a Ha; apply MU1; cbn [outside]; rewrite Ha; unfold SEC_INIT; split; [clear - HLO1 HLOS; lia | exact I]).
  assert (CO1 : call_ok RT Σ m1 (Z_to_bv 64 usp1) lo).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 4. }
  assert (FRR1 : rw_cells asegs m1 (usp - 16) [C8 s0; C8 ra]).
  { unfold sr_frame in FR1. replace (usp - 16) with (usp1 + Z.of_nat (cells_size [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; unfold usp1; lia).
    exact (rw_cells_skip m1 usp1 [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR1). }
  destruct (cl_chain_call (rt_cg RT Σ) e_sec_alloc_realloc e_CRYPTO_secure_malloc SITE_sr_sm m m1 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH (SITE_sr_sm, e_sec_alloc_realloc) (or_introl eq_refl)) (proj2 CGH (SITE_sr_sm, e_CRYPTO_secure_malloc) (or_introl eq_refl)) UWC AG1 FRR1
              ltac:(rewrite EU1; unfold usp1; lia) SPT) as (CTXa & UWCa).
  (* [comment removed for export] *)
  apply (C_SM Σ PMc (Z_to_bv 64 SITE_sr_sm) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 (Z_to_bv 64 n) (Z_to_bv 64 BUFFER_FILE) (Z_to_bv 64 60) (Z_to_bv 64 n)
           a4 a5 a6 a7 s2 (Z_to_bv 64 BM) s4 s5 (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 n lo (bv_unsigned ra :: outer) lb canary
           FDO MST eq_refl eq_refl Hn ART1 MI1 CO1 ltac:(rewrite EU1; unfold usp1, RT_STACK in *; clear - HSTK; lia)).
  { rewrite (unsigned_lit SITE_sr_sm) by (unfold SITE_sr_sm; lia). exact CTXa. }
  { exact UWCa. }
  { rewrite (unsigned_lit SITE_sr_sm) by (unfold SITE_sr_sm; lia). apply (proj2 CGH). right; left; reflexivity. }
  { apply (cg_has_sub _ _ _ _ _ CGH); intros e He; cbn [In] in He |- *; [right | do 2 right]; exact He. }
  { exact Hlen. } { exact Hcr. } { exact CLE1. } { exact SEC1. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & q & Hc2 & LV1 & FRS1 & SP1 & CR1 & Q0 & Q16 & QU & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & CLE2 & SEC2 & WR2 & ACC2) & Hc2'). clear Hc2.
  destruct RS2 as (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_sr_sm) in Hc2' by (unfold SITE_sr_sm; lia).
  assert (INQ1 : In (q, n) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
  assert (INBM1 : In (BM, 32) (rt_live RT Σ1)) by (rewrite LV1; right; exact INBM).
  assert (P2 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> bv_unsigned x <> G_ALLOW_CUST -> m2 x = m x).
  { intros x Hx HG. rewrite (PRES2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; clear; lia]) ltac:(cbn [outside]; split; [clear - HG; lia | exact I])).
    apply PR1; [exact Hx | exact I]. }
  assert (BMC2 : rw_cells asegs m2 BM [C8 (Z_to_bv 64 L); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 max); C8 flw]).
  { apply (rw_cells_agree_nw asegs m m2 _ _ BMC). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply P2; [apply (acl_live _ _ _ BM 32); [exact INBM | clear - Hx; lia] | unfold G_ALLOW_CUST; clear - Hx BMHI; lia]. }
  assert (FR2 : rw_cells asegs m2 usp1 (sr_frame s6 s5 s4 s3 s2 s1 s0 ra)).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ FR1). intros x Hx. cbv beta in Hx. unfold sr_frame in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply PRES2; [left; unfold usp1, USTACK_TOP in *; clear - Hx NUM; lia|]. cbn [outside]. unfold G_ALLOW_CUST, usp1 in *. split; [clear - Hx HLO1 HLOS; lia | exact I]. }
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & _ & _ & _ & UT2).
  (* [comment removed for export] *)
  pose proof (sr_nd_walk ra (Z_to_bv 64 SITE_sr_sm) sp gp y0 y1 y2 s0 s1 s2 s3 s4 s5 s6 h1 h2 h3 h4 h5 h6 h7 s7 s8 s9 s10 s11 y3 y4 y5 y6 s1 s2 s4 s5 F2 fc2 m2 lo BM q L max flw
                HLO1 HLOS SPH ST2 UT2 FR2 BMC2 (proj2 (af_acc_live RT AF Σ1 m2 BM 32 ART2 INBM1)) BM0 BMAL BMHI BMLO ltac:(clear - Q0 QU Hn; unfold USTACK_TOP in *; lia) MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  apply Hk. exists Σ1, q. split; [| exact (conj LV1 (conj FRS1 (conj SP1 (conj CR1 (conj Q0 (conj Q16 (conj QU CG1)))))))].
  eapply ASTA_conseq; [exact Hc3|]. cbv beta. intros ms (x0 & x1 & x2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & x3 & x4 & x5 & x6 & m3 & -> & MU3 & WM3 & MI3 & ST3).
  fold usp in ST3. exists m3. split; [do 16 eexists; reflexivity|].
  assert (E3 : forall x : word, m3 x = m2 x) by (intros x; apply MU3; exact I).
  assert (ART3 : ART RT Σ1 m3) by (apply (af_frame RT AF Σ1 m2 m3 usp1 ART2 ltac:(rewrite SP1; unfold usp1; clear - NUM; lia)); [intros x _; apply E3 | exact WM3]).
  split; [exact (conj ART3 (conj MI3 (conj (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 WM3)) ST3)))|].
  split; [intros x Hx Ho; rewrite E3; apply P2; [exact Hx | cbn [outside] in Ho; clear - Ho; lia]|].
  split; [apply (cl_env_agree m2 m3 _ canary CLE2); intros a _; apply E3|].
  split; [apply (sec_off_agree m2 m3 SEC2); intros a _; apply E3|].
  split; [exact (wr_at_wm m2 m3 _ _ WR2 WM3)|].
  apply (acc_agree m2 m3 q n ACC2); [clear - Q0; lia|]. intros a Ha. apply E3.
Qed.
End CSecreND.
