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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_W4_kit Fz_env Fz_M_malloc Fz_M_free Fz_M_cleanse Fz_M_clear_free Fz_M_clear_realloc Fz_W1_defs Fz_W1_new Fz_W1_sync Fz_W1_grow Fz_W1_write Fz_W1_writec Fz_M_secure Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition SITE_bf_ccf : Z := 0x249e90.      (* [comment removed for export] *)
Definition SITE_bf_tail : Z := 0x249eb8.     (* [comment removed for export] *)
Definition SITE_mf_mbf : Z := 0x304dfc.      (* [comment removed for export] *)
Definition SITE_mf_free1 : Z := 0x304e30.    (* [comment removed for export] *)
Definition SITE_mf_free2 : Z := 0x304e44.    (* [comment removed for export] *)
Definition SITE_mbf_bmf : Z := 0x305158.
Definition BUF_FILE : Z := 0x73520.          (* [comment removed for export] *)
Definition MEM_FILE : Z := 0xa0ea0.          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition bf_s0_post (sp gp tp t0 t1 t2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' : word) (BM D max lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (j : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_bf_ccf) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 BM) (Z_to_bv 64 D) (Z_to_bv 64 max) (Z_to_bv 64 BUF_FILE) (Z_to_bv 64 49)
                 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_CRYPTO_clear_free) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -32) [CB 8 j; C8 s1'; C8 s0'; C8 ra0] /\ stk asegs m' lo (bv_unsigned sp + -32).

Lemma bf_s0_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BM len D max flw : Z),
  lo <= bv_unsigned sp - 32 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m BM (bufmem_cells len D max (Z_to_bv 64 flw)) -> acc asegs m BM 32 -> 0 < BM -> BM mod 16 = 0 -> 0x10007fff8000 <= BM -> BM + 32 <= lo ->
  0 < D < 2^64 -> 0 <= max < 2^64 -> 0 <= flw < 2^64 -> Z.land flw 1 = 0 -> mem_inv asegs m ->
  evt asegs (bf_s0_post sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ra0 s0' s1' BM D max lo m)
    (MS (mkR ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' (Z_to_bv 64 BM) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_BUF_MEM_free) fc None m (seg_rom asegs)).
Proof.
  intros until flw. intros HLO HLOS SPH ST UT SHC BMC ACCBM BM0 BMAL BMHI BMLO HD HMAX HFL HFL1 MI.
  unfold e_BUF_MEM_free, g_shadow_memory_dynamic_address, bufmem_cells in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 32, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 32, SP)]) by ut_fp_lia. assert (HWS : sh_fp [(SP - 32, SP)]) by sh_fp_lia.
  assert (BMAL8 : BM mod 8 = 0) by (clear - BMAL; Z.div_mod_to_equations; lia).
  th_frame 32%nat [8; 8; 8; 8]%nat ST.
  zstep. do 3 zstep. zstep.
  zstep. if_cases Ka; zify_cond Ka; try (exfalso; rewrite ?unsigned_lit in Ka by lia; lia). try clear Ka.
  zstep.                                                       (* [comment removed for export] *)
  zstep. zstep. zstep.
  zstep. do 3 zstep. zstep. th_if_lit.
  zstep.
  zstep. if_cases Kd; zify_cond Kd; try (exfalso; rewrite ?unsigned_lit in Kd by lia; lia). try clear Kd.
  zstep. do 3 zstep. zstep. th_if_lit.
  zstep. do 3 zstep. zstep. th_if_lit.
  zstep. zstep. zstep. rewrite ?(unsigned_lit flw) by lia. rewrite HFL1. zstep. th_if_lit.
  zstep. zstep. zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold bf_s0_post, SITE_bf_ccf, e_CRYPTO_clear_free, BUF_FILE. apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact FR | assumption].
Qed.

(* [comment removed for export] *)
Definition bf_tail_post (ra0 sp gp tp t0 t1 t2 s0' s1' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (BM lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 BM) (Z_to_bv 64 BUF_FILE) (Z_to_bv 64 51) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_CRYPTO_free) fc None m' (seg_rom asegs)
    /\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma bf_s1_walk : forall ra0 ra1 sp gp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BM : Z) (j : list byte),
  lo <= bv_unsigned sp - 32 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp + -32) -> img_untouched m ->
  rw_cells asegs m (bv_unsigned sp + -32) [CB 8 j; C8 s1'; C8 s0'; C8 ra0] -> 0 <= BM < 2^64 -> mem_inv asegs m ->
  evt asegs (bf_tail_post ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc BM lo m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 BM) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_bf_ccf) fc None m (seg_rom asegs)).
Proof.
  intros until j. intros HLO HLOS SPH ST UT FR HBM MI.
  unfold SITE_bf_ccf in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 (SP + -32)) = SP + -32) by (apply unsigned_lit; lia).
  zstep.
  zstep. zstep. zstep. zstep.
  zstep. zstep. zstep. zstep. th_release FR SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold bf_tail_post, e_CRYPTO_free, BUF_FILE. apply evt_done. eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
Definition bf_nd_post (ra0 sp gp tp t0 t1 t2 s0' s1' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (BM lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 BM) (Z_to_bv 64 BUF_FILE) (Z_to_bv 64 51) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_CRYPTO_free) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma bf_nd_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BM len max flw : Z),
  lo <= bv_unsigned sp - 32 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m BM (bufmem_cells len 0 max (Z_to_bv 64 flw)) -> acc asegs m BM 32 -> 0 < BM -> BM mod 16 = 0 -> 0x10007fff8000 <= BM -> BM + 32 <= lo ->
  mem_inv asegs m ->
  evt asegs (bf_nd_post ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc BM lo m)
    (MS (mkR ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' (Z_to_bv 64 BM) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_BUF_MEM_free) fc None m (seg_rom asegs)).
Proof.
  intros until flw. intros HLO HLOS SPH ST UT SHC BMC ACCBM BM0 BMAL BMHI BMLO MI.
  unfold e_BUF_MEM_free, g_shadow_memory_dynamic_address, bufmem_cells in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 32, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 32, SP)]) by ut_fp_lia. assert (HWS : sh_fp [(SP - 32, SP)]) by sh_fp_lia.
  assert (BMAL8 : BM mod 8 = 0) by (clear - BMAL; Z.div_mod_to_equations; lia).
  th_frame 32%nat [8; 8; 8; 8]%nat ST.
  zstep. do 3 zstep. zstep.
  zstep. if_cases Ka; zify_cond Ka; try (exfalso; rewrite ?unsigned_lit in Ka by lia; lia). try clear Ka.
  zstep.                                                       (* [comment removed for export] *)
  zstep. zstep. zstep.
  zstep. do 3 zstep. zstep. th_if_lit.
  zstep.
  zstep. th_if_lit.
  zstep. zstep. zstep. zstep.
  zstep. zstep. zstep. zstep. th_release FR SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold bf_nd_post, e_CRYPTO_free, BUF_FILE. apply evt_done. eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
Definition mbf_s0_post (ra0 sp gp tp t0 t1 t2 s0' s1' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (BI BB BM fl lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a1 a2 a3 a4 : word) (j : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_mbf_bmf) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 1) (Z_to_bv 64 BM) a1 a2 a3 a4
                 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_BUF_MEM_free) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -32) [CB 8 j; C8 s1'; C8 s0'; C8 ra0] /\ stk asegs m' lo (bv_unsigned sp + -32).

Lemma mbf_s0_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BI BB BM R fl : Z) (rrw numw padw : word),
  lo <= bv_unsigned sp - 32 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  rw_cells asegs m (BI + 49) [C1 (Z_to_bv 8 (fl ≫ 8))] ->
  acc asegs m BI 128 -> 0 < BI -> BI mod 16 = 0 -> 0x10007fff8000 <= BI -> BI + 128 <= lo ->
  rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] -> acc asegs m BB 16 -> 0 < BB -> BB mod 16 = 0 -> 0x10007fff8000 <= BB -> BB + 16 <= lo ->
  0 <= BM < 2^64 -> mem_inv asegs m ->
  evt asegs (mbf_s0_post ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc BI BB BM fl lo m)
    (MS (mkR ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' (Z_to_bv 64 BI) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_mem_buf_free) fc None m (seg_rom asegs)).
Proof.
  intros until padw. intros HLO HLOS SPH ST UT SHC BW FLOK FB1 ACCBI BI0 BIAL BIHI BILO BBC ACCBB BB0 BBAL BBHI BBLO HBM MI.
  unfold e_mem_buf_free, g_shadow_memory_dynamic_address, bio_w1_cells in *. destruct FLOK as (FLR & FL512).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 32, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 32, SP)]) by ut_fp_lia. assert (HWS : sh_fp [(SP - 32, SP)]) by sh_fp_lia.
  assert (BIAL8 : BI mod 8 = 0) by (clear - BIAL; Z.div_mod_to_equations; lia). assert (BBAL8 : BB mod 8 = 0) by (clear - BBAL; Z.div_mod_to_equations; lia).
  th_frame 32%nat [8; 8; 8; 8]%nat ST.
  zstep. do 3 zstep. zstep.
  zstep. if_cases Ka; zify_cond Ka; try (exfalso; rewrite ?unsigned_lit in Ka by lia; lia). try clear Ka.
  zstep. zstep. zstep.
  zstep. do 3 zstep. zstep. th_if_lit.
  zstep. zstep. zstep. th_if_lit.
  zstep. do 3 zstep. zstep. th_if_lit.
  zstep. zstep. th_if_lit.
  zstep. do 3 zstep. zstep. th_if_lit.
  zstep. zstep. if_cases Kb; zify_cond Kb; try (exfalso; rewrite ?unsigned_lit in Kb by lia; lia). try clear Kb.
  do 3 zstep. zstep. th_if_lit.
  zstep. zstep. zstep. zstep. zstep. zstep. th_if_lit.
  zstep. cbv beta. rewrite (Z_to_bv_unsigned 8 (fl ≫ 8)). unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  zstep. rewrite (fl_rdonly_byte fl) by lia. zstep. th_if_lit.
  zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold mbf_s0_post, SITE_mbf_bmf, e_BUF_MEM_free. apply evt_done. do 6 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact FR | assumption].
Qed.

Definition mbf_s1_post (ra0 sp gp tp t0 t1 t2 s0' s1' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms =>
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra0) fc None m (seg_rom asegs)
    /\ stk asegs m lo (bv_unsigned sp).

Lemma mbf_s1_walk : forall ra0 ra1 sp gp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (j : list byte),
  lo <= bv_unsigned sp - 32 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp + -32) -> img_untouched m ->
  rw_cells asegs m (bv_unsigned sp + -32) [CB 8 j; C8 s1'; C8 s0'; C8 ra0] -> mem_inv asegs m ->
  evt asegs (mbf_s1_post ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_mbf_bmf) fc None m (seg_rom asegs)).
Proof.
  intros until j. intros HLO HLOS SPH ST UT FR MI.
  unfold SITE_mbf_bmf in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 (SP + -32)) = SP + -32) by (apply unsigned_lit; lia).
  zstep.
  zstep. zstep. zstep. zstep. zstep. th_release FR SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold mbf_s1_post. apply evt_done. split; [reflexivity | assumption].
Qed.

(* [comment removed for export] *)
Definition mf_s0_post (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' : word) (BI BB lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a1 a2 : word) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_mf_mbf) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 BB) (Z_to_bv 64 BI) a1 a2 a3 a4
                 a5 a6 a7 (Z_to_bv 64 0x7fff8000) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_mem_buf_free) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -32) [C8 s2'; C8 s1'; C8 s0'; C8 ra0] /\ stk asegs m' lo (bv_unsigned sp + -32).

Lemma mf_s0_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a1 a2 a3 a4 a5 a6 a7 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BI BB fl : Z) (rrw numw padw : word),
  lo <= bv_unsigned sp - 32 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB)) ->
  acc asegs m BI 128 -> 0 < BI -> BI mod 16 = 0 -> 0x10007fff8000 <= BI -> BI + 128 <= lo -> 0 <= BB < 2^64 -> mem_inv asegs m ->
  evt asegs (mf_s0_post sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ra0 s0' s1' s2' BI BB lo m)
    (MS (mkR ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' (Z_to_bv 64 BI) a1 a2 a3 a4 a5 a6 a7 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_mem_free) fc None m (seg_rom asegs)).
Proof.
  intros until padw. intros HLO HLOS SPH ST UT SHC BW ACCBI BI0 BIAL BIHI BILO HBB MI.
  unfold e_mem_free, g_shadow_memory_dynamic_address, bio_w1_cells in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 32, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 32, SP)]) by ut_fp_lia. assert (HWS : sh_fp [(SP - 32, SP)]) by sh_fp_lia.
  assert (BIAL8 : BI mod 8 = 0) by (clear - BIAL; Z.div_mod_to_equations; lia).
  th_frame 32%nat [8; 8; 8; 8]%nat ST.
  zstep. do 4 zstep. zstep.
  zstep. if_cases Ka; zify_cond Ka; try (exfalso; rewrite ?unsigned_lit in Ka by lia; lia). try clear Ka.
  zstep. zstep. zstep.
  zstep. do 3 zstep. zstep. th_if_lit.
  zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold mf_s0_post, SITE_mf_mbf, e_mem_buf_free. apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact FR | assumption].
Qed.

(* [comment removed for export] *)
Definition mf_s1_post (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (BB R : Z) (m : mem) : machine_state -> Prop :=
  fun ms =>
    ms = MS (mkR (Z_to_bv 64 SITE_mf_free1) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 BB) (Z_to_bv 64 R) (Z_to_bv 64 MEM_FILE) (Z_to_bv 64 153) a3 a4
                 a5 a6 a7 (Z_to_bv 64 MEM_FILE) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_CRYPTO_free) fc None m (seg_rom asegs).

Lemma mf_s1_walk : forall ra1 sp gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (BB BM R : Z),
  bv_unsigned sp <= 2^47 -> img_untouched m ->
  rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] -> acc asegs m BB 16 -> 0 < BB -> BB mod 16 = 0 -> 0x10007fff8000 <= BB -> BB + 16 <= 2^47 ->
  0 <= R < 2^64 -> mem_inv asegs m -> a0 = Z_to_bv 64 1 ->
  evt asegs (mf_s1_post sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc BB R m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 BB) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 0x7fff8000) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_mf_mbf) fc None m (seg_rom asegs)).
Proof.
  intros until R. intros SPH UT BBC ACCBB BB0 BBAL BBHI BBU HR MI HA0. subst a0.
  unfold SITE_mf_mbf in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (BBAL8 : BB mod 8 = 0) by (clear - BBAL; Z.div_mod_to_equations; lia).
  zstep. th_if_lit.                                            (* [comment removed for export] *)
  zstep. do 3 zstep. zstep. th_if_lit.
  zstep. zstep. zstep. zstep. zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold mf_s1_post, SITE_mf_free1, e_CRYPTO_free, MEM_FILE. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Definition mf_s2_post (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (BB : Z) (m : mem) : machine_state -> Prop :=
  fun ms =>
    ms = MS (mkR (Z_to_bv 64 SITE_mf_free2) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 BB) (Z_to_bv 64 BB) (Z_to_bv 64 MEM_FILE) (Z_to_bv 64 154) a3 a4
                 a5 a6 a7 (Z_to_bv 64 MEM_FILE) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_CRYPTO_free) fc None m (seg_rom asegs).

Lemma mf_s2_walk : forall ra1 sp gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (BB : Z),
  bv_unsigned sp <= 2^47 -> 0 <= BB < 2^64 -> mem_inv asegs m ->
  evt asegs (mf_s2_post sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc BB m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 BB) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 MEM_FILE) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_mf_free1) fc None m (seg_rom asegs)).
Proof.
  intros until BB. intros SPH HBB MI.
  unfold SITE_mf_free1, MEM_FILE in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold mf_s2_post, SITE_mf_free2, e_CRYPTO_free, MEM_FILE. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Definition mf_s3_post (ra0 sp gp tp t0 t1 t2 s0' s1' s2' a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma mf_s3_walk : forall ra0 ra1 sp gp t0 t1 t2 s0' s1' s2' a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (s1x s2x : word)
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  lo <= bv_unsigned sp - 32 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp + -32) -> img_untouched m ->
  rw_cells asegs m (bv_unsigned sp + -32) [C8 s2'; C8 s1'; C8 s0'; C8 ra0] -> mem_inv asegs m ->
  evt asegs (mf_s3_post ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' s2' a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1x a0 a1 a2 a3 a4 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_mf_free2) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros HLO HLOS SPH ST UT FR MI.
  unfold SITE_mf_free2 in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 (SP + -32)) = SP + -32) by (apply unsigned_lit; lia).
  zstep.
  zstep. zstep. zstep. zstep. zstep. th_release FR SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold mf_s3_post. apply evt_done. eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
Definition bf_sec_post (sp gp tp t0 t1 t2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' : word) (BM D max lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (j : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_bf_tail) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 BM) (Z_to_bv 64 D) (Z_to_bv 64 max) (Z_to_bv 64 BUF_FILE) (Z_to_bv 64 47)
                 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_CRYPTO_secure_clear_free) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -32) [CB 8 j; C8 s1'; C8 s0'; C8 ra0] /\ stk asegs m' lo (bv_unsigned sp + -32).

Lemma bf_sec_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BM len D max flw : Z),
  lo <= bv_unsigned sp - 32 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m BM (bufmem_cells len D max (Z_to_bv 64 flw)) -> acc asegs m BM 32 -> 0 < BM -> BM mod 16 = 0 -> 0x10007fff8000 <= BM -> BM + 32 <= lo ->
  0 < D < 2^64 -> 0 <= max < 2^64 -> 0 <= flw < 2^64 -> Z.land flw 1 = 1 -> mem_inv asegs m ->
  evt asegs (bf_sec_post sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ra0 s0' s1' BM D max lo m)
    (MS (mkR ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' (Z_to_bv 64 BM) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_BUF_MEM_free) fc None m (seg_rom asegs)).
Proof.
  intros until flw. intros HLO HLOS SPH ST UT SHC BMC ACCBM BM0 BMAL BMHI BMLO HD HMAX HFL HFL1 MI.
  unfold e_BUF_MEM_free, g_shadow_memory_dynamic_address, bufmem_cells in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 32, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 32, SP)]) by ut_fp_lia. assert (HWS : sh_fp [(SP - 32, SP)]) by sh_fp_lia.
  assert (BMAL8 : BM mod 8 = 0) by (clear - BMAL; Z.div_mod_to_equations; lia).
  th_frame 32%nat [8; 8; 8; 8]%nat ST.
  zstep. do 3 zstep. zstep.
  zstep. if_cases Ka; zify_cond Ka; try (exfalso; rewrite ?unsigned_lit in Ka by lia; lia). try clear Ka.
  zstep.                                                       (* [comment removed for export] *)
  zstep. zstep. zstep.
  zstep. do 3 zstep. zstep. th_if_lit.
  zstep.
  zstep. if_cases Kd; zify_cond Kd; try (exfalso; rewrite ?unsigned_lit in Kd by lia; lia). try clear Kd.
  zstep. do 3 zstep. zstep. th_if_lit.
  zstep. do 3 zstep. zstep. th_if_lit.
  zstep. zstep. zstep. rewrite ?(unsigned_lit flw) by lia. rewrite HFL1. zstep. th_if_lit.
  zstep. zstep. zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold bf_sec_post, SITE_bf_tail, e_CRYPTO_secure_clear_free, BUF_FILE. apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact FR | assumption].
Qed.

(* [comment removed for export] *)
Lemma bf_tail_walk : forall ra0 ra1 sp gp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BM : Z) (j : list byte),
  lo <= bv_unsigned sp - 32 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp + -32) -> img_untouched m ->
  rw_cells asegs m (bv_unsigned sp + -32) [CB 8 j; C8 s1'; C8 s0'; C8 ra0] -> 0 <= BM < 2^64 -> mem_inv asegs m ->
  evt asegs (bf_tail_post ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc BM lo m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 BM) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_bf_tail) fc None m (seg_rom asegs)).
Proof.
  intros until j. intros HLO HLOS SPH ST UT FR HBM MI.
  unfold SITE_bf_tail in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 (SP + -32)) = SP + -32) by (apply unsigned_lit; lia).
  zstep. zstep. zstep. zstep.
  zstep. zstep. zstep. zstep. th_release FR SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold bf_tail_post, e_CRYPTO_free, BUF_FILE. apply evt_done. eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

Section CFree.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_FR : crypto_free_env_stmt RT.
Hypothesis C_CCF : crypto_clear_free_env_stmt RT.

Definition BF_SITES : list (Z * Z) := [(SITE_bf_ccf, e_BUF_MEM_free)].
Definition BF_CALLS : list (Z * Z) := [(SITE_bf_ccf, e_CRYPTO_clear_free); (SITE_bf_ccf, e_free)].

(* [comment removed for export] *)
Definition free_post (Σ : rts RT) PMc (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (lo : Z) (m : mem) (lb : byte) (canary : word)
    (live' : list (Z * Z)) : config -> Prop :=
  fun c => exists (Σ' : rts RT) (v : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
           /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres (rt_live RT Σ') (rt_frames RT Σ) (bv_unsigned sp) m m'
           /\ cl_env m' lb canary) c
       /\ rt_live RT Σ' = live' /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_cg RT Σ' = rt_cg RT Σ.

(* [comment removed for export] *)
Definition bm_data_opt (live : list (Z * Z)) (BM D max : Z) : Prop := D = 0 \/ (In (D, max) live /\ D <> BM /\ 1 <= max < 2 ^ 40).

Lemma live_remove_0 : forall (Σ : rts RT) (m : mem), ART RT Σ m -> live_remove 0 (rt_live RT Σ) = rt_live RT Σ.
Proof.
  intros Σ m HA. apply live_remove_notin. intros (p & n) Hin. cbn [fst]. pose proof (af_live_range RT AF Σ m p n HA Hin) as (H & _). lia.
Qed.

(* [comment removed for export] *)
Definition buf_mem_free_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BM D len max flw : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BM ->
  In (BM, 32) (rt_live RT Σ) -> BM mod 16 = 0 -> rw_cells asegs m BM (bufmem_cells len D max (Z_to_bv 64 flw)) -> 0 <= flw < 2 ^ 64 -> (D = 0 \/ Z.land flw 1 = 0) ->
  bm_data_opt (rt_live RT Σ) BM D max -> 0 <= max < 2 ^ 40 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 80 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_BUF_MEM_free (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) BF_SITES BF_CALLS ->
  In (bv_unsigned ra, e_CRYPTO_free) (cg_call (rt_cg RT Σ)) -> In (bv_unsigned ra, e_free) (cg_call (rt_cg RT Σ)) ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_BUF_MEM_free m)))
    (free_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m lb canary (live_remove BM (live_remove D (rt_live RT Σ)))).

Theorem buf_mem_free_cps : buf_mem_free_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BM D len max flw outer lb canary
    FDO MST -> -> INBM BMAL BMC HFL HFL1 DOPT HMAX0 ART0 MI0 CALL HSTK CTX UWC CGH TL1 TL2 CLE.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 32 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -32).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (HLO1 : lo <= usp - 32) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (af_live_range RT AF Σ m BM 32 ART0 INBM) as (BM0 & BMLO' & _). assert (BMLO : BM + 32 <= lo) by (clear - BMLO' LOW; lia). clear BMLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BM 32 ART0 INBM ltac:(lia)) as BMHI. pose proof (proj2 (af_acc_live RT AF Σ m BM 32 ART0 INBM)) as ACCBM.
  destruct DOPT as [-> | (IND & NDBM & HMAX)].
  2: assert (HFL1' : Z.land flw 1 = 0) by (destruct HFL1 as [E|E]; [exfalso; pose proof (af_live_range RT AF Σ m D max ART0 IND) as (D0' & _); clear - E D0'; lia| exact E]).
  { (* [comment removed for export] *)
    pose proof (bf_nd_walk ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BM len max flw
                  HLO1 HLOS SPH ST UT SHC BMC ACCBM BM0 BMAL BMHI BMLO MI0) as W0.
    fold usp in W0.
    cl_lift W0 HA c1 Hc1.
    destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & ST1) & Hc1'). clear Hc1. fold usp in MU1, ST1, Hc1'.
    pose proof (cl_seg_ART RT AF Σ m m1 usp 32 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
    pose proof (cl_seg_pres RT AF Σ m m1 usp 32 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
    assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
    pose proof (cl_env_seg _ m m1 lb canary CLE MU1 ltac:(cl_fp_lia)) as CLE1.
    assert (CO1 : call_ok RT Σ m1 sp lo) by exact (conj ST1 (conj LOW (conj LOR (conj SPT SPA)))).
    apply (C_FR Σ PMc ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 (Z_to_bv 64 BM) (Z_to_bv 64 BUF_FILE) (Z_to_bv 64 51) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m1 BM 32 lo outer lb canary FDO MST eq_refl eq_refl INBM ART1 MI1 CO1 (conj TL1 (proj2 CTX)) (uw_chain_agree outer m m1 sp s0 UWC AG1) TL2 CLE1).
    { exact Hc1'. }
    clear Hc1'. intros c4 (Σ2 & v2 & Hc4 & LV2 & FRS2 & SP2 & CR2 & CG2).
    apply Hk. unfold free_post. exists Σ2, v2.
    split; [| rewrite LV2, FRS2, SP2, CR2, CG2, (live_remove_0 Σ m ART0); repeat split; reflexivity].
    eapply ASTA_conseq; [exact Hc4|]. cbv beta. intros ms (m4 & RS4 & RAF4 & PRES4 & CLE4). exists m4.
    split; [exact RS4|]. split; [exact RAF4|]. split; [| exact CLE4].
    intros x Hx. rewrite (PRES4 x Hx). apply PR1; [| exact I].
    apply (aclient_mono _ _ _ _ _ _ _ Hx); [rewrite LV2; intros e He; exact (live_remove_sub _ _ _ He) | auto | clear; lia]. }
  pose proof (af_live_range RT AF Σ m D max ART0 IND) as (D0 & DLO' & _). assert (DLO : D + max <= lo) by (clear - DLO' LOW; lia). clear DLO'.
  (* [comment removed for export] *)
  pose proof (bf_s0_walk ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BM len D max flw
                HLO1 HLOS SPH ST UT SHC BMC ACCBM BM0 BMAL BMHI BMLO ltac:(clear - D0 DLO HLO1 SPH HMAX; lia) ltac:(clear - HMAX; lia) HFL HFL1' MI0) as W0.
  fold usp in W0. fold usp1 in W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (j & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 32 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 32 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  pose proof (cl_env_seg _ m m1 lb canary CLE MU1 ltac:(cl_fp_lia)) as CLE1.
  assert (CO1 : call_ok RT Σ m1 (Z_to_bv 64 usp1) lo).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 2. }
  assert (FRR1 : rw_cells asegs m1 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp1 + Z.of_nat (cells_size [CB 8 j; C8 s1])) by (cbn [cells_size csize Nat.add]; unfold usp1; lia).
    exact (rw_cells_skip m1 usp1 [CB 8 j; C8 s1] [C8 s0; C8 ra] FR1). }
  destruct (cl_chain_call (rt_cg RT Σ) e_BUF_MEM_free e_CRYPTO_clear_free SITE_bf_ccf m m1 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH _ ltac:(left; reflexivity)) (proj2 CGH _ ltac:(left; reflexivity)) UWC AG1 FRR1 ltac:(rewrite EU1; unfold usp1; lia) SPT) as (CTX2 & UWC2).
  (* [comment removed for export] *)
  apply (C_CCF Σ PMc (Z_to_bv 64 SITE_bf_ccf) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 BM) (Z_to_bv 64 D) (Z_to_bv 64 max) (Z_to_bv 64 BUF_FILE) (Z_to_bv 64 49)
           a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 D max max lo (bv_unsigned ra :: outer) lb canary
           FDO MST eq_refl eq_refl eq_refl IND ltac:(clear - HMAX; lia) ltac:(clear - HMAX; lia) ART1 MI1 CO1 ltac:(rewrite EU1; unfold usp1, RT_STACK in *; clear - HSTK; lia)).
  { rewrite (unsigned_lit SITE_bf_ccf) by (unfold SITE_bf_ccf; lia). exact CTX2. }
  { exact UWC2. }
  { rewrite (unsigned_lit SITE_bf_ccf) by (unfold SITE_bf_ccf; lia). apply (proj2 CGH). right; left; reflexivity. }
  { exact CLE1. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & v1 & Hc2 & LV1 & FRS1 & SP1 & CR1 & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & ST2) & PRES2 & CLE2) & Hc2'). clear Hc2.
  destruct RS2 as (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_bf_ccf) in Hc2' by (unfold SITE_bf_ccf; lia).
  assert (AG12 : forall x : word, usp1 <= bv_unsigned x < USTACK_TOP -> m2 x = m1 x) by (intros x Hx; apply PRES2; left; exact Hx).
  assert (FR2 : rw_cells asegs m2 usp1 [CB 8 j; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ FR1). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add length] in Hx. apply AG12. unfold usp1, USTACK_TOP in *. clear - Hx NUM. lia. }
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & _ & _ & _ & UT2).
  (* [comment removed for export] *)
  pose proof (bf_s1_walk ra (Z_to_bv 64 SITE_bf_ccf) sp gp y0 y1 y2 s0 s1 v1 h1 h2 h3 h4 h5 h6 h7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6 F2 fc2 m2 lo BM j
                HLO1 HLOS SPH ST2 UT2 FR2 ltac:(clear - BM0 BMLO HLO1 SPH; lia) MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (m3 & -> & MU3 & WM3 & MI3 & ST3) & Hc3'). clear Hc3. fold usp in ST3.
  assert (E3 : forall x : word, m3 x = m2 x) by (intros x; apply MU3; exact I).
  assert (ART3 : ART RT Σ1 m3) by (apply (af_frame RT AF Σ1 m2 m3 usp1 ART2 ltac:(rewrite SP1; unfold usp1; clear - NUM; lia)); [intros x _; apply E3 | exact WM3]).
  assert (INBM1 : In (BM, 32) (rt_live RT Σ1)) by (rewrite LV1; apply live_remove_keep; [exact INBM | cbn [fst]; intros E; exact (NDBM (eq_sym E))]).
  assert (CO3 : call_ok RT Σ1 m3 sp lo) by (unfold call_ok; rewrite SP1; exact (conj ST3 (conj LOW (conj LOR (conj SPT SPA))))).
  assert (UWC3 : uw_chain m3 sp s0 outer).
  { apply (uw_chain_agree outer m m3 sp s0 UWC). intros x Hx. cbv beta in Hx. rewrite E3. rewrite (AG12 x ltac:(unfold usp1; clear - Hx; lia)). exact (AG1 x Hx). }
  pose proof (cl_env_agree m2 m3 lb canary CLE2 ltac:(intros a _; apply E3)) as CLE3.
  (* [comment removed for export] *)
  apply (C_FR Σ1 PMc ra sp gp (Z_to_bv 64 0xba3ef0) y0 y1 y2 s0 s1 (Z_to_bv 64 BM) (Z_to_bv 64 BUF_FILE) (Z_to_bv 64 51) h3 h4 h5 h6 h7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6
           F2 fc2 m3 BM 32 lo outer lb canary FDO MST eq_refl eq_refl INBM1 ART3 MI3 CO3 ltac:(rewrite CG1; exact (conj TL1 (proj2 CTX))) UWC3 ltac:(rewrite CG1; exact TL2) CLE3).
  { exact Hc3'. }
  clear Hc3'. intros c4 (Σ2 & v2 & Hc4 & LV2 & FRS2 & SP2 & CR2 & CG2).
  apply Hk. unfold free_post. exists Σ2, v2.
  split; [| rewrite LV2, FRS2, SP2, CR2, CG2, LV1, FRS1, SP1, CR1, CG1; repeat split; reflexivity].
  eapply ASTA_conseq; [exact Hc4|]. cbv beta. intros ms (m4 & RS4 & RAF4 & PRES4 & CLE4). exists m4.
  split; [exact RS4|]. split; [exact RAF4|]. split; [| exact CLE4].
  intros x Hx. rewrite (PRES4 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | rewrite FRS1; auto | clear; lia])). rewrite E3.
  assert (Hx1 : aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x)).
  { apply (aclient_mono _ _ _ _ _ _ _ Hx); [| auto | clear; lia]. rewrite LV2, LV1. intros e He. exact (live_remove_sub _ _ _ (live_remove_sub _ _ _ He)). }
  rewrite (PRES2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [rewrite LV2; intros e He; exact (live_remove_sub _ _ _ He) | auto | unfold usp1; clear; lia])).
  apply PR1; [exact Hx1 | exact I].
Qed.

Definition MF_SITES : list (Z * Z) :=
  [(SITE_mf_mbf, e_mem_free); (SITE_mf_free1, e_mem_free); (SITE_mf_free2, e_mem_free); (SITE_mbf_bmf, e_mem_buf_free)] ++ BF_SITES.
Definition MF_CALLS : list (Z * Z) :=
  [(SITE_mf_mbf, e_mem_buf_free); (SITE_mf_free1, e_CRYPTO_free); (SITE_mf_free1, e_free); (SITE_mf_free2, e_CRYPTO_free); (SITE_mf_free2, e_free);
   (SITE_mbf_bmf, e_BUF_MEM_free); (SITE_mbf_bmf, e_CRYPTO_free); (SITE_mbf_bmf, e_free)] ++ BF_CALLS.

(* [comment removed for export] *)
Definition mem_free_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BI BB BM R D len max fl flw : Z) (rrw numw padw : word) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BI ->
  In (BI, 128) (rt_live RT Σ) -> BI mod 16 = 0 -> rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  In (BB, 16) (rt_live RT Σ) -> BB mod 16 = 0 -> rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] ->
  In (BM, 32) (rt_live RT Σ) -> BM mod 16 = 0 -> rw_cells asegs m BM (bufmem_cells len D max (Z_to_bv 64 flw)) -> 0 <= flw < 2 ^ 64 -> (D = 0 \/ Z.land flw 1 = 0) ->
  In (R, 32) (rt_live RT Σ) -> BM <> R -> BB <> BM -> BB <> R -> D <> BB -> D <> R ->
  bm_data_opt (rt_live RT Σ) BM D max -> 0 <= max < 2 ^ 40 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 144 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_mem_free (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) MF_SITES MF_CALLS ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_mem_free m)))
    (free_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m lb canary (live_remove BB (live_remove R (live_remove BM (live_remove D (rt_live RT Σ)))))).

Theorem mem_free_cps : mem_free_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R D len max fl flw rrw numw padw outer lb canary
    FDO MST -> -> INBI BIAL BW FLOK INBB BBAL BBC INBM BMAL BMC HFL HFL1 INR NMR NBM NBR NDBB NDR DOPT HMAX0 ART0 MI0 CALL HSTK CTX UWC CGH CLE.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 64 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -32). set (usp2 := usp1 + -32).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (EU2 : bv_unsigned (Z_to_bv 64 usp2) = usp2) by (apply unsigned_lit; unfold usp2, usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (HLO1 : lo <= usp - 32) by (clear - HSTK; unfold RT_STACK in *; lia). assert (HLO2 : lo <= usp1 - 32) by (clear - HSTK; unfold usp1, RT_STACK in *; lia).
  pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia). assert (SPH1 : usp1 <= 2 ^ 47) by (clear - NUM; unfold usp1, USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (af_live_range RT AF Σ m BI 128 ART0 INBI) as (BI0 & BILO' & _). assert (BILO : BI + 128 <= lo) by (clear - BILO' LOW; lia). clear BILO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BI 128 ART0 INBI ltac:(lia)) as BIHI. pose proof (proj2 (af_acc_live RT AF Σ m BI 128 ART0 INBI)) as ACCBI.
  pose proof (af_live_range RT AF Σ m BB 16 ART0 INBB) as (BB0 & BBLO' & _). assert (BBLO : BB + 16 <= lo) by (clear - BBLO' LOW; lia). clear BBLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BB 16 ART0 INBB ltac:(lia)) as BBHI. pose proof (proj2 (af_acc_live RT AF Σ m BB 16 ART0 INBB)) as ACCBB.
  pose proof (af_live_range RT AF Σ m BM 32 ART0 INBM) as (BM0 & BMLO' & _). assert (BMLO : BM + 32 <= lo) by (clear - BMLO' LOW; lia). clear BMLO'.
  pose proof (af_live_range RT AF Σ m R 32 ART0 INR) as (R0 & RLO' & _). assert (RLO : R + 32 <= lo) by (clear - RLO' LOW; lia). clear RLO'.
  pose proof (bio_flags_byte1 m BI _ _ fl rrw numw padw _ ltac:(destruct FLOK; lia) BW) as FB1.
  assert (ES : bv_unsigned sp = usp) by reflexivity.
  (* [comment removed for export] *)
  pose proof (mf_s0_walk ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB fl rrw numw padw
                HLO1 HLOS SPH ST UT SHC BW ACCBI BI0 BIAL BIHI BILO ltac:(clear - BB0 BBLO HLO1 SPH; lia) MI0) as W0.
  fold usp in W0. fold usp1 in W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (x1 & x2 & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 32 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 32 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  assert (AGL1 : forall a n, a + n <= lo -> agree_on (fun x => a <= x < a + n) m m1) by (intros a' n H x Hx; cbv beta in Hx; apply MU1; cbn [outside]; clear - H Hx HLO1; lia).
  pose proof (cl_env_seg _ m m1 lb canary CLE MU1 ltac:(cl_fp_lia)) as CLE1.
  destruct (af_client_consts RT AF Σ m1 ART1) as (_ & SHC1 & _ & _ & UT1).
  assert (BW1 : rw_cells asegs m1 (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB))).
  { apply (rw_cells_agree asegs m m1 _ _ BW); [apply AGL1; unfold bio_w1_cells; cbn [cells_size csize Nat.add]; clear - BILO; lia | exact WM1]. }
  assert (FB11 : rw_cells asegs m1 (BI + 49) [C1 (Z_to_bv 8 (fl ≫ 8))]).
  { apply (rw_cells_agree asegs m m1 _ _ FB1); [apply AGL1; cbn [cells_size csize Nat.add]; clear - BILO; lia | exact WM1]. }
  assert (BBC1 : rw_cells asegs m1 BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)]).
  { apply (rw_cells_agree asegs m m1 _ _ BBC); [apply AGL1; cbn [cells_size csize Nat.add]; exact BBLO | exact WM1]. }
  assert (BMC1 : rw_cells asegs m1 BM (bufmem_cells len D max (Z_to_bv 64 flw))).
  { apply (rw_cells_agree asegs m m1 _ _ BMC); [apply AGL1; unfold bufmem_cells; cbn [cells_size csize Nat.add]; exact BMLO | exact WM1]. }
  assert (FRR1 : rw_cells asegs m1 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp1 + Z.of_nat (cells_size [C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; unfold usp1; lia).
    exact (rw_cells_skip m1 usp1 [C8 s2; C8 s1] [C8 s0; C8 ra] FR1). }
  destruct (cl_chain_call (rt_cg RT Σ) e_mem_free e_mem_buf_free SITE_mf_mbf m m1 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH (SITE_mf_mbf, e_mem_free) ltac:(cbn; tauto)) (proj2 CGH (SITE_mf_mbf, e_mem_buf_free) ltac:(cbn; tauto)) UWC AG1 FRR1 ltac:(rewrite EU1; unfold usp1; lia) SPT) as (CTXa & UWCa).
  assert (STK1 : stk asegs m1 lo (bv_unsigned (Z_to_bv 64 usp1))) by (rewrite EU1; exact ST1).
  (* [comment removed for export] *)
  pose proof (mbf_s0_walk (Z_to_bv 64 SITE_mf_mbf) (Z_to_bv 64 usp1) gp t0 t1 t2 sp (Z_to_bv 64 BB) x1 x2 a3 a4 a5 a6 a7 (Z_to_bv 64 0x7fff8000) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m1 lo BI BB BM R fl rrw numw padw
                ltac:(rewrite EU1; exact HLO2) HLOS ltac:(rewrite EU1; exact SPH1) STK1 UT1 SHC1 BW1 FLOK FB11
                (proj2 (af_acc_live RT AF Σ m1 BI 128 ART1 INBI)) BI0 BIAL BIHI BILO BBC1 (proj2 (af_acc_live RT AF Σ m1 BB 16 ART1 INBB)) BB0 BBAL BBHI BBLO
                ltac:(clear - BM0 BMLO HLO1 SPH; lia) MI1) as W1.
  unfold mbf_s0_post in W1. rewrite EU1 in W1. fold usp2 in W1.
  cl_lift W1 Hc1' c2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (z1 & z2 & z3 & z4 & j2 & m2 & -> & MU2 & WM2 & MI2 & FR2 & ST2) & Hc2'). clear Hc2.
  pose proof (cl_seg_ART RT AF Σ m1 m2 usp1 32 [] ART1 ltac:(unfold usp1; lia) ltac:(unfold usp1; lia) MU2 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM2) as ART2.
  pose proof (cl_seg_pres RT AF Σ m1 m2 usp1 32 [] ART1 ltac:(unfold usp1; lia) ltac:(lia) MU2) as PR2.
  assert (AG2 : agree_on (fun x => usp1 <= x < USTACK_TOP) m1 m2) by (intros a Ha; apply PR2; [left; exact Ha | exact I]).
  assert (AGL2 : forall a n, a + n <= lo -> agree_on (fun x => a <= x < a + n) m1 m2) by (intros a' n H x Hx; cbv beta in Hx; apply MU2; cbn [outside]; clear - H Hx HLO2; lia).
  pose proof (cl_env_seg _ m1 m2 lb canary CLE1 MU2 ltac:(cl_fp_lia)) as CLE2.
  assert (BMC2 : rw_cells asegs m2 BM (bufmem_cells len D max (Z_to_bv 64 flw))).
  { apply (rw_cells_agree asegs m1 m2 _ _ BMC1); [apply AGL2; unfold bufmem_cells; cbn [cells_size csize Nat.add]; exact BMLO | exact WM2]. }
  (* [comment removed for export] *)
  assert (ESM : bv_unsigned (Z_to_bv 64 SITE_mf_mbf) = SITE_mf_mbf) by (apply unsigned_lit; unfold SITE_mf_mbf; lia).
  assert (FRR2 : rw_cells asegs m2 (bv_unsigned (Z_to_bv 64 usp1) - 16) [C8 sp; C8 (Z_to_bv 64 SITE_mf_mbf)]).
  { rewrite EU1. replace (usp1 - 16) with (usp2 + Z.of_nat (cells_size [CB 8 j2; C8 (Z_to_bv 64 BB)])) by (cbn [cells_size csize Nat.add]; unfold usp2; lia).
    exact (rw_cells_skip m2 usp2 [CB 8 j2; C8 (Z_to_bv 64 BB)] [C8 sp; C8 (Z_to_bv 64 SITE_mf_mbf)] FR2). }
  assert (AG2w : agree_on (fun x => bv_unsigned (Z_to_bv 64 usp1) <= x < USTACK_TOP) m1 m2) by (rewrite EU1; exact AG2).
  destruct (cl_chain_call (rt_cg RT Σ) e_mem_buf_free e_BUF_MEM_free SITE_mbf_bmf m1 m2 (Z_to_bv 64 SITE_mf_mbf) sp (Z_to_bv 64 usp1) (Z_to_bv 64 usp2) (bv_unsigned ra :: outer)
              ltac:(rewrite ESM; exact CTXa) (proj1 CGH (SITE_mbf_bmf, e_mem_buf_free) ltac:(cbn; tauto)) (proj2 CGH (SITE_mbf_bmf, e_BUF_MEM_free) ltac:(cbn; tauto))
              UWCa AG2w FRR2 ltac:(rewrite EU1, EU2; unfold usp2; lia) ltac:(rewrite EU1; unfold usp1, USTACK_TOP in *; clear - NUM; lia)) as (CTXb & UWCb).
  rewrite ESM in CTXb, UWCb.
  assert (CO2 : call_ok RT Σ m2 (Z_to_bv 64 usp2) lo).
  { fold usp in SPA. unfold call_ok. rewrite EU2. split; [exact ST2|]. split; [exact LOW|]. split; [unfold usp2, usp1, RT_STACK in *; clear - HSTK; lia|].
    split; [unfold usp2, usp1, USTACK_TOP in *; clear - NUM; lia|]. apply Z.mod_divide; [lia|]. apply Z.mod_divide in SPA; [|lia]. destruct SPA as (q & Hq). exists (q - 4). unfold usp2, usp1. lia. }
  (* [comment removed for export] *)
  apply (buf_mem_free_cps Σ PMc (Z_to_bv 64 SITE_mbf_bmf) (Z_to_bv 64 usp2) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 (Z_to_bv 64 usp1) (Z_to_bv 64 1) (Z_to_bv 64 BM) z1 z2 z3 z4
           a5 a6 a7 (Z_to_bv 64 0x7fff8000) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 lo BM D len max flw (SITE_mf_mbf :: bv_unsigned ra :: outer) lb canary
           FDO MST eq_refl eq_refl INBM BMAL BMC2 HFL HFL1 DOPT HMAX0 ART2 MI2 CO2 ltac:(rewrite EU2; unfold usp2, usp1, RT_STACK in *; clear - HSTK; lia)).
  { rewrite (unsigned_lit SITE_mbf_bmf) by (unfold SITE_mbf_bmf; lia). exact CTXb. }
  { exact UWCb. }
  { apply (cg_has_sub _ _ _ _ _ CGH); intros e He; [unfold MF_SITES | unfold MF_CALLS]; apply in_or_app; right; exact He. }
  { rewrite (unsigned_lit SITE_mbf_bmf) by (unfold SITE_mbf_bmf; lia). apply (proj2 CGH). cbn. tauto. }
  { rewrite (unsigned_lit SITE_mbf_bmf) by (unfold SITE_mbf_bmf; lia). apply (proj2 CGH). cbn. tauto. }
  { exact CLE2. }
  { exact Hc2'. }
  clear Hc2'. intros c3 (Σ1 & v1 & Hc3 & LV1 & FRS1 & SP1 & CR1 & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (m3 & RS3 & (ART3 & MI3 & ST3w) & PRES3 & CLE3) & Hc3'). clear Hc3.
  destruct RS3 as (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & F3 & fc3 & ->).
  rewrite EU2 in ST3w, PRES3. rewrite (ret_pc_even SITE_mbf_bmf) in Hc3' by (unfold SITE_mbf_bmf; lia).
  assert (AG23 : forall x : word, usp1 <= bv_unsigned x < USTACK_TOP -> m3 x = m2 x) by (intros x Hx; apply PRES3; left; unfold usp2; clear - Hx; lia).
  assert (INBB1 : In (BB, 16) (rt_live RT Σ1)).
  { rewrite LV1. apply live_remove_keep; [apply live_remove_keep; [exact INBB | cbn [fst]; intros E; exact (NDBB (eq_sym E))] | cbn [fst]; exact NBM]. }
  assert (INR1 : In (R, 32) (rt_live RT Σ1)).
  { rewrite LV1. apply live_remove_keep; [apply live_remove_keep; [exact INR | cbn [fst]; intros E; exact (NDR (eq_sym E))] | cbn [fst]; intros E; exact (NMR (eq_sym E))]. }
  assert (AG04 : forall x : word, usp1 <= bv_unsigned x < USTACK_TOP -> m3 x = m1 x).
  { intros x Hx. rewrite (AG23 x Hx). apply AG2. exact Hx. }
  assert (BBC4 : rw_cells asegs m3 BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)]).
  { apply (rw_cells_agree_nw asegs m1 m3 _ _ BBC1). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    rewrite (PRES3 x ltac:(apply (acl_live _ _ _ BB 16); [exact INBB1 | clear - Hx; lia])). apply AGL2 with (a := BB) (n := 16); [exact BBLO | cbv beta; clear - Hx; lia]. }
  destruct (af_client_consts RT AF Σ1 m3 ART3) as (_ & _ & _ & _ & UT3).
  assert (FR3 : rw_cells asegs m3 usp2 [CB 8 j2; C8 (Z_to_bv 64 BB); C8 sp; C8 (Z_to_bv 64 SITE_mf_mbf)]).
  { apply (rw_cells_agree_nw asegs m2 m3 _ _ FR2). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply PRES3. left. unfold usp2, usp1, USTACK_TOP in *. clear - Hx NUM. lia. }
  pose proof (mbf_s1_walk (Z_to_bv 64 SITE_mf_mbf) (Z_to_bv 64 SITE_mbf_bmf) (Z_to_bv 64 usp1) gp y0 y1 y2 sp (Z_to_bv 64 BB) v1 h1 h2 h3 h4 h5 h6 h7
                (Z_to_bv 64 0x7fff8000) s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6 F3 fc3 m3 lo j2
                ltac:(rewrite EU1; exact HLO2) HLOS ltac:(rewrite EU1; exact SPH1) ltac:(rewrite EU1; exact ST3w) UT3 ltac:(rewrite EU1; exact FR3) MI3) as W2.
  rewrite EU1 in W2. fold usp2 in W2.
  cl_lift W2 Hc3' c4 Hc4.
  destruct (ASTA_unpack RT Σ1 _ _ c4 Hc4) as (ms4 & (-> & ST3) & Hc4'). clear Hc4.
  rewrite EU1 in ST3. rewrite (ret_pc_even SITE_mf_mbf) in Hc4' by (unfold SITE_mf_mbf; lia).
  (* [comment removed for export] *)
  pose proof (mf_s1_walk (Z_to_bv 64 SITE_mf_mbf) sp gp y0 y1 y2 (Z_to_bv 64 1) h1 h2 h3 h4 h5 h6 h7 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6 F3 fc3 m3 BB BM R
                SPH UT3 BBC4 (proj2 (af_acc_live RT AF Σ1 m3 BB 16 ART3 INBB1)) BB0 BBAL BBHI ltac:(clear - BBLO HLO1 SPH; lia) ltac:(clear - R0 RLO HLO1 SPH; lia) MI3 eq_refl) as W3.
  fold usp usp1 in W3.
  cl_lift W3 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ1 _ _ c5 Hc5) as (ms5 & -> & Hc5'). clear Hc5.
  assert (CO4 : call_ok RT Σ1 m3 (Z_to_bv 64 usp1) lo).
  { fold usp in SPA. unfold call_ok. rewrite EU1, SP1. split; [exact ST3|]. split; [exact LOW|]. split; [unfold usp1, RT_STACK in *; clear - HSTK; lia|].
    split; [unfold usp1, USTACK_TOP in *; clear - NUM; lia|]. apply Z.mod_divide; [lia|]. apply Z.mod_divide in SPA; [|lia]. destruct SPA as (q & Hq). exists (q - 2). unfold usp1. lia. }
  assert (FRR4 : rw_cells asegs m3 (usp - 16) [C8 s0; C8 ra]).
  { apply (rw_cells_agree_nw asegs m1 m3 _ _ FRR1). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply AG04. unfold usp1, USTACK_TOP in *. clear - Hx NUM. lia. }
  assert (AG04' : agree_on (fun x => usp <= x < USTACK_TOP) m m3) by (intros x Hx; cbv beta in Hx; rewrite (AG04 x ltac:(unfold usp1; clear - Hx; lia)); exact (AG1 x Hx)).
  destruct (cl_chain_call (rt_cg RT Σ) e_mem_free e_CRYPTO_free SITE_mf_free1 m m3 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH (SITE_mf_free1, e_mem_free) ltac:(cbn; tauto)) (proj2 CGH (SITE_mf_free1, e_CRYPTO_free) ltac:(cbn; tauto)) UWC AG04' FRR4 ltac:(rewrite EU1; unfold usp1; lia) SPT) as (CTXc & UWCc).
  apply (C_FR Σ1 PMc (Z_to_bv 64 SITE_mf_free1) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) y0 y1 y2 sp (Z_to_bv 64 BB) (Z_to_bv 64 R) (Z_to_bv 64 MEM_FILE) (Z_to_bv 64 153)
           h3 h4 h5 h6 h7 (Z_to_bv 64 MEM_FILE) s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6 F3 fc3 m3 R 32 lo (bv_unsigned ra :: outer) lb canary
           FDO MST eq_refl eq_refl INR1 ART3 MI3 CO4).
  { rewrite CG1, (unsigned_lit SITE_mf_free1) by (unfold SITE_mf_free1; lia). exact CTXc. }
  { exact UWCc. }
  { rewrite CG1, (unsigned_lit SITE_mf_free1) by (unfold SITE_mf_free1; lia). apply (proj2 CGH). cbn. tauto. }
  { exact CLE3. }
  { exact Hc5'. }
  clear Hc5'. intros c6 (Σ2 & v2 & Hc6 & LV2 & FRS2 & SP2 & CR2 & CG2).
  destruct (ASTA_unpack RT Σ2 _ _ c6 Hc6) as (ms6 & (m5 & RS5 & (ART5 & MI5 & ST5) & PRES5 & CLE5) & Hc6'). clear Hc6.
  destruct RS5 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F5 & fc5 & ->).
  rewrite EU1 in ST5, PRES5. rewrite (ret_pc_even SITE_mf_free1) in Hc6' by (unfold SITE_mf_free1; lia).
  assert (INBB2 : In (BB, 16) (rt_live RT Σ2)) by (rewrite LV2; apply live_remove_keep; [exact INBB1 | cbn [fst]; exact NBR]).
  (* [comment removed for export] *)
  pose proof (mf_s2_walk (Z_to_bv 64 SITE_mf_free1) sp gp u0 u1 u2 v2 b1 b2 b3 b4 b5 b6 b7 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F5 fc5 m5 BB
                SPH ltac:(clear - BB0 BBLO HLO1 SPH; lia) MI5) as W4.
  fold usp usp1 in W4.
  cl_lift W4 Hc6' c7 Hc7.
  destruct (ASTA_unpack RT Σ2 _ _ c7 Hc7) as (ms7 & -> & Hc7'). clear Hc7.
  assert (CO5 : call_ok RT Σ2 m5 (Z_to_bv 64 usp1) lo).
  { fold usp in SPA. unfold call_ok. rewrite EU1, SP2, SP1. split; [exact ST5|]. split; [exact LOW|]. split; [unfold usp1, RT_STACK in *; clear - HSTK; lia|].
    split; [unfold usp1, USTACK_TOP in *; clear - NUM; lia|]. apply Z.mod_divide; [lia|]. apply Z.mod_divide in SPA; [|lia]. destruct SPA as (q & Hq). exists (q - 2). unfold usp1. lia. }
  assert (AG45 : forall x : word, usp1 <= bv_unsigned x < USTACK_TOP -> m5 x = m3 x) by (intros x Hx; apply PRES5; left; exact Hx).
  assert (FRR5 : rw_cells asegs m5 (usp - 16) [C8 s0; C8 ra]).
  { apply (rw_cells_agree_nw asegs m3 m5 _ _ FRR4). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply AG45. unfold usp1, USTACK_TOP in *. clear - Hx NUM. lia. }
  assert (AG05' : agree_on (fun x => usp <= x < USTACK_TOP) m m5) by (intros x Hx; cbv beta in Hx; rewrite (AG45 x ltac:(unfold usp1; clear - Hx; lia)); exact (AG04' x Hx)).
  destruct (cl_chain_call (rt_cg RT Σ) e_mem_free e_CRYPTO_free SITE_mf_free2 m m5 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH (SITE_mf_free2, e_mem_free) ltac:(cbn; tauto)) (proj2 CGH (SITE_mf_free2, e_CRYPTO_free) ltac:(cbn; tauto)) UWC AG05' FRR5 ltac:(rewrite EU1; unfold usp1; lia) SPT) as (CTXd & UWCd).
  apply (C_FR Σ2 PMc (Z_to_bv 64 SITE_mf_free2) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 sp (Z_to_bv 64 BB) (Z_to_bv 64 BB) (Z_to_bv 64 MEM_FILE) (Z_to_bv 64 154)
           b3 b4 b5 b6 b7 (Z_to_bv 64 MEM_FILE) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F5 fc5 m5 BB 16 lo (bv_unsigned ra :: outer) lb canary
           FDO MST eq_refl eq_refl INBB2 ART5 MI5 CO5).
  { rewrite CG2, CG1, (unsigned_lit SITE_mf_free2) by (unfold SITE_mf_free2; lia). exact CTXd. }
  { exact UWCd. }
  { rewrite CG2, CG1, (unsigned_lit SITE_mf_free2) by (unfold SITE_mf_free2; lia). apply (proj2 CGH). cbn. tauto. }
  { exact CLE5. }
  { exact Hc7'. }
  clear Hc7'. intros c8 (Σ3 & v3 & Hc8 & LV3 & FRS3 & SP3 & CR3 & CG3).
  destruct (ASTA_unpack RT Σ3 _ _ c8 Hc8) as (ms8 & (m6 & RS6 & (ART6 & MI6 & ST6) & PRES6 & CLE6) & Hc8'). clear Hc8.
  destruct RS6 as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & F6 & fc6 & ->).
  rewrite EU1 in ST6, PRES6. rewrite (ret_pc_even SITE_mf_free2) in Hc8' by (unfold SITE_mf_free2; lia).
  assert (AG56 : forall x : word, usp1 <= bv_unsigned x < USTACK_TOP -> m6 x = m5 x) by (intros x Hx; apply PRES6; left; exact Hx).
  assert (FR6 : rw_cells asegs m6 usp1 [C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree_nw asegs m1 m6 _ _ FR1). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    rewrite (AG56 x ltac:(unfold usp1, USTACK_TOP in *; clear - Hx NUM; lia)), (AG45 x ltac:(unfold usp1, USTACK_TOP in *; clear - Hx NUM; lia)).
    apply AG04. unfold usp1, USTACK_TOP in *. clear - Hx NUM. lia. }
  destruct (af_client_consts RT AF Σ3 m6 ART6) as (_ & _ & _ & _ & UT6).
  (* [comment removed for export] *)
  pose proof (mf_s3_walk ra (Z_to_bv 64 SITE_mf_free2) sp gp w0 w1 w2 s0 s1 s2 v3 d1 d2 d3 d4 d5 d6 d7 s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 (Z_to_bv 64 BB) (Z_to_bv 64 MEM_FILE)
                F6 fc6 m6 lo HLO1 HLOS SPH ST6 UT6 FR6 MI6) as W5.
  fold usp usp1 in W5.
  cl_lift W5 Hc8' c9 Hc9.
  apply Hk. unfold free_post. exists Σ3, (Z_to_bv 64 1).
  split; [| rewrite LV3, FRS3, SP3, CR3, CG3, LV2, FRS2, SP2, CR2, CG2, LV1, FRS1, SP1, CR1, CG1; repeat split; reflexivity].
  eapply ASTA_conseq; [exact Hc9|]. cbv beta. intros ms (m7 & -> & MU7 & WM7 & MI7 & ST7). fold usp in ST7. exists m7.
  assert (E7 : forall x : word, m7 x = m6 x) by (intros x; apply MU7; exact I).
  assert (ART7 : ART RT Σ3 m7) by (apply (af_frame RT AF Σ3 m6 m7 usp1 ART6 ltac:(rewrite SP3, SP2, SP1; unfold usp1; clear - NUM; lia)); [intros x _; apply E7 | exact WM7]).
  split; [do 16 eexists; reflexivity|]. split; [exact (conj ART7 (conj MI7 ST7))|]. split; [| apply (cl_env_agree m6 m7 lb canary CLE6); intros a _; apply E7].
  assert (SUB31 : forall e, In e (rt_live RT Σ3) -> In e (rt_live RT Σ1)) by (intros e He; rewrite LV3, LV2 in He; exact (live_remove_sub _ _ _ (live_remove_sub _ _ _ He))).
  assert (SUB30 : forall e, In e (rt_live RT Σ3) -> In e (rt_live RT Σ)) by (intros e He; pose proof (SUB31 e He) as He1; rewrite LV1 in He1; exact (live_remove_sub _ _ _ (live_remove_sub _ _ _ He1))).
  intros x Hx. rewrite E7.
  rewrite (PRES6 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | rewrite FRS2, FRS1; auto | unfold usp1; clear; lia])).
  rewrite (PRES5 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [rewrite LV3; intros e He; exact (live_remove_sub _ _ _ He) | rewrite FRS1; auto | unfold usp1; clear; lia])).
  rewrite (PRES3 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [exact SUB31 | auto | unfold usp2, usp1; clear; lia])).
  rewrite (PR2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [exact SUB30 | auto | unfold usp1; clear; lia]) I).
  exact (PR1 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [exact SUB30 | auto | clear; lia]) I).
Qed.

Hypothesis C_SCF : crypto_secure_clear_free_env_stmt RT.

Definition BFS_SITES : list (Z * Z) := [(SITE_bf_tail, e_BUF_MEM_free)].
Definition BFS_CALLS : list (Z * Z) := [(SITE_bf_tail, e_CRYPTO_secure_clear_free); (SITE_bf_tail, e_CRYPTO_free); (SITE_bf_tail, e_free)].

(* [comment removed for export] *)
Definition free_post_sec (Σ : rts RT) PMc (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (lo : Z) (m : mem) (lb : byte) (canary : word)
    (live' : list (Z * Z)) : config -> Prop :=
  fun c => exists (Σ' : rts RT) (v : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
           /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres (rt_live RT Σ') (rt_frames RT Σ) (bv_unsigned sp) m m'
           /\ cl_env m' lb canary /\ sec_off m') c
       /\ rt_live RT Σ' = live' /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_cg RT Σ' = rt_cg RT Σ.

(* [comment removed for export] *)
Definition buf_mem_free_sec_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BM D len max flw : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BM ->
  In (BM, 32) (rt_live RT Σ) -> BM mod 16 = 0 -> rw_cells asegs m BM (bufmem_cells len D max (Z_to_bv 64 flw)) -> 0 <= flw < 2 ^ 64 -> Z.land flw 1 = 1 ->
  In (D, max) (rt_live RT Σ) -> D <> BM -> 1 <= max < 2 ^ 40 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 80 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_BUF_MEM_free (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) BFS_SITES BFS_CALLS ->
  In (bv_unsigned ra, e_CRYPTO_free) (cg_call (rt_cg RT Σ)) -> In (bv_unsigned ra, e_free) (cg_call (rt_cg RT Σ)) ->
  cl_env m lb canary -> sec_off m ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_BUF_MEM_free m)))
    (free_post_sec Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m lb canary (live_remove BM (live_remove D (rt_live RT Σ)))).

Theorem buf_mem_free_sec_cps : buf_mem_free_sec_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BM D len max flw outer lb canary
    FDO MST -> -> INBM BMAL BMC HFL HFL1 IND NDBM HMAX ART0 MI0 CALL HSTK CTX UWC CGH TL1 TL2 CLE SEC.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 32 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -32).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (HLO1 : lo <= usp - 32) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (af_live_range RT AF Σ m BM 32 ART0 INBM) as (BM0 & BMLO' & _). assert (BMLO : BM + 32 <= lo) by (clear - BMLO' LOW; lia). clear BMLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BM 32 ART0 INBM ltac:(lia)) as BMHI. pose proof (proj2 (af_acc_live RT AF Σ m BM 32 ART0 INBM)) as ACCBM.
  pose proof (af_live_range RT AF Σ m D max ART0 IND) as (D0 & DLO' & _). assert (DLO : D + max <= lo) by (clear - DLO' LOW; lia). clear DLO'.
  (* [comment removed for export] *)
  pose proof (bf_sec_walk ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BM len D max flw
                HLO1 HLOS SPH ST UT SHC BMC ACCBM BM0 BMAL BMHI BMLO ltac:(clear - D0 DLO HLO1 SPH HMAX; lia) ltac:(clear - HMAX; lia) HFL HFL1 MI0) as W0.
  fold usp in W0. fold usp1 in W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (j & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 32 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 32 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  pose proof (cl_env_seg _ m m1 lb canary CLE MU1 ltac:(cl_fp_lia)) as CLE1.
  assert (CO1 : call_ok RT Σ m1 (Z_to_bv 64 usp1) lo).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 2. }
  assert (FRR1 : rw_cells asegs m1 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp1 + Z.of_nat (cells_size [CB 8 j; C8 s1])) by (cbn [cells_size csize Nat.add]; unfold usp1; lia).
    exact (rw_cells_skip m1 usp1 [CB 8 j; C8 s1] [C8 s0; C8 ra] FR1). }
  destruct (cl_chain_call (rt_cg RT Σ) e_BUF_MEM_free e_CRYPTO_secure_clear_free SITE_bf_tail m m1 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH _ ltac:(left; reflexivity)) (proj2 CGH _ ltac:(left; reflexivity)) UWC AG1 FRR1 ltac:(rewrite EU1; unfold usp1; lia) SPT) as (CTX2 & UWC2).
  (* [comment removed for export] *)
  assert (SEC1 : sec_off m1) by (apply (sec_off_agree m m1 SEC); intros a Ha; apply MU1; cbn [outside]; rewrite Ha; unfold SEC_INIT; split; [clear - HLO1 HLOS; lia | exact I]).
  apply (C_SCF Σ PMc (Z_to_bv 64 SITE_bf_tail) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 BM) (Z_to_bv 64 D) (Z_to_bv 64 max) (Z_to_bv 64 BUF_FILE) (Z_to_bv 64 47)
           a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 D max max lo (bv_unsigned ra :: outer) lb canary
           FDO MST eq_refl eq_refl eq_refl IND ltac:(clear - HMAX; lia) ltac:(clear - HMAX; lia) ltac:(clear - HMAX; lia) ART1 MI1 CO1 ltac:(rewrite EU1; unfold usp1, RT_STACK in *; clear - HSTK; lia)).
  { rewrite (unsigned_lit SITE_bf_tail) by (unfold SITE_bf_tail; lia). exact CTX2. }
  { exact UWC2. }
  { rewrite (unsigned_lit SITE_bf_tail) by (unfold SITE_bf_tail; lia). apply (proj2 CGH). right; left; reflexivity. }
  { rewrite (unsigned_lit SITE_bf_tail) by (unfold SITE_bf_tail; lia). apply (proj2 CGH). right; right; left; reflexivity. }
  { exact CLE1. }
  { exact SEC1. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & v1 & Hc2 & LV1 & FRS1 & SP1 & CR1 & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & ST2) & PRES2 & CLE2 & SEC2) & Hc2'). clear Hc2.
  destruct RS2 as (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_bf_tail) in Hc2' by (unfold SITE_bf_tail; lia).
  assert (AG12 : forall x : word, usp1 <= bv_unsigned x < USTACK_TOP -> m2 x = m1 x) by (intros x Hx; apply PRES2; left; exact Hx).
  assert (FR2 : rw_cells asegs m2 usp1 [CB 8 j; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ FR1). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add length] in Hx. apply AG12. unfold usp1, USTACK_TOP in *. clear - Hx NUM. lia. }
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & _ & _ & _ & UT2).
  (* [comment removed for export] *)
  pose proof (bf_tail_walk ra (Z_to_bv 64 SITE_bf_tail) sp gp y0 y1 y2 s0 s1 v1 h1 h2 h3 h4 h5 h6 h7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6 F2 fc2 m2 lo BM j
                HLO1 HLOS SPH ST2 UT2 FR2 ltac:(clear - BM0 BMLO HLO1 SPH; lia) MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (m3 & -> & MU3 & WM3 & MI3 & ST3) & Hc3'). clear Hc3. fold usp in ST3.
  assert (E3 : forall x : word, m3 x = m2 x) by (intros x; apply MU3; exact I).
  assert (ART3 : ART RT Σ1 m3) by (apply (af_frame RT AF Σ1 m2 m3 usp1 ART2 ltac:(rewrite SP1; unfold usp1; clear - NUM; lia)); [intros x _; apply E3 | exact WM3]).
  assert (INBM1 : In (BM, 32) (rt_live RT Σ1)) by (rewrite LV1; apply live_remove_keep; [exact INBM | cbn [fst]; intros E; exact (NDBM (eq_sym E))]).
  assert (CO3 : call_ok RT Σ1 m3 sp lo) by (unfold call_ok; rewrite SP1; exact (conj ST3 (conj LOW (conj LOR (conj SPT SPA))))).
  assert (UWC3 : uw_chain m3 sp s0 outer).
  { apply (uw_chain_agree outer m m3 sp s0 UWC). intros x Hx. cbv beta in Hx. rewrite E3. rewrite (AG12 x ltac:(unfold usp1; clear - Hx; lia)). exact (AG1 x Hx). }
  pose proof (cl_env_agree m2 m3 lb canary CLE2 ltac:(intros a _; apply E3)) as CLE3.
  (* [comment removed for export] *)
  apply (C_FR Σ1 PMc ra sp gp (Z_to_bv 64 0xba3ef0) y0 y1 y2 s0 s1 (Z_to_bv 64 BM) (Z_to_bv 64 BUF_FILE) (Z_to_bv 64 51) h3 h4 h5 h6 h7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6
           F2 fc2 m3 BM 32 lo outer lb canary FDO MST eq_refl eq_refl INBM1 ART3 MI3 CO3 ltac:(rewrite CG1; exact (conj TL1 (proj2 CTX))) UWC3 ltac:(rewrite CG1; exact TL2) CLE3).
  { exact Hc3'. }
  clear Hc3'. intros c4 (Σ2 & v2 & Hc4 & LV2 & FRS2 & SP2 & CR2 & CG2).
  apply Hk. unfold free_post_sec. exists Σ2, v2.
  split; [| rewrite LV2, FRS2, SP2, CR2, CG2, LV1, FRS1, SP1, CR1, CG1; repeat split; reflexivity].
  eapply ASTA_conseq; [exact Hc4|]. cbv beta. intros ms (m4 & RS4 & RAF4 & PRES4 & CLE4). exists m4.
  split; [exact RS4|]. split; [exact RAF4|].
  assert (AG04 : forall x : word, aclient (rt_live RT Σ2) (rt_frames RT Σ) usp (bv_unsigned x) -> m4 x = m x); [| split; [exact AG04 | split; [exact CLE4 | apply (sec_off_agree m m4 SEC); intros a Ha; apply AG04; right; left; rewrite Ha; exact sec_init_static]]].
  intros x Hx. rewrite (PRES4 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | rewrite FRS1; auto | clear; lia])). rewrite E3.
  assert (Hx1 : aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x)).
  { apply (aclient_mono _ _ _ _ _ _ _ Hx); [| auto | clear; lia]. rewrite LV2, LV1. intros e He. exact (live_remove_sub _ _ _ (live_remove_sub _ _ _ He)). }
  rewrite (PRES2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [rewrite LV2; intros e He; exact (live_remove_sub _ _ _ He) | auto | unfold usp1; clear; lia])).
  apply PR1; [exact Hx1 | exact I].
Qed.

Definition MFS_SITES : list (Z * Z) :=
  [(SITE_mf_mbf, e_mem_free); (SITE_mf_free1, e_mem_free); (SITE_mf_free2, e_mem_free); (SITE_mbf_bmf, e_mem_buf_free)] ++ BFS_SITES.
Definition MFS_CALLS : list (Z * Z) :=
  [(SITE_mf_mbf, e_mem_buf_free); (SITE_mf_free1, e_CRYPTO_free); (SITE_mf_free1, e_free); (SITE_mf_free2, e_CRYPTO_free); (SITE_mf_free2, e_free);
   (SITE_mbf_bmf, e_BUF_MEM_free); (SITE_mbf_bmf, e_CRYPTO_free); (SITE_mbf_bmf, e_free)] ++ BFS_CALLS.

(* [comment removed for export] *)
Definition mem_free_sec_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BI BB BM R D len max fl flw : Z) (rrw numw padw : word) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BI ->
  In (BI, 128) (rt_live RT Σ) -> BI mod 16 = 0 -> rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  In (BB, 16) (rt_live RT Σ) -> BB mod 16 = 0 -> rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] ->
  In (BM, 32) (rt_live RT Σ) -> BM mod 16 = 0 -> rw_cells asegs m BM (bufmem_cells len D max (Z_to_bv 64 flw)) -> 0 <= flw < 2 ^ 64 -> Z.land flw 1 = 1 ->
  In (R, 32) (rt_live RT Σ) -> BM <> R -> BB <> BM -> BB <> R -> D <> BB -> D <> R ->
  In (D, max) (rt_live RT Σ) -> D <> BM -> 1 <= max < 2 ^ 40 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 144 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_mem_free (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) MFS_SITES MFS_CALLS ->
  cl_env m lb canary -> sec_off m ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_mem_free m)))
    (free_post_sec Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m lb canary (live_remove BB (live_remove R (live_remove BM (live_remove D (rt_live RT Σ)))))).

Theorem mem_free_sec_cps : mem_free_sec_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R D len max fl flw rrw numw padw outer lb canary
    FDO MST -> -> INBI BIAL BW FLOK INBB BBAL BBC INBM BMAL BMC HFL HFL1 INR NMR NBM NBR NDBB NDR IND NDBM HMAX ART0 MI0 CALL HSTK CTX UWC CGH CLE SEC.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 64 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -32). set (usp2 := usp1 + -32).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (EU2 : bv_unsigned (Z_to_bv 64 usp2) = usp2) by (apply unsigned_lit; unfold usp2, usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (HLO1 : lo <= usp - 32) by (clear - HSTK; unfold RT_STACK in *; lia). assert (HLO2 : lo <= usp1 - 32) by (clear - HSTK; unfold usp1, RT_STACK in *; lia).
  pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia). assert (SPH1 : usp1 <= 2 ^ 47) by (clear - NUM; unfold usp1, USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (af_live_range RT AF Σ m BI 128 ART0 INBI) as (BI0 & BILO' & _). assert (BILO : BI + 128 <= lo) by (clear - BILO' LOW; lia). clear BILO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BI 128 ART0 INBI ltac:(lia)) as BIHI. pose proof (proj2 (af_acc_live RT AF Σ m BI 128 ART0 INBI)) as ACCBI.
  pose proof (af_live_range RT AF Σ m BB 16 ART0 INBB) as (BB0 & BBLO' & _). assert (BBLO : BB + 16 <= lo) by (clear - BBLO' LOW; lia). clear BBLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BB 16 ART0 INBB ltac:(lia)) as BBHI. pose proof (proj2 (af_acc_live RT AF Σ m BB 16 ART0 INBB)) as ACCBB.
  pose proof (af_live_range RT AF Σ m BM 32 ART0 INBM) as (BM0 & BMLO' & _). assert (BMLO : BM + 32 <= lo) by (clear - BMLO' LOW; lia). clear BMLO'.
  pose proof (af_live_range RT AF Σ m R 32 ART0 INR) as (R0 & RLO' & _). assert (RLO : R + 32 <= lo) by (clear - RLO' LOW; lia). clear RLO'.
  pose proof (bio_flags_byte1 m BI _ _ fl rrw numw padw _ ltac:(destruct FLOK; lia) BW) as FB1.
  assert (ES : bv_unsigned sp = usp) by reflexivity.
  (* [comment removed for export] *)
  pose proof (mf_s0_walk ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB fl rrw numw padw
                HLO1 HLOS SPH ST UT SHC BW ACCBI BI0 BIAL BIHI BILO ltac:(clear - BB0 BBLO HLO1 SPH; lia) MI0) as W0.
  fold usp in W0. fold usp1 in W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (x1 & x2 & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 32 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 32 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  assert (AGL1 : forall a n, a + n <= lo -> agree_on (fun x => a <= x < a + n) m m1) by (intros a' n H x Hx; cbv beta in Hx; apply MU1; cbn [outside]; clear - H Hx HLO1; lia).
  pose proof (cl_env_seg _ m m1 lb canary CLE MU1 ltac:(cl_fp_lia)) as CLE1.
  destruct (af_client_consts RT AF Σ m1 ART1) as (_ & SHC1 & _ & _ & UT1).
  assert (BW1 : rw_cells asegs m1 (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB))).
  { apply (rw_cells_agree asegs m m1 _ _ BW); [apply AGL1; unfold bio_w1_cells; cbn [cells_size csize Nat.add]; clear - BILO; lia | exact WM1]. }
  assert (FB11 : rw_cells asegs m1 (BI + 49) [C1 (Z_to_bv 8 (fl ≫ 8))]).
  { apply (rw_cells_agree asegs m m1 _ _ FB1); [apply AGL1; cbn [cells_size csize Nat.add]; clear - BILO; lia | exact WM1]. }
  assert (BBC1 : rw_cells asegs m1 BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)]).
  { apply (rw_cells_agree asegs m m1 _ _ BBC); [apply AGL1; cbn [cells_size csize Nat.add]; exact BBLO | exact WM1]. }
  assert (BMC1 : rw_cells asegs m1 BM (bufmem_cells len D max (Z_to_bv 64 flw))).
  { apply (rw_cells_agree asegs m m1 _ _ BMC); [apply AGL1; unfold bufmem_cells; cbn [cells_size csize Nat.add]; exact BMLO | exact WM1]. }
  assert (FRR1 : rw_cells asegs m1 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp1 + Z.of_nat (cells_size [C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; unfold usp1; lia).
    exact (rw_cells_skip m1 usp1 [C8 s2; C8 s1] [C8 s0; C8 ra] FR1). }
  destruct (cl_chain_call (rt_cg RT Σ) e_mem_free e_mem_buf_free SITE_mf_mbf m m1 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH (SITE_mf_mbf, e_mem_free) ltac:(cbn; tauto)) (proj2 CGH (SITE_mf_mbf, e_mem_buf_free) ltac:(cbn; tauto)) UWC AG1 FRR1 ltac:(rewrite EU1; unfold usp1; lia) SPT) as (CTXa & UWCa).
  assert (STK1 : stk asegs m1 lo (bv_unsigned (Z_to_bv 64 usp1))) by (rewrite EU1; exact ST1).
  (* [comment removed for export] *)
  pose proof (mbf_s0_walk (Z_to_bv 64 SITE_mf_mbf) (Z_to_bv 64 usp1) gp t0 t1 t2 sp (Z_to_bv 64 BB) x1 x2 a3 a4 a5 a6 a7 (Z_to_bv 64 0x7fff8000) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m1 lo BI BB BM R fl rrw numw padw
                ltac:(rewrite EU1; exact HLO2) HLOS ltac:(rewrite EU1; exact SPH1) STK1 UT1 SHC1 BW1 FLOK FB11
                (proj2 (af_acc_live RT AF Σ m1 BI 128 ART1 INBI)) BI0 BIAL BIHI BILO BBC1 (proj2 (af_acc_live RT AF Σ m1 BB 16 ART1 INBB)) BB0 BBAL BBHI BBLO
                ltac:(clear - BM0 BMLO HLO1 SPH; lia) MI1) as W1.
  unfold mbf_s0_post in W1. rewrite EU1 in W1. fold usp2 in W1.
  cl_lift W1 Hc1' c2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (z1 & z2 & z3 & z4 & j2 & m2 & -> & MU2 & WM2 & MI2 & FR2 & ST2) & Hc2'). clear Hc2.
  pose proof (cl_seg_ART RT AF Σ m1 m2 usp1 32 [] ART1 ltac:(unfold usp1; lia) ltac:(unfold usp1; lia) MU2 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM2) as ART2.
  pose proof (cl_seg_pres RT AF Σ m1 m2 usp1 32 [] ART1 ltac:(unfold usp1; lia) ltac:(lia) MU2) as PR2.
  assert (AG2 : agree_on (fun x => usp1 <= x < USTACK_TOP) m1 m2) by (intros a Ha; apply PR2; [left; exact Ha | exact I]).
  assert (AGL2 : forall a n, a + n <= lo -> agree_on (fun x => a <= x < a + n) m1 m2) by (intros a' n H x Hx; cbv beta in Hx; apply MU2; cbn [outside]; clear - H Hx HLO2; lia).
  pose proof (cl_env_seg _ m1 m2 lb canary CLE1 MU2 ltac:(cl_fp_lia)) as CLE2.
  assert (BMC2 : rw_cells asegs m2 BM (bufmem_cells len D max (Z_to_bv 64 flw))).
  { apply (rw_cells_agree asegs m1 m2 _ _ BMC1); [apply AGL2; unfold bufmem_cells; cbn [cells_size csize Nat.add]; exact BMLO | exact WM2]. }
  (* [comment removed for export] *)
  assert (ESM : bv_unsigned (Z_to_bv 64 SITE_mf_mbf) = SITE_mf_mbf) by (apply unsigned_lit; unfold SITE_mf_mbf; lia).
  assert (FRR2 : rw_cells asegs m2 (bv_unsigned (Z_to_bv 64 usp1) - 16) [C8 sp; C8 (Z_to_bv 64 SITE_mf_mbf)]).
  { rewrite EU1. replace (usp1 - 16) with (usp2 + Z.of_nat (cells_size [CB 8 j2; C8 (Z_to_bv 64 BB)])) by (cbn [cells_size csize Nat.add]; unfold usp2; lia).
    exact (rw_cells_skip m2 usp2 [CB 8 j2; C8 (Z_to_bv 64 BB)] [C8 sp; C8 (Z_to_bv 64 SITE_mf_mbf)] FR2). }
  assert (AG2w : agree_on (fun x => bv_unsigned (Z_to_bv 64 usp1) <= x < USTACK_TOP) m1 m2) by (rewrite EU1; exact AG2).
  destruct (cl_chain_call (rt_cg RT Σ) e_mem_buf_free e_BUF_MEM_free SITE_mbf_bmf m1 m2 (Z_to_bv 64 SITE_mf_mbf) sp (Z_to_bv 64 usp1) (Z_to_bv 64 usp2) (bv_unsigned ra :: outer)
              ltac:(rewrite ESM; exact CTXa) (proj1 CGH (SITE_mbf_bmf, e_mem_buf_free) ltac:(cbn; tauto)) (proj2 CGH (SITE_mbf_bmf, e_BUF_MEM_free) ltac:(cbn; tauto))
              UWCa AG2w FRR2 ltac:(rewrite EU1, EU2; unfold usp2; lia) ltac:(rewrite EU1; unfold usp1, USTACK_TOP in *; clear - NUM; lia)) as (CTXb & UWCb).
  rewrite ESM in CTXb, UWCb.
  assert (CO2 : call_ok RT Σ m2 (Z_to_bv 64 usp2) lo).
  { fold usp in SPA. unfold call_ok. rewrite EU2. split; [exact ST2|]. split; [exact LOW|]. split; [unfold usp2, usp1, RT_STACK in *; clear - HSTK; lia|].
    split; [unfold usp2, usp1, USTACK_TOP in *; clear - NUM; lia|]. apply Z.mod_divide; [lia|]. apply Z.mod_divide in SPA; [|lia]. destruct SPA as (q & Hq). exists (q - 4). unfold usp2, usp1. lia. }
  (* [comment removed for export] *)
  assert (SEC2 : sec_off m2).
  { apply (sec_off_agree m m2 SEC). intros a Ha. rewrite (MU2 a ltac:(cbn [outside]; rewrite Ha; unfold SEC_INIT, usp1; split; [clear - HLO2 HLOS; lia | exact I])).
    apply MU1. cbn [outside]. rewrite Ha. unfold SEC_INIT. split; [clear - HLO1 HLOS; lia | exact I]. }
  apply (buf_mem_free_sec_cps Σ PMc (Z_to_bv 64 SITE_mbf_bmf) (Z_to_bv 64 usp2) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 (Z_to_bv 64 usp1) (Z_to_bv 64 1) (Z_to_bv 64 BM) z1 z2 z3 z4
           a5 a6 a7 (Z_to_bv 64 0x7fff8000) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 lo BM D len max flw (SITE_mf_mbf :: bv_unsigned ra :: outer) lb canary
           FDO MST eq_refl eq_refl INBM BMAL BMC2 HFL HFL1 IND NDBM HMAX ART2 MI2 CO2 ltac:(rewrite EU2; unfold usp2, usp1, RT_STACK in *; clear - HSTK; lia)).
  { rewrite (unsigned_lit SITE_mbf_bmf) by (unfold SITE_mbf_bmf; lia). exact CTXb. }
  { exact UWCb. }
  { apply (cg_has_sub _ _ _ _ _ CGH); intros e He; [unfold MFS_SITES | unfold MFS_CALLS]; apply in_or_app; right; exact He. }
  { rewrite (unsigned_lit SITE_mbf_bmf) by (unfold SITE_mbf_bmf; lia). apply (proj2 CGH). cbn. tauto. }
  { rewrite (unsigned_lit SITE_mbf_bmf) by (unfold SITE_mbf_bmf; lia). apply (proj2 CGH). cbn. tauto. }
  { exact CLE2. }
  { exact SEC2. }
  { exact Hc2'. }
  clear Hc2'. intros c3 (Σ1 & v1 & Hc3 & LV1 & FRS1 & SP1 & CR1 & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (m3 & RS3 & (ART3 & MI3 & ST3w) & PRES3 & CLE3 & SEC3) & Hc3'). clear Hc3.
  destruct RS3 as (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & F3 & fc3 & ->).
  rewrite EU2 in ST3w, PRES3. rewrite (ret_pc_even SITE_mbf_bmf) in Hc3' by (unfold SITE_mbf_bmf; lia).
  assert (AG23 : forall x : word, usp1 <= bv_unsigned x < USTACK_TOP -> m3 x = m2 x) by (intros x Hx; apply PRES3; left; unfold usp2; clear - Hx; lia).
  assert (INBB1 : In (BB, 16) (rt_live RT Σ1)).
  { rewrite LV1. apply live_remove_keep; [apply live_remove_keep; [exact INBB | cbn [fst]; intros E; exact (NDBB (eq_sym E))] | cbn [fst]; exact NBM]. }
  assert (INR1 : In (R, 32) (rt_live RT Σ1)).
  { rewrite LV1. apply live_remove_keep; [apply live_remove_keep; [exact INR | cbn [fst]; intros E; exact (NDR (eq_sym E))] | cbn [fst]; intros E; exact (NMR (eq_sym E))]. }
  assert (AG04 : forall x : word, usp1 <= bv_unsigned x < USTACK_TOP -> m3 x = m1 x).
  { intros x Hx. rewrite (AG23 x Hx). apply AG2. exact Hx. }
  assert (BBC4 : rw_cells asegs m3 BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)]).
  { apply (rw_cells_agree_nw asegs m1 m3 _ _ BBC1). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    rewrite (PRES3 x ltac:(apply (acl_live _ _ _ BB 16); [exact INBB1 | clear - Hx; lia])). apply AGL2 with (a := BB) (n := 16); [exact BBLO | cbv beta; clear - Hx; lia]. }
  destruct (af_client_consts RT AF Σ1 m3 ART3) as (_ & _ & _ & _ & UT3).
  assert (FR3 : rw_cells asegs m3 usp2 [CB 8 j2; C8 (Z_to_bv 64 BB); C8 sp; C8 (Z_to_bv 64 SITE_mf_mbf)]).
  { apply (rw_cells_agree_nw asegs m2 m3 _ _ FR2). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply PRES3. left. unfold usp2, usp1, USTACK_TOP in *. clear - Hx NUM. lia. }
  pose proof (mbf_s1_walk (Z_to_bv 64 SITE_mf_mbf) (Z_to_bv 64 SITE_mbf_bmf) (Z_to_bv 64 usp1) gp y0 y1 y2 sp (Z_to_bv 64 BB) v1 h1 h2 h3 h4 h5 h6 h7
                (Z_to_bv 64 0x7fff8000) s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6 F3 fc3 m3 lo j2
                ltac:(rewrite EU1; exact HLO2) HLOS ltac:(rewrite EU1; exact SPH1) ltac:(rewrite EU1; exact ST3w) UT3 ltac:(rewrite EU1; exact FR3) MI3) as W2.
  rewrite EU1 in W2. fold usp2 in W2.
  cl_lift W2 Hc3' c4 Hc4.
  destruct (ASTA_unpack RT Σ1 _ _ c4 Hc4) as (ms4 & (-> & ST3) & Hc4'). clear Hc4.
  rewrite EU1 in ST3. rewrite (ret_pc_even SITE_mf_mbf) in Hc4' by (unfold SITE_mf_mbf; lia).
  (* [comment removed for export] *)
  pose proof (mf_s1_walk (Z_to_bv 64 SITE_mf_mbf) sp gp y0 y1 y2 (Z_to_bv 64 1) h1 h2 h3 h4 h5 h6 h7 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6 F3 fc3 m3 BB BM R
                SPH UT3 BBC4 (proj2 (af_acc_live RT AF Σ1 m3 BB 16 ART3 INBB1)) BB0 BBAL BBHI ltac:(clear - BBLO HLO1 SPH; lia) ltac:(clear - R0 RLO HLO1 SPH; lia) MI3 eq_refl) as W3.
  fold usp usp1 in W3.
  cl_lift W3 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ1 _ _ c5 Hc5) as (ms5 & -> & Hc5'). clear Hc5.
  assert (CO4 : call_ok RT Σ1 m3 (Z_to_bv 64 usp1) lo).
  { fold usp in SPA. unfold call_ok. rewrite EU1, SP1. split; [exact ST3|]. split; [exact LOW|]. split; [unfold usp1, RT_STACK in *; clear - HSTK; lia|].
    split; [unfold usp1, USTACK_TOP in *; clear - NUM; lia|]. apply Z.mod_divide; [lia|]. apply Z.mod_divide in SPA; [|lia]. destruct SPA as (q & Hq). exists (q - 2). unfold usp1. lia. }
  assert (FRR4 : rw_cells asegs m3 (usp - 16) [C8 s0; C8 ra]).
  { apply (rw_cells_agree_nw asegs m1 m3 _ _ FRR1). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply AG04. unfold usp1, USTACK_TOP in *. clear - Hx NUM. lia. }
  assert (AG04' : agree_on (fun x => usp <= x < USTACK_TOP) m m3) by (intros x Hx; cbv beta in Hx; rewrite (AG04 x ltac:(unfold usp1; clear - Hx; lia)); exact (AG1 x Hx)).
  destruct (cl_chain_call (rt_cg RT Σ) e_mem_free e_CRYPTO_free SITE_mf_free1 m m3 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH (SITE_mf_free1, e_mem_free) ltac:(cbn; tauto)) (proj2 CGH (SITE_mf_free1, e_CRYPTO_free) ltac:(cbn; tauto)) UWC AG04' FRR4 ltac:(rewrite EU1; unfold usp1; lia) SPT) as (CTXc & UWCc).
  apply (C_FR Σ1 PMc (Z_to_bv 64 SITE_mf_free1) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) y0 y1 y2 sp (Z_to_bv 64 BB) (Z_to_bv 64 R) (Z_to_bv 64 MEM_FILE) (Z_to_bv 64 153)
           h3 h4 h5 h6 h7 (Z_to_bv 64 MEM_FILE) s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6 F3 fc3 m3 R 32 lo (bv_unsigned ra :: outer) lb canary
           FDO MST eq_refl eq_refl INR1 ART3 MI3 CO4).
  { rewrite CG1, (unsigned_lit SITE_mf_free1) by (unfold SITE_mf_free1; lia). exact CTXc. }
  { exact UWCc. }
  { rewrite CG1, (unsigned_lit SITE_mf_free1) by (unfold SITE_mf_free1; lia). apply (proj2 CGH). cbn. tauto. }
  { exact CLE3. }
  { exact Hc5'. }
  clear Hc5'. intros c6 (Σ2 & v2 & Hc6 & LV2 & FRS2 & SP2 & CR2 & CG2).
  destruct (ASTA_unpack RT Σ2 _ _ c6 Hc6) as (ms6 & (m5 & RS5 & (ART5 & MI5 & ST5) & PRES5 & CLE5) & Hc6'). clear Hc6.
  destruct RS5 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F5 & fc5 & ->).
  rewrite EU1 in ST5, PRES5. rewrite (ret_pc_even SITE_mf_free1) in Hc6' by (unfold SITE_mf_free1; lia).
  assert (INBB2 : In (BB, 16) (rt_live RT Σ2)) by (rewrite LV2; apply live_remove_keep; [exact INBB1 | cbn [fst]; exact NBR]).
  (* [comment removed for export] *)
  pose proof (mf_s2_walk (Z_to_bv 64 SITE_mf_free1) sp gp u0 u1 u2 v2 b1 b2 b3 b4 b5 b6 b7 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F5 fc5 m5 BB
                SPH ltac:(clear - BB0 BBLO HLO1 SPH; lia) MI5) as W4.
  fold usp usp1 in W4.
  cl_lift W4 Hc6' c7 Hc7.
  destruct (ASTA_unpack RT Σ2 _ _ c7 Hc7) as (ms7 & -> & Hc7'). clear Hc7.
  assert (CO5 : call_ok RT Σ2 m5 (Z_to_bv 64 usp1) lo).
  { fold usp in SPA. unfold call_ok. rewrite EU1, SP2, SP1. split; [exact ST5|]. split; [exact LOW|]. split; [unfold usp1, RT_STACK in *; clear - HSTK; lia|].
    split; [unfold usp1, USTACK_TOP in *; clear - NUM; lia|]. apply Z.mod_divide; [lia|]. apply Z.mod_divide in SPA; [|lia]. destruct SPA as (q & Hq). exists (q - 2). unfold usp1. lia. }
  assert (AG45 : forall x : word, usp1 <= bv_unsigned x < USTACK_TOP -> m5 x = m3 x) by (intros x Hx; apply PRES5; left; exact Hx).
  assert (FRR5 : rw_cells asegs m5 (usp - 16) [C8 s0; C8 ra]).
  { apply (rw_cells_agree_nw asegs m3 m5 _ _ FRR4). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply AG45. unfold usp1, USTACK_TOP in *. clear - Hx NUM. lia. }
  assert (AG05' : agree_on (fun x => usp <= x < USTACK_TOP) m m5) by (intros x Hx; cbv beta in Hx; rewrite (AG45 x ltac:(unfold usp1; clear - Hx; lia)); exact (AG04' x Hx)).
  destruct (cl_chain_call (rt_cg RT Σ) e_mem_free e_CRYPTO_free SITE_mf_free2 m m5 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH (SITE_mf_free2, e_mem_free) ltac:(cbn; tauto)) (proj2 CGH (SITE_mf_free2, e_CRYPTO_free) ltac:(cbn; tauto)) UWC AG05' FRR5 ltac:(rewrite EU1; unfold usp1; lia) SPT) as (CTXd & UWCd).
  apply (C_FR Σ2 PMc (Z_to_bv 64 SITE_mf_free2) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 sp (Z_to_bv 64 BB) (Z_to_bv 64 BB) (Z_to_bv 64 MEM_FILE) (Z_to_bv 64 154)
           b3 b4 b5 b6 b7 (Z_to_bv 64 MEM_FILE) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F5 fc5 m5 BB 16 lo (bv_unsigned ra :: outer) lb canary
           FDO MST eq_refl eq_refl INBB2 ART5 MI5 CO5).
  { rewrite CG2, CG1, (unsigned_lit SITE_mf_free2) by (unfold SITE_mf_free2; lia). exact CTXd. }
  { exact UWCd. }
  { rewrite CG2, CG1, (unsigned_lit SITE_mf_free2) by (unfold SITE_mf_free2; lia). apply (proj2 CGH). cbn. tauto. }
  { exact CLE5. }
  { exact Hc7'. }
  clear Hc7'. intros c8 (Σ3 & v3 & Hc8 & LV3 & FRS3 & SP3 & CR3 & CG3).
  destruct (ASTA_unpack RT Σ3 _ _ c8 Hc8) as (ms8 & (m6 & RS6 & (ART6 & MI6 & ST6) & PRES6 & CLE6) & Hc8'). clear Hc8.
  destruct RS6 as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & F6 & fc6 & ->).
  rewrite EU1 in ST6, PRES6. rewrite (ret_pc_even SITE_mf_free2) in Hc8' by (unfold SITE_mf_free2; lia).
  assert (AG56 : forall x : word, usp1 <= bv_unsigned x < USTACK_TOP -> m6 x = m5 x) by (intros x Hx; apply PRES6; left; exact Hx).
  assert (FR6 : rw_cells asegs m6 usp1 [C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree_nw asegs m1 m6 _ _ FR1). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    rewrite (AG56 x ltac:(unfold usp1, USTACK_TOP in *; clear - Hx NUM; lia)), (AG45 x ltac:(unfold usp1, USTACK_TOP in *; clear - Hx NUM; lia)).
    apply AG04. unfold usp1, USTACK_TOP in *. clear - Hx NUM. lia. }
  destruct (af_client_consts RT AF Σ3 m6 ART6) as (_ & _ & _ & _ & UT6).
  (* [comment removed for export] *)
  pose proof (mf_s3_walk ra (Z_to_bv 64 SITE_mf_free2) sp gp w0 w1 w2 s0 s1 s2 v3 d1 d2 d3 d4 d5 d6 d7 s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 (Z_to_bv 64 BB) (Z_to_bv 64 MEM_FILE)
                F6 fc6 m6 lo HLO1 HLOS SPH ST6 UT6 FR6 MI6) as W5.
  fold usp usp1 in W5.
  cl_lift W5 Hc8' c9 Hc9.
  apply Hk. unfold free_post_sec. exists Σ3, (Z_to_bv 64 1).
  split; [| rewrite LV3, FRS3, SP3, CR3, CG3, LV2, FRS2, SP2, CR2, CG2, LV1, FRS1, SP1, CR1, CG1; repeat split; reflexivity].
  eapply ASTA_conseq; [exact Hc9|]. cbv beta. intros ms (m7 & -> & MU7 & WM7 & MI7 & ST7). fold usp in ST7. exists m7.
  assert (E7 : forall x : word, m7 x = m6 x) by (intros x; apply MU7; exact I).
  assert (ART7 : ART RT Σ3 m7) by (apply (af_frame RT AF Σ3 m6 m7 usp1 ART6 ltac:(rewrite SP3, SP2, SP1; unfold usp1; clear - NUM; lia)); [intros x _; apply E7 | exact WM7]).
  split; [do 16 eexists; reflexivity|]. split; [exact (conj ART7 (conj MI7 ST7))|].
  enough (AG07 : forall x : word, aclient (rt_live RT Σ3) (rt_frames RT Σ) usp (bv_unsigned x) -> m7 x = m x).
  { split; [exact AG07|]. split; [apply (cl_env_agree m6 m7 lb canary CLE6); intros a _; apply E7|]. apply (sec_off_agree m m7 SEC). intros a Ha. apply AG07. right; left. rewrite Ha. exact sec_init_static. }
  assert (SUB31 : forall e, In e (rt_live RT Σ3) -> In e (rt_live RT Σ1)) by (intros e He; rewrite LV3, LV2 in He; exact (live_remove_sub _ _ _ (live_remove_sub _ _ _ He))).
  assert (SUB30 : forall e, In e (rt_live RT Σ3) -> In e (rt_live RT Σ)) by (intros e He; pose proof (SUB31 e He) as He1; rewrite LV1 in He1; exact (live_remove_sub _ _ _ (live_remove_sub _ _ _ He1))).
  intros x Hx. rewrite E7.
  rewrite (PRES6 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | rewrite FRS2, FRS1; auto | unfold usp1; clear; lia])).
  rewrite (PRES5 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [rewrite LV3; intros e He; exact (live_remove_sub _ _ _ He) | rewrite FRS1; auto | unfold usp1; clear; lia])).
  rewrite (PRES3 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [exact SUB31 | auto | unfold usp2, usp1; clear; lia])).
  rewrite (PR2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [exact SUB30 | auto | unfold usp1; clear; lia]) I).
  exact (PR1 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [exact SUB30 | auto | clear; lia]) I).
Qed.
End CFree.
