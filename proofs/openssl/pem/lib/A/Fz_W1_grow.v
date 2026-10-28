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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_W4_kit Fz_env Fz_M_malloc Fz_M_clear_free Fz_M_clear_realloc Fz_W1_defs Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition SITE_gr_fit : Z := 0x24a338.
Definition SITE_gr_ccr : Z := 0x24a3b8.
Definition SITE_gr_tail : Z := 0x24a414.
Definition BUF_FILE_LIT : Z := 0x73520.
Definition gr_frame (s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell := [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition gr_fit_post (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s4' s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' s3' s5' s6' s7' : word) (BM D len len' lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (j : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_gr_fit) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 sp (Z_to_bv 64 len') (Z_to_bv 64 (D + len)) (Z_to_bv 64 0) (Z_to_bv 64 (len' - len))
                 a3 a4 a5 a6 a7 (Z_to_bv 64 BM) (Z_to_bv 64 (BM + 16)) s4' (Z_to_bv 64 (BM ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BM + 16) ≫ 3 + 2147450880))
                 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_asan_memset) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -80) (CB 8 j :: gr_frame s7' s6' s5' s4' s3' s2' s1' s0' ra0) /\ stk asegs m' lo (bv_unsigned sp + -80).

Lemma gr_fit_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BM D len max len' : Z) (flw : word),
  lo <= bv_unsigned sp - 80 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m BM (bufmem_cells len D max flw) -> acc asegs m BM 32 -> 0 < BM -> BM mod 16 = 0 -> 0x10007fff8000 <= BM -> BM + 32 <= lo ->
  0 < D -> D + max < 2^63 -> 0 <= len -> len < len' -> len' <= max -> mem_inv asegs m ->
  evt asegs (gr_fit_post sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 a3 a4 a5 a6 a7 s4' s8 s9 s10 s11 t3 t4 t5 t6 F fc ra0 s0' s1' s2' s3' s5' s6' s7' BM D len len' lo m)
    (MS (mkR ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' (Z_to_bv 64 BM) (Z_to_bv 64 len') a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_BUF_MEM_grow_clean) fc None m (seg_rom asegs)).
Proof.
  intros until flw. intros HLO HLOS SPH ST UT SHC BMC ACCBM BM0 BMAL BMHI BMLO D0 DMAX HLEN HLT HFIT MI.
  unfold e_BUF_MEM_grow_clean, g_shadow_memory_dynamic_address, bufmem_cells in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 80, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 80, SP)]) by ut_fp_lia. assert (HWS : sh_fp [(SP - 80, SP)]) by sh_fp_lia.
  assert (BMAL8 : BM mod 8 = 0) by (clear - BMAL; Z.div_mod_to_equations; lia).
  assert (EUBM : bv_unsigned (Z_to_bv 64 BM) = BM) by (apply unsigned_lit; lia).
  th_frame 80%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  zstep. do 9 zstep. zstep.
  zstep. zstep. zstep.
  do 4 zstep. zstep. th_if_lit.
  zstep. zstep. zstep. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  do 4 zstep. zstep. th_if_lit.
  zstep. zstep. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  do 4 zstep. zstep. th_if_lit.
  zstep. zstep. rewrite ?(unsigned_lit D), ?(unsigned_lit len) by lia.
  zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold gr_fit_post, SITE_gr_fit, e_asan_memset, gr_frame. apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [eassumption| assumption].
Qed.

(* [comment removed for export] *)
Definition gr_tail_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (BM D max len' lo : Z) (flw : word) (m : mem)
    : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 len') a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(BM, BM + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' BM (bufmem_cells len' D max flw).

Lemma gr_fit2_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BM D len max len' : Z) (flw : word) (j : list byte),
  lo <= bv_unsigned sp - 80 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp + -80) -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m (bv_unsigned sp + -80) (CB 8 j :: gr_frame s7' s6' s5' s4' s3' s2' s1' s0' ra0) ->
  rw_cells asegs m BM (bufmem_cells len D max flw) -> acc asegs m BM 32 -> 0 < BM -> BM mod 16 = 0 -> 0x10007fff8000 <= BM -> BM + 32 <= lo ->
  0 <= len' < 2^63 -> mem_inv asegs m ->
  evt asegs (gr_tail_post ra0 sp gp (Z_to_bv 64 0xba3ef0) s0' s1' s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 F fc BM D max len' lo flw m)
    (MS (mkR (Z_to_bv 64 SITE_gr_fit) (Z_to_bv 64 (bv_unsigned sp + -80)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 len') a0 a1 a2
             a3 a4 a5 a6 a7 (Z_to_bv 64 BM) (Z_to_bv 64 (BM + 16)) s4' (Z_to_bv 64 (BM ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BM + 16) ≫ 3 + 2147450880))
             s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_gr_fit) fc None m (seg_rom asegs)).
Proof.
  intros until j. intros HLO HLOS SPH ST UT SHC FR BMC ACCBM BM0 BMAL BMHI BMLO HLEN MI.
  unfold SITE_gr_fit, g_shadow_memory_dynamic_address, bufmem_cells, gr_frame in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(BM, BM + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(BM, BM + 8)]) by ut_fp_lia. assert (HWS : sh_fp [(BM, BM + 8)]) by sh_fp_lia.
  assert (BMAL8 : BM mod 8 = 0) by (clear - BMAL; Z.div_mod_to_equations; lia).
  zstep. zstep. th_if_lit.
  zstep. zstep.
  do 9 zstep. zstep. th_release FR SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold gr_tail_post, bufmem_cells. apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
Lemma gr_div3_magic : forall x, 0 <= x < 2 ^ 32 -> x * 2863311531 / 2 ^ 33 = x / 3.
Proof.
  intros x Hx. pose proof (Z.div_mod x 3 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound x 3 ltac:(lia)) as MB.
  symmetry. apply (Z.div_unique _ _ _ (x / 3 + (x mod 3) * 2863311531)); lia.
Qed.
Lemma gr_n_arith : forall y, 0 <= y < 2 ^ 31 ->
  Z.land (bv_swrap 32 (bv_wrap 32 (Z.land ((Z.land (y ≪ 32) 18446744073709551615 * 12297829383904690176) ≫ 64) 18446744073709551615 ≫ 31) ≫ 2))
         18446744073709551615 ≪ 2 = y / 3 * 4.
Proof.
  intros y Hy. change 18446744073709551615 with (Z.ones 64). rewrite !Z.land_ones by lia.
  rewrite (Z.shiftl_mul_pow2 y 32) by lia. rewrite (Z.mod_small (y * 2 ^ 32)) by lia.
  replace (y * 2 ^ 32 * 12297829383904690176) with (y * 2863311531 * 2 ^ 64) by lia.
  rewrite (Z.shiftr_div_pow2 _ 64), Z.div_mul by lia. rewrite (Z.mod_small (y * 2863311531)) by lia.
  rewrite (Z.shiftr_div_pow2 _ 31) by lia.
  assert (C31 : 0 <= y * 2863311531 / 2 ^ 31 < 2 ^ 32) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small _ _ C31).
  rewrite (Z.shiftr_div_pow2 _ 2), Z.div_div by lia. change (2 ^ 31 * 2 ^ 2) with (2 ^ 33). rewrite gr_div3_magic by lia.
  assert (Q : 0 <= y / 3 < 2 ^ 30) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 `div` 2) with (2 ^ 31).
  rewrite (Z.mod_small (y / 3 + 2 ^ 31)) by lia. replace (y / 3 + 2 ^ 31 - 2 ^ 31) with (y / 3) by lia.
  rewrite (Z.mod_small (y / 3)) by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.
Definition gr_n (len' : Z) : Z := (len' + 3) / 3 * 4.
Definition SITE_gr_secre : Z := 0x24a3d0.

(* [comment removed for export] *)
Definition gr_g0_post (sp gp tp t0 t1 t2 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' : word) (BM D max len' sec lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a2x : word) (j : list byte) (m' : mem),
    ms = (if sec =? 0
          then MS (mkR (Z_to_bv 64 SITE_gr_ccr) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 sp (Z_to_bv 64 len') (Z_to_bv 64 D) (Z_to_bv 64 max) (Z_to_bv 64 (gr_n len'))
                 (Z_to_bv 64 BUF_FILE_LIT) (Z_to_bv 64 132) a5 a6 a7 (Z_to_bv 64 BM) (Z_to_bv 64 (BM + 16)) (Z_to_bv 64 (gr_n len')) (Z_to_bv 64 (BM ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000)
                 (Z_to_bv 64 ((BM + 16) ≫ 3 + 2147450880)) s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_CRYPTO_clear_realloc) fc None m' (seg_rom asegs)
          else MS (mkR (Z_to_bv 64 SITE_gr_secre) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 sp (Z_to_bv 64 len') (Z_to_bv 64 BM) (Z_to_bv 64 (gr_n len')) a2x
                 (Z_to_bv 64 12297829383904690176) a4 a5 a6 a7 (Z_to_bv 64 BM) (Z_to_bv 64 (BM + 16)) (Z_to_bv 64 (gr_n len')) (Z_to_bv 64 (BM ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000)
                 (Z_to_bv 64 ((BM + 16) ≫ 3 + 2147450880)) s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_sec_alloc_realloc) fc None m' (seg_rom asegs))
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -80) (CB 8 j :: gr_frame s7' s6' s5' s4' s3' s2' s1' s0' ra0) /\ stk asegs m' lo (bv_unsigned sp + -80).

Lemma gr_g0_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BM D len max len' sec : Z) (flw : word),
  lo <= bv_unsigned sp - 80 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m BM (bufmem_cells len D max flw) -> rw_cells asegs m (BM + 24) [C1 (Z_to_bv 8 sec)] ->
  acc asegs m BM 32 -> 0 < BM -> BM mod 16 = 0 -> 0x10007fff8000 <= BM -> BM + 32 <= lo ->
  0 <= D -> D + max < 2^63 -> 0 <= len <= max -> max < len' -> len' < 0x5ffffffd -> (sec = 0 \/ sec = 1) -> mem_inv asegs m ->
  evt asegs (gr_g0_post sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ra0 s0' s1' s2' s3' s4' s5' s6' s7' BM D max len' sec lo m)
    (MS (mkR ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' (Z_to_bv 64 BM) (Z_to_bv 64 len') a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_BUF_MEM_grow_clean) fc None m (seg_rom asegs)).
Proof.
  intros until flw. intros HLO HLOS SPH ST UT SHC BMC FB ACCBM BM0 BMAL BMHI BMLO D0 DMAX HLEN HLT HLIM HSEC MI.
  unfold e_BUF_MEM_grow_clean, g_shadow_memory_dynamic_address, bufmem_cells in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 80, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 80, SP)]) by ut_fp_lia. assert (HWS : sh_fp [(SP - 80, SP)]) by sh_fp_lia.
  assert (BMAL8 : BM mod 8 = 0) by (clear - BMAL; Z.div_mod_to_equations; lia).
  assert (EUBM : bv_unsigned (Z_to_bv 64 BM) = BM) by (apply unsigned_lit; lia).
  th_frame 80%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  zstep. do 9 zstep. zstep.
  zstep. zstep. zstep.
  do 4 zstep. zstep. th_if_lit.
  zstep. zstep. zstep. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  do 4 zstep. zstep. th_if_lit.
  zstep. zstep. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  zstep. zstep. zstep. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit in K2 by lia. lia. }
  do 4 zstep. zstep. th_if_lit.
  zstep. zstep. zstep. cbv beta. rewrite (Z_to_bv_unsigned 8 sec), (bv_wrap_small 8 sec) by (unfold bv_modulus; cbn [Z.of_N Z.pow_pos Pos.iter Z.mul Pos.mul]; lia).
  do 8 zstep. rewrite (gr_n_arith (len' + 3)) by lia.
  destruct HSEC as [-> | ->].
  - change (Z.land 0 1) with 0. zstep. th_if_lit.
    do 4 zstep. zstep. th_if_lit.
    do 5 zstep. zstep.
    subst SP. rewrite ?Z_to_bv_bv_unsigned.
    unfold gr_g0_post, gr_n, SITE_gr_ccr, e_CRYPTO_clear_realloc, BUF_FILE_LIT, gr_frame. cbn [Z.eqb]. apply evt_done. exists a2. do 2 eexists. split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [eassumption| assumption].
  - change (Z.land 1 1) with 1. zstep. th_if_lit.
    zstep. zstep. zstep.
    subst SP. rewrite ?Z_to_bv_bv_unsigned.
    unfold gr_g0_post, gr_n, SITE_gr_secre, e_sec_alloc_realloc, gr_frame. cbn [Z.eqb]. apply evt_done. do 3 eexists. split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [eassumption| assumption].
Qed.

(* [comment removed for export] *)
Definition gr_g2_post (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' : word) (BM q n len len' lo : Z) (flw : word) (j : list byte) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_gr_tail) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 sp (Z_to_bv 64 len') (Z_to_bv 64 (q + len)) (Z_to_bv 64 0) (Z_to_bv 64 (len' - len))
                 a3 a4 a5 a6 a7 (Z_to_bv 64 BM) (Z_to_bv 64 (BM + 16)) (Z_to_bv 64 n) (Z_to_bv 64 (BM ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BM + 16) ≫ 3 + 2147450880))
                 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_asan_memset) fc None m' (seg_rom asegs)
    /\ munch [(BM + 8, BM + 24)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -80) (CB 8 j :: gr_frame s7' s6' s5' s4' s3' s2' s1' s0' ra0) /\ stk asegs m' lo (bv_unsigned sp + -80)
    /\ rw_cells asegs m' BM (bufmem_cells len q n flw).

Lemma gr_g2_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BM D q n len max len' : Z) (flw : word) (j : list byte),
  lo <= bv_unsigned sp - 80 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp + -80) -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m (bv_unsigned sp + -80) (CB 8 j :: gr_frame s7' s6' s5' s4' s3' s2' s1' s0' ra0) ->
  rw_cells asegs m BM (bufmem_cells len D max flw) -> acc asegs m BM 32 -> 0 < BM -> BM mod 16 = 0 -> 0x10007fff8000 <= BM -> BM + 32 <= lo ->
  0 < q -> q + n < 2^63 -> 0 <= n -> 0 <= len <= len' -> len' < 2^40 -> 0 <= D < 2^64 -> 0 <= max < 2^64 -> mem_inv asegs m ->
  evt asegs (gr_g2_post sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ra0 s0' s1' s2' s3' s4' s5' s6' s7' BM q n len len' lo flw j m)
    (MS (mkR (Z_to_bv 64 SITE_gr_ccr) (Z_to_bv 64 (bv_unsigned sp + -80)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 len') (Z_to_bv 64 q) a1 a2
             a3 a4 a5 a6 a7 (Z_to_bv 64 BM) (Z_to_bv 64 (BM + 16)) (Z_to_bv 64 n) (Z_to_bv 64 (BM ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BM + 16) ≫ 3 + 2147450880))
             s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_gr_ccr) fc None m (seg_rom asegs)).
Proof.
  intros until j. intros HLO HLOS SPH ST UT SHC FR BMC ACCBM BM0 BMAL BMHI BMLO Q0 QHI HN HLEN HL40 HD HMAX MI.
  unfold SITE_gr_ccr, g_shadow_memory_dynamic_address, bufmem_cells, gr_frame in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(BM + 8, BM + 24)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(BM + 8, BM + 24)]) by ut_fp_lia. assert (HWS : sh_fp [(BM + 8, BM + 24)]) by sh_fp_lia.
  assert (BMAL8 : BM mod 8 = 0) by (clear - BMAL; Z.div_mod_to_equations; lia).
  assert (EUQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  zstep. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  do 4 zstep. zstep. th_if_lit.
  zstep.
  zstep. zstep. th_if_lit.
  zstep.
  zstep. zstep. th_if_lit.
  zstep.
  do 3 zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold gr_g2_post, SITE_gr_tail, e_asan_memset, gr_frame, bufmem_cells. apply evt_done. eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
Lemma gr_tail_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6 (s3x s4x s5x s6x s7x : word)
    (F : bvmap 5 word) fc (m : mem) (lo BM D len max len' : Z) (flw : word) (j : list byte),
  lo <= bv_unsigned sp - 80 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp + -80) -> img_untouched m ->
  rw_cells asegs m (bv_unsigned sp + -80) (CB 8 j :: gr_frame s7' s6' s5' s4' s3' s2' s1' s0' ra0) ->
  rw_cells asegs m BM (bufmem_cells len D max flw) -> acc asegs m BM 32 -> 0 < BM -> BM mod 16 = 0 -> 0x10007fff8000 <= BM -> BM + 32 <= lo ->
  0 <= len' < 2^63 -> mem_inv asegs m ->
  evt asegs (gr_tail_post ra0 sp gp (Z_to_bv 64 0xba3ef0) s0' s1' s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 F fc BM D max len' lo flw m)
    (MS (mkR (Z_to_bv 64 SITE_gr_tail) (Z_to_bv 64 (bv_unsigned sp + -80)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 len') a0 a1 a2
             a3 a4 a5 a6 a7 (Z_to_bv 64 BM) s3x s4x (Z_to_bv 64 (BM ≫ 3 + 2147450880)) s6x s7x s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_gr_tail) fc None m (seg_rom asegs)).
Proof.
  intros until j. intros HLO HLOS SPH ST UT FR BMC ACCBM BM0 BMAL BMHI BMLO HLEN MI.
  unfold SITE_gr_tail, bufmem_cells, gr_frame in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(BM, BM + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(BM, BM + 8)]) by ut_fp_lia. assert (HWS : sh_fp [(BM, BM + 8)]) by sh_fp_lia.
  assert (BMAL8 : BM mod 8 = 0) by (clear - BMAL; Z.div_mod_to_equations; lia).
  zstep. zstep.
  do 9 zstep. zstep. th_release FR SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold gr_tail_post, bufmem_cells. apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
Definition cr0_post (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms => exists m', ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_CRYPTO_malloc) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).
Lemma cr0_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> bv_unsigned sp <= 2^47 -> mem_inv asegs m ->
  evt asegs (cr0_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_CRYPTO_clear_realloc m).
Proof.
  unfold entry_st, e_CRYPTO_clear_realloc. intros until lo; intros ST HLO SPH MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP; rewrite <- (Z_to_bv_bv_unsigned sp); rewrite <- ESP.
  pose proof (munch_refl [(SP - 64, SP)] m) as MU; pose proof (wmono_refl asegs m) as WM.
  th_frame 64%nat [8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  zstep. do 7 zstep. zstep.
  zstep. zstep. zstep. th_if_lit.
  zstep. zstep. zstep. do 7 zstep. zstep. th_release FR SP. zstep.
  subst SP; rewrite ?Z_to_bv_bv_unsigned.
  unfold cr0_post, e_CRYPTO_malloc; apply evt_done; eexists; split; [reflexivity|].
  split; [assumption|]; split; [assumption|]; split; assumption.
Qed.

Lemma live_CB : forall RT (AF : art_facts RT) (Σ : rts RT) (m : mem) p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> 0 <= n ->
  exists junk, length junk = Z.to_nat n /\ rw_cells asegs m p [CB (Z.to_nat n) junk].
Proof.
  intros RT AF Σ m p n HA Hin Hn. destruct (wr_at_rw_CB m p n (proj1 (af_acc_live RT AF Σ m p n HA Hin)) Hn) as (junk & H).
  exists junk. split; [exact (proj1 (proj1 (proj1 H))) | exact H].
Qed.

(* [comment removed for export] *)
Lemma fresh_apart : forall RT (AF : art_facts RT) (Σ1 : rts RT) (m1 : mem) p n L usp a,
  ART RT Σ1 m1 -> rt_live RT Σ1 = (p, n) :: L -> rt_sp0 RT Σ1 - STACK_WIN <= usp -> 0 <= n -> aclient L (rt_frames RT Σ1) usp a -> ~ (p <= a < p + n).
Proof.
  intros RT AF Σ1 m1 p n L usp a ART1 LV LU Hn Ha.
  assert (INL : In (p, n) (rt_live RT Σ1)) by (rewrite LV; left; reflexivity).
  pose proof (af_live_range RT AF Σ1 m1 p n ART1 INL) as (R0 & R1 & R2).
  destruct Ha as [H|[H|[H|[H|H]]]].
  - lia.
  - pose proof (client_static_range a H). unfold SEGTOP_A in *. lia.
  - destruct H as (p2 & n2 & Hin & Hp). destruct (af_live_disj RT AF Σ1 m1 p n p2 n2 [] L ART1 LV Hin); lia.
  - destruct H as (f & k & Hin & Hf). pose proof (af_frames_range RT AF Σ1 m1 f k ART1 Hin) as (_ & _ & _ & R3). destruct (R3 p n INL); lia.
  - destruct H as (f & k & Hin & Hf). pose proof (af_fshadow_apart RT AF Σ1 m1 f k ART1 Hin) as (SL & _). destruct (SL p n INL); lia.
Qed.

Lemma gr_n_gt : forall x, 0 <= x -> x < gr_n x.
Proof. intros x Hx. unfold gr_n. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma flags_byte : forall (m : mem) BM len D max sec, (sec = 0 \/ sec = 1) -> rw_cells asegs m BM (bufmem_cells len D max (Z_to_bv 64 sec)) ->
  rw_cells asegs m (BM + 24) [C1 (Z_to_bv 8 sec)].
Proof.
  intros m BM len D max sec HS H. unfold bufmem_cells in H.
  pose proof (rw_cells_skip m BM [C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 max)] [C8 (Z_to_bv 64 sec)] H) as H8. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H8.
  apply (rw_cells_head m (BM + 24) (C1 (Z_to_bv 8 sec)) [CB 7 (tl (le8 (Z_to_bv 64 sec)))]).
  apply (rw_cells_recast m (BM + 24) _ _ H8); destruct HS as [-> | ->]; vm_compute; repeat split; reflexivity.
Qed.

Section CGr.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_CM : crypto_malloc_env_stmt RT.
Hypothesis MSI : memset_icontract RT e_asan_memset.
Hypothesis C_CCR : crypto_clear_realloc_env_stmt RT.

(* [comment removed for export] *)
Definition ccr_null_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (n lo : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 n -> tp = Z_to_bv 64 0xba3ef0 -> 1 <= n <= 0x8000000 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 64 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_CRYPTO_clear_realloc (bv_unsigned ra :: outer) -> In (bv_unsigned ra, e_CRYPTO_malloc) (cg_call (rt_cg RT Σ)) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) [(SITE_cm_malloc, e_CRYPTO_malloc)] [(SITE_cm_malloc, e_malloc)] ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost n <= rt_credit RT Σ -> cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_CRYPTO_clear_realloc m)))
    (fun c => exists (Σ' : rts RT) (p : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
           /\ cl_env m' (Z_to_bv 8 1) canary /\ wr_at asegs m' p n /\ acc asegs m' p n) c
       /\ rt_live RT Σ' = (p, n) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - mcost n /\ 0 < p /\ p mod 16 = 0 /\ p + n < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem ccr_null_cps : ccr_null_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n lo outer lb canary
    FDO MST -> A2 TP Hn ART0 MI0 CALL HSTK CTX TAIL UWC CGH Hlen Hcr CLE T c HA Hk.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA). pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof (cr0_walk ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo ST ltac:(unfold RT_STACK in HSTK; clear - HSTK; lia)
                ltac:(unfold USTACK_TOP in SPT; clear - SPT; lia) MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & ST1) & Hc1'). clear Hc1.
  pose proof (cl_seg_ART RT AF Σ m m1 (bv_unsigned sp) 64 [] ART0 ltac:(unfold RT_STACK in *; lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  assert (P1 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (bv_unsigned x) -> m1 x = m x).
  { intros x Hx. apply MU1. cbn [outside]. split; [| exact I]. destruct (cl_split RT AF Σ m (bv_unsigned sp) 64 _ ART0 ltac:(unfold RT_STACK in *; lia) ltac:(lia) Hx); lia. }
  apply (C_CM Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 n lo outer lb canary FDO MST A2 TP Hn ART1 MI1
           (conj ST1 (conj LOW (conj LOR (conj SPT SPA)))) ltac:(unfold RT_STACK in *; clear - HSTK; lia) (conj TAIL (proj2 CTX))
           (uw_chain_agree outer m m1 sp s0 UWC ltac:(intros x Hx; cbv beta in Hx; apply P1; apply acl_stack; exact Hx)) CGH Hlen Hcr
           (cl_env_seg _ m m1 lb canary CLE MU1 ltac:(cl_fp_lia)) T c1 Hc1').
  intros c2 (Σ' & p & Hc2 & REST). apply Hk. exists Σ', p. split; [| exact REST].
  eapply ASTA_conseq; [exact Hc2|]. intros ms (m' & RS & (ART' & MI' & WM' & ST') & PRES & REST'). exists m'.
  split; [exact RS|]. split; [exact (conj ART' (conj MI' (conj (wmono_trans asegs _ _ _ WM1 WM') ST')))|]. split; [| exact REST'].
  intros x Hx Ho. rewrite (PRES x Hx Ho). exact (P1 x Hx).
Qed.

Definition GRF_W (BM D max : Z) : list (Z * Z) := [(BM, BM + 8); (D, D + max)].

(* [comment removed for export] *)
Definition grow_fit_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BM D len max len' : Z) (flw : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BM -> a1 = Z_to_bv 64 len' ->
  In (BM, 32) (rt_live RT Σ) -> BM mod 16 = 0 -> rw_cells asegs m BM (bufmem_cells len D max flw) -> In (D, max) (rt_live RT Σ) -> D <> BM ->
  0 <= len -> len < len' -> len' <= max -> max < 2 ^ 31 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 80 <= bv_unsigned sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_BUF_MEM_grow_clean m)))
    (ASTA RT Σ PMc (fun ms => exists (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 len') m' ms
        /\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (GRF_W BM D max) m m'
        /\ rw_cells asegs m' BM (bufmem_cells len' D max flw))).

Theorem grow_fit_cps : grow_fit_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BM D len max len' flw
    FDO MST -> -> -> INBM BMAL BMC IND NDBM HLEN HLT HFIT HMAX ART0 MI0 CALL HSTK.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 80 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -80).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (HLO1 : lo <= usp - 80) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (af_live_range RT AF Σ m BM 32 ART0 INBM) as (BM0 & BMLO' & _). assert (BMLO : BM + 32 <= lo) by (clear - BMLO' LOW; lia). clear BMLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BM 32 ART0 INBM ltac:(lia)) as BMHI. pose proof (proj2 (af_acc_live RT AF Σ m BM 32 ART0 INBM)) as ACCBM.
  pose proof (af_live_range RT AF Σ m D max ART0 IND) as (D0 & DLO' & _). assert (DLO : D + max <= lo) by (clear - DLO' LOW; lia). clear DLO'.
  assert (DMAX : D + max < 2 ^ 63) by (clear - DLO HLO1 SPH; lia).
  pose proof (live_ne_apart RT AF Σ m D max BM 32 ART0 IND INBM ltac:(intros E; injection E; intros _; exact NDBM)) as APDBM.
  (* [comment removed for export] *)
  pose proof (gr_fit_walk ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BM D len max len' flw
                HLO1 HLOS SPH ST UT SHC BMC ACCBM BM0 BMAL BMHI BMLO D0 DMAX HLEN HLT HFIT MI0) as W0.
  fold usp in W0. fold usp1 in W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (j & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 80 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  assert (P1 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> m1 x = m x).
  { intros x Hx. apply MU1. cbn [outside]. split; [| exact I]. destruct (cl_split RT AF Σ m usp 80 _ ART0 ltac:(lia) ltac:(lia) Hx); lia. }
  assert (COP : lo + RT_STACK <= usp1 /\ usp1 + 16 <= USTACK_TOP /\ usp1 mod 16 = 0).
  { fold usp in SPA. unfold usp1. split; [unfold RT_STACK in *; clear - HSTK; lia|]. split; [unfold USTACK_TOP in *; clear - NUM; lia|].
    apply Z.mod_divide; [lia|]. apply Z.mod_divide in SPA; [|lia]. destruct SPA as (q & Hq). exists (q - 5). lia. }
  assert (CO1 : call_ok RT Σ m1 (Z_to_bv 64 usp1) lo) by (unfold call_ok; rewrite EU1; exact (conj ST1 (conj LOW COP))).
  (* [comment removed for export] *)
  apply (MSI Σ PMc (Z_to_bv 64 SITE_gr_fit) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 len') (Z_to_bv 64 (D + len)) (Z_to_bv 64 0) (Z_to_bv 64 (len' - len))
           a3 a4 a5 a6 a7 (Z_to_bv 64 BM) (Z_to_bv 64 (BM + 16)) s4 (Z_to_bv 64 (BM ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BM + 16) ≫ 3 + 2147450880))
           s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 (D + len) (len' - len) (Z_to_bv 8 0) lo FDO MST eq_refl eq_refl eq_refl
           ltac:(clear - D0 DLO HLO1 SPH HLEN HLT HFIT; lia) ltac:(clear - HLEN HLT HFIT HMAX; lia)).
  { exact (live_checked_dst RT AF Σ m1 _ D max (D + len) (len' - len) ART1 IND ltac:(clear - HLEN; lia) ltac:(clear - HFIT; lia) ltac:(clear - HLT; lia)). }
  { exact ART1. } { exact MI1. } { exact CO1. }
  { exact Hc1'. }
  clear Hc1'. intros c2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & ZB2) & Hc2'). clear Hc2.
  destruct RS2 as (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_gr_fit) in Hc2' by (unfold SITE_gr_fit; lia).
  assert (P2 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (D <= bv_unsigned x < D + max) -> m2 x = m x).
  { intros x Hx HnD. rewrite (PRES2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; lia]) ltac:(clear - HnD HLEN HFIT; lia)). exact (P1 x Hx). }
  assert (FR2 : rw_cells asegs m2 usp1 (CB 8 j :: gr_frame s7 s6 s5 s4 s3 s2 s1 s0 ra)).
  { apply (rw_cells_agree asegs m1 m2 _ _ FR1); [| exact WM2]. intros x Hx. cbv beta in Hx. unfold gr_frame in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply PRES2; [left; unfold usp1, USTACK_TOP in *; clear - Hx NUM; lia | unfold usp1 in Hx; clear - Hx DLO HLO1 HLEN HFIT; lia]. }
  assert (BMC2 : rw_cells asegs m2 BM (bufmem_cells len D max flw)).
  { apply (rw_cells_agree asegs m m2 _ _ BMC); [| exact (wmono_trans asegs _ _ _ WM1 WM2)]. intros x Hx. cbv beta in Hx. unfold bufmem_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply P2; [apply (acl_live _ _ _ BM 32); [exact INBM | clear - Hx; lia] | clear - Hx APDBM; lia]. }
  destruct (af_client_consts RT AF Σ m2 ART2) as (_ & SHC2 & _ & _ & UT2). pose proof (proj2 (af_acc_live RT AF Σ m2 BM 32 ART2 INBM)) as ACCBM2.
  (* [comment removed for export] *)
  pose proof (gr_fit2_walk ra sp gp y0 y1 y2 s0 s1 (Z_to_bv 64 (D + len)) h1 h2 h3 h4 h5 h6 h7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6 F2 fc2 m2 lo BM D len max len' flw j
                HLO1 HLOS SPH ST2 UT2 SHC2 FR2 BMC2 ACCBM2 BM0 BMAL BMHI BMLO ltac:(clear - HLEN HLT HFIT HMAX; lia) MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  apply Hk. eapply ASTA_conseq; [exact Hc3|]. intros ms (z0 & z1 & z2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & z3 & z4 & z5 & z6 & m3 & -> & MU3 & WM3 & MI3 & ST3 & BMC3).
  fold usp in ST3. exists m3. split; [do 16 eexists; reflexivity|].
  assert (ART3 : ART RT Σ m3).
  { apply (af_frame RT AF Σ m2 m3 usp1 ART2 ltac:(unfold usp1; lia)); [| exact WM3].
    intros x Hx. apply MU3. cbn [outside]. split; [| exact I]. intros Hin; apply Hx. apply (acl_live _ _ _ BM 32); [exact INBM | clear - Hin; lia]. }
  split; [exact (conj ART3 (conj MI3 (conj (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 WM3)) ST3)))|].
  split; [| exact BMC3].
  intros x Hx Ho. unfold GRF_W in Ho. cbn [outside] in Ho. rewrite (MU3 x ltac:(cbn [outside]; clear - Ho; lia)). apply P2; [exact Hx | clear - Ho; lia].
Qed.
Definition CCR_SITES : list (Z * Z) := [(SITE_ccr_malloc, e_CRYPTO_clear_realloc); (SITE_cm_malloc, e_CRYPTO_malloc); (SITE_ccr_cfree, e_CRYPTO_clear_realloc)].
Definition CCR_CALLS : list (Z * Z) := [(SITE_ccr_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc); (SITE_ccr_cfree, e_CRYPTO_clear_free); (SITE_ccr_cfree, e_free)].

(* [comment removed for export] *)
Lemma ccr_opt : forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (p n0 old num lo : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 old -> a2 = Z_to_bv 64 num -> tp = Z_to_bv 64 0xba3ef0 ->
  ((p = 0 /\ old = 0) \/ (In (p, n0) (rt_live RT Σ) /\ 1 <= old <= n0)) -> old <= num -> 1 <= num <= 0x8000000 -> old < 2 ^ 40 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x100 + 64 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_CRYPTO_clear_realloc (bv_unsigned ra :: outer) -> In (bv_unsigned ra, e_CRYPTO_malloc) (cg_call (rt_cg RT Σ)) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) CCR_SITES CCR_CALLS ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost num <= rt_credit RT Σ -> cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_CRYPTO_clear_realloc m)))
    (fun c => exists (Σ' : rts RT) (q : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 q) m' ms
           /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (live_remove p (rt_live RT Σ)) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
           /\ cl_env m' (Z_to_bv 8 1) canary /\ wr_at asegs m' q num /\ acc asegs m' q num) c
       /\ rt_live RT Σ' = (q, num) :: live_remove p (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - mcost num /\ 0 < q /\ q mod 16 = 0 /\ q + num < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ).
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n0 old num lo outer lb canary
    FDO MST A0 A1 A2 TP HP Hon Hnum Ho40 ART0 MI0 CALL HSTK CTX TAIL UWC CGH Hlen Hcr CLE T c HA Hk.
  destruct HP as [(-> & ->) | (Hin & Hold)].
  - assert (NZ : forall e, In e (rt_live RT Σ) -> fst e <> 0).
    { intros (p' & n') He. cbn [fst]. pose proof (af_live_range RT AF Σ m p' n' ART0 He). lia. }
    rewrite (live_remove_notin 0 (rt_live RT Σ) NZ) in Hk.
    apply (ccr_null_cps Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m num lo outer lb canary
             FDO MST A0 A2 TP ltac:(clear - Hnum; lia) ART0 MI0 CALL ltac:(clear - HSTK; unfold RT_STACK in *; lia) CTX TAIL UWC
             ltac:(split; intros x Hx; [apply (proj1 CGH) | apply (proj2 CGH)]; cbn [CCR_SITES CCR_CALLS In] in Hx |- *; clear - Hx; tauto) Hlen Hcr CLE T c HA).
    intros c' (Σ' & q & H' & REST). apply Hk. exists Σ', q. split; [| exact REST].
    eapply ASTA_conseq; [exact H'|]. intros ms (m' & RS & AFT & R'). exists m'. exact (conj RS (conj (rt_after_f_of _ _ _ _ _ _ AFT) R')).
  - apply (C_CCR Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n0 old num lo outer lb canary
             FDO MST A0 A1 A2 TP Hin Hold ltac:(clear - Hon Hnum; lia) Ho40 ART0 MI0 CALL HSTK CTX UWC CGH Hlen Hcr CLE T c HA).
    intros c' (Σ' & q & H' & REST). apply Hk. exists Σ', q. split; [| exact REST].
    eapply ASTA_conseq; [exact H'|]. intros ms (m' & RS & AFT & PR & CL & WR & ACC & _). exists m'. exact (conj RS (conj AFT (conj PR (conj CL (conj WR ACC))))).
Qed.

Definition GR_SITES : list (Z * Z) := (SITE_gr_ccr, e_BUF_MEM_grow_clean) :: CCR_SITES.
Definition GR_CALLS : list (Z * Z) := (SITE_gr_ccr, e_CRYPTO_clear_realloc) :: (SITE_gr_ccr, e_CRYPTO_malloc) :: CCR_CALLS.
Definition GR_W (BM : Z) : list (Z * Z) := [(BM, BM + 24); (G_ALLOW_CUST, G_ALLOW_CUST + 1)].
(* [comment removed for export] *)
Definition data_opt (live : list (Z * Z)) (BM D max : Z) : Prop := (D = 0 /\ max = 0) \/ (In (D, max) live /\ 1 <= max /\ D <> BM).

(* [comment removed for export] *)
Definition grow_re_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BM D len max len' : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BM -> a1 = Z_to_bv 64 len' ->
  In (BM, 32) (rt_live RT Σ) -> BM mod 16 = 0 -> rw_cells asegs m BM (bufmem_cells len D max (Z_to_bv 64 0)) -> data_opt (rt_live RT Σ) BM D max ->
  0 <= len <= max -> max < len' -> gr_n len' <= 0x8000000 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x100 + 144 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_BUF_MEM_grow_clean (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) GR_SITES GR_CALLS ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost (gr_n len') <= rt_credit RT Σ -> cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_BUF_MEM_grow_clean m)))
    (fun c => exists (Σ' : rts RT) (q : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 len') m' ms
           /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) (bv_unsigned sp) (GR_W BM) m m'
           /\ cl_env m' (Z_to_bv 8 1) canary /\ rw_cells asegs m' BM (bufmem_cells len' q (gr_n len') (Z_to_bv 64 0))) c
       /\ rt_live RT Σ' = (q, gr_n len') :: live_remove D (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - mcost (gr_n len') /\ 0 < q /\ q mod 16 = 0 /\ q + gr_n len' < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem grow_re_cps : grow_re_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BM D len max len' outer lb canary
    FDO MST -> -> -> INBM BMAL BMC DOPT HLEN HLT HN4 ART0 MI0 CALL HSTK CTX UWC CGH Hlen Hcr CLE.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 80 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -80). set (n := gr_n len') in *. pose proof (gr_n_gt len' ltac:(clear - HLEN HLT; lia)) as HNGT. fold n in HNGT.
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (HLO1 : lo <= usp - 80) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (af_live_range RT AF Σ m BM 32 ART0 INBM) as (BM0 & BMLO' & _). assert (BMLO : BM + 32 <= lo) by (clear - BMLO' LOW; lia). clear BMLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BM 32 ART0 INBM ltac:(lia)) as BMHI. pose proof (proj2 (af_acc_live RT AF Σ m BM 32 ART0 INBM)) as ACCBM.
  assert (DRNG : 0 <= D /\ D + max < 2 ^ 63 /\ D <> BM /\ (D + max <= BM \/ BM + 32 <= D)).
  { destruct DOPT as [(-> & ->) | (IND & HM1 & NDBM)]; [clear - BM0; lia|].
    pose proof (af_live_range RT AF Σ m D max ART0 IND) as (D0 & DLO' & _).
    pose proof (live_ne_apart RT AF Σ m D max BM 32 ART0 IND INBM ltac:(intros E; injection E; intros _; exact NDBM)). clear - D0 DLO' LOW HLO1 SPH H NDBM. lia. }
  destruct DRNG as (D0 & DMAX & NDBM & APDBM).
  assert (COP : lo + RT_STACK <= usp1 /\ usp1 + 16 <= USTACK_TOP /\ usp1 mod 16 = 0).
  { fold usp in SPA. unfold usp1. split; [unfold RT_STACK in *; clear - HSTK; lia|]. split; [unfold USTACK_TOP in *; clear - NUM; lia|].
    apply Z.mod_divide; [lia|]. apply Z.mod_divide in SPA; [|lia]. destruct SPA as (q & Hq). exists (q - 5). lia. }
  (* [comment removed for export] *)
  pose proof (gr_g0_walk ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BM D len max len' 0 (Z_to_bv 64 0)
                HLO1 HLOS SPH ST UT SHC BMC (flags_byte m BM len D max 0 (or_introl eq_refl) BMC) ACCBM BM0 BMAL BMHI BMLO D0 DMAX HLEN HLT
                ltac:(clear - HN4 HNGT; lia) (or_introl eq_refl) MI0) as W0.
  fold usp in W0. fold usp1 in W0. fold n in W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (a2x & j & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1. cbn [Z.eqb] in Hc1'.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 80 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  assert (P1 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> m1 x = m x).
  { intros x Hx. apply MU1. cbn [outside]. split; [| exact I]. destruct (cl_split RT AF Σ m usp 80 _ ART0 ltac:(lia) ltac:(lia) Hx); lia. }
  assert (AG01 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros x Hx; cbv beta in Hx; apply P1; apply acl_stack; exact Hx).
  assert (FRR1 : rw_cells asegs m1 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp1 + Z.of_nat (cells_size [CB 8 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; unfold usp1; lia).
    exact (rw_cells_skip m1 usp1 [CB 8 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR1). }
  destruct (cl_chain_call (rt_cg RT Σ) e_BUF_MEM_grow_clean e_CRYPTO_clear_realloc SITE_gr_ccr m m1 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH _ ltac:(left; reflexivity)) (proj2 CGH _ ltac:(left; reflexivity)) UWC AG01 FRR1 ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTX1 & UWC1).
  assert (CO1 : call_ok RT Σ m1 (Z_to_bv 64 usp1) lo) by (unfold call_ok; rewrite EU1; exact (conj ST1 (conj LOW COP))).
  pose proof (cl_env_seg _ m m1 lb canary CLE MU1 ltac:(cl_fp_lia)) as CLE1.
  (* [comment removed for export] *)
  apply (ccr_opt Σ PMc (Z_to_bv 64 SITE_gr_ccr) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 len') (Z_to_bv 64 D) (Z_to_bv 64 max) (Z_to_bv 64 n)
           (Z_to_bv 64 BUF_FILE_LIT) (Z_to_bv 64 132) a5 a6 a7 (Z_to_bv 64 BM) (Z_to_bv 64 (BM + 16)) (Z_to_bv 64 n) (Z_to_bv 64 (BM ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000)
           (Z_to_bv 64 ((BM + 16) ≫ 3 + 2147450880)) s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 D max max n lo (bv_unsigned ra :: outer) lb canary
           FDO MST eq_refl eq_refl eq_refl eq_refl).
  { destruct DOPT as [(-> & ->) | (IND & HM1 & _)]; [left; split; reflexivity | right; split; [exact IND | clear - HM1; lia]]. }
  { clear - HLEN HLT HNGT; lia. } { clear - HLEN HLT HNGT HN4; lia. } { clear - HLEN HLT HNGT HN4; lia. }
  { exact ART1. } { exact MI1. } { exact CO1. }
  { rewrite EU1. unfold usp1, RT_STACK in *. clear - HSTK. lia. }
  { rewrite (unsigned_lit SITE_gr_ccr) by (unfold SITE_gr_ccr; lia). exact CTX1. }
  { rewrite (unsigned_lit SITE_gr_ccr) by (unfold SITE_gr_ccr; lia). apply (proj2 CGH). right; left; reflexivity. }
  { exact UWC1. }
  { split; intros x Hx; [apply (proj1 CGH) | apply (proj2 CGH)]; cbn [GR_SITES GR_CALLS CCR_SITES CCR_CALLS In] in Hx |- *; clear - Hx; tauto. }
  { exact Hlen. } { exact Hcr. } { exact CLE1. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & q & Hc2 & LV1 & FRS1 & SP1 & CR1 & Q0 & Q16 & QU & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & ST2) & PRES2 & CLE2 & WRQ & ACCQ) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_gr_ccr) in Hc2' by (unfold SITE_gr_ccr; lia).
  assert (INBM1 : In (BM, 32) (rt_live RT Σ1)).
  { rewrite LV1. right. apply live_remove_keep; [exact INBM | cbn [fst]; clear - NDBM; lia]. }
  assert (P2 : forall x : word, aclient (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) usp (bv_unsigned x) -> bv_unsigned x <> G_ALLOW_CUST -> m2 x = m x).
  { intros x Hx HnL. rewrite (PRES2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; lia]) ltac:(cbn [outside]; split; [clear - HnL; lia | exact I])).
    apply P1. apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e He; exact (live_remove_sub _ _ _ He) | auto | lia]. }
  assert (FR2 : rw_cells asegs m2 usp1 (CB 8 j :: gr_frame s7 s6 s5 s4 s3 s2 s1 s0 ra)).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ FR1). intros x Hx. cbv beta in Hx. unfold gr_frame in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply PRES2; [left; unfold usp1, USTACK_TOP in *; clear - Hx NUM; lia | unfold G_ALLOW_CUST; cbn [outside]; unfold usp1, RT_STACK in *; clear - Hx NUM HSTK; lia]. }
  assert (BMC2 : rw_cells asegs m2 BM (bufmem_cells len D max (Z_to_bv 64 0))).
  { apply (rw_cells_agree_nw asegs m m2 _ _ BMC). intros x Hx. cbv beta in Hx. unfold bufmem_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply P2; [apply (acl_live _ _ _ BM 32); [apply live_remove_keep; [exact INBM | cbn [fst]; clear - NDBM; lia] | clear - Hx; lia] | unfold G_ALLOW_CUST; clear - Hx BMHI; lia]. }
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & SHC2 & _ & _ & UT2). pose proof (proj2 (af_acc_live RT AF Σ1 m2 BM 32 ART2 INBM1)) as ACCBM2.
  (* [comment removed for export] *)
  pose proof (gr_g2_walk ra sp gp u0 u1 u2 s0 s1 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 lo BM D q n len max len' (Z_to_bv 64 0) j
                HLO1 HLOS SPH ST2 UT2 SHC2 FR2 BMC2 ACCBM2 BM0 BMAL BMHI BMLO Q0 ltac:(unfold USTACK_TOP in QU; clear - QU; lia) ltac:(clear - HNGT HLEN HLT; lia)
                ltac:(clear - HLEN HLT; lia) ltac:(clear - HNGT HN4; lia) ltac:(clear - D0 DMAX HLEN; lia) ltac:(clear - D0 DMAX HLEN; lia) MI2) as W2.
  fold usp usp1 in W2.
  cl_lift W2 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (m3 & -> & MU3 & WM3 & MI3 & FR3 & ST3 & BMC3) & Hc3'). clear Hc3.
  fold usp in FR3, ST3, Hc3'. fold usp1 in FR3, ST3, Hc3'.
  assert (ART3 : ART RT Σ1 m3).
  { apply (af_frame RT AF Σ1 m2 m3 usp1 ART2 ltac:(rewrite SP1; unfold usp1; lia)); [| exact WM3].
    intros x Hx. apply MU3. cbn [outside]. split; [| exact I]. intros Hin; apply Hx. apply (acl_live _ _ _ BM 32); [exact INBM1 | clear - Hin; lia]. }
  assert (CO3 : call_ok RT Σ1 m3 (Z_to_bv 64 usp1) lo) by (unfold call_ok; rewrite EU1, SP1; exact (conj ST3 (conj LOW COP))).
  assert (INQ : In (q, n) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
  (* [comment removed for export] *)
  apply (MSI Σ1 PMc (Z_to_bv 64 SITE_gr_tail) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 sp (Z_to_bv 64 len') (Z_to_bv 64 (q + len)) (Z_to_bv 64 0) (Z_to_bv 64 (len' - len))
           b3 b4 b5 b6 b7 (Z_to_bv 64 BM) (Z_to_bv 64 (BM + 16)) (Z_to_bv 64 n) (Z_to_bv 64 (BM ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BM + 16) ≫ 3 + 2147450880))
           s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m3 (q + len) (len' - len) (Z_to_bv 8 0) lo FDO MST eq_refl eq_refl eq_refl
           ltac:(unfold USTACK_TOP in QU; clear - Q0 QU HLEN HLT HNGT; lia) ltac:(clear - HLEN HLT HNGT HN4; lia)).
  { exact (live_checked_dst RT AF Σ1 m3 _ q n (q + len) (len' - len) ART3 INQ ltac:(clear - HLEN; lia) ltac:(clear - HNGT; lia) ltac:(clear - HLEN HLT; lia)). }
  { exact ART3. } { exact MI3. } { exact CO3. }
  { exact Hc3'. }
  clear Hc3'. intros c4 Hc4.
  destruct (ASTA_unpack RT Σ1 _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & ZB4) & Hc4'). clear Hc4.
  destruct RS4 as (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & F4 & fc4 & ->).
  rewrite EU1 in ST4, PRES4. rewrite (ret_pc_even SITE_gr_tail) in Hc4' by (unfold SITE_gr_tail; lia).
  assert (NQ : forall x, aclient (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) usp x -> ~ (q <= x < q + n)).
  { intros x Hx. rewrite <- FRS1 in Hx. exact (fresh_apart RT AF Σ1 m2 q n _ usp x ART2 LV1 ltac:(rewrite SP1; lia) ltac:(clear - HNGT HLEN HLT; lia) Hx). }
  assert (P4 : forall x : word, aclient (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) usp (bv_unsigned x) -> bv_unsigned x <> G_ALLOW_CUST ->
                 ~ (BM + 8 <= bv_unsigned x < BM + 24) -> m4 x = m x).
  { intros x Hx HnL HnB. rewrite (PRES4 x ltac:(rewrite LV1, FRS1; apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e He; right; exact He | auto | unfold usp1; lia]) ltac:(pose proof (NQ _ Hx); clear - H HLEN HLT HNGT; lia)).
    rewrite (MU3 x ltac:(cbn [outside]; clear - HnB; lia)). exact (P2 x Hx HnL). }
  assert (FR4 : rw_cells asegs m4 usp1 (CB 8 j :: gr_frame s7 s6 s5 s4 s3 s2 s1 s0 ra)).
  { apply (rw_cells_agree asegs m3 m4 _ _ FR3); [| exact WM4]. intros x Hx. cbv beta in Hx. unfold gr_frame in Hx. cbn [cells_size csize Nat.add] in Hx.
    pose proof (af_live_range RT AF Σ1 m2 q n ART2 INQ) as (_ & QLO & _). rewrite SP1 in QLO.
    apply PRES4; [left; unfold usp1, USTACK_TOP in *; clear - Hx NUM; lia | unfold usp1 in Hx; clear - Hx QLO NUM HLEN HLT HNGT; lia]. }
  assert (BMC4 : rw_cells asegs m4 BM (bufmem_cells len q n (Z_to_bv 64 0))).
  { apply (rw_cells_agree asegs m3 m4 _ _ BMC3); [| exact WM4]. intros x Hx. cbv beta in Hx. unfold bufmem_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
    pose proof (af_live_disj RT AF Σ1 m2 q n BM 32 [] (live_remove D (rt_live RT Σ)) ART2 LV1 ltac:(apply live_remove_keep; [exact INBM | cbn [fst]; clear - NDBM; lia])) as DQB.
    apply PRES4; [apply (acl_live _ _ _ BM 32); [exact INBM1 | clear - Hx; lia] | clear - Hx DQB HLEN HLT HNGT; lia]. }
  destruct (af_client_consts RT AF Σ1 m4 ART4) as (_ & _ & _ & _ & UT4).
  (* [comment removed for export] *)
  pose proof (gr_tail_walk ra sp gp y0 y1 y2 s0 s1 (Z_to_bv 64 (q + len)) h1 h2 h3 h4 h5 h6 h7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6
                (Z_to_bv 64 (BM + 16)) (Z_to_bv 64 n) (Z_to_bv 64 (BM ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BM + 16) ≫ 3 + 2147450880))
                F4 fc4 m4 lo BM q len n len' (Z_to_bv 64 0) j HLO1 HLOS SPH ST4 UT4 FR4 BMC4 (proj2 (af_acc_live RT AF Σ1 m4 BM 32 ART4 INBM1)) BM0 BMAL BMHI BMLO ltac:(clear - HLEN HLT HNGT HN4; lia) MI4) as W4.
  fold usp usp1 in W4.
  cl_lift W4 Hc4' c5 Hc5.
  apply Hk. exists Σ1, q.
  split; [| exact (conj LV1 (conj FRS1 (conj SP1 (conj CR1 (conj Q0 (conj Q16 (conj QU CG1)))))))].
  eapply ASTA_conseq; [exact Hc5|]. intros ms (z0 & z1 & z2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & z3 & z4 & z5 & z6 & m5 & -> & MU5 & WM5 & MI5 & ST5 & BMC5).
  fold usp in ST5. exists m5. split; [do 16 eexists; reflexivity|].
  assert (ART5 : ART RT Σ1 m5).
  { apply (af_frame RT AF Σ1 m4 m5 usp1 ART4 ltac:(rewrite SP1; unfold usp1; lia)); [| exact WM5].
    intros x Hx. apply MU5. cbn [outside]. split; [| exact I]. intros Hin; apply Hx. apply (acl_live _ _ _ BM 32); [exact INBM1 | clear - Hin; lia]. }
  split; [exact (conj ART5 (conj MI5 ST5))|].
  split.
  { intros x Hx Ho. unfold GR_W, G_ALLOW_CUST in Ho. cbn [outside] in Ho. rewrite (MU5 x ltac:(cbn [outside]; clear - Ho; lia)). apply P4; [exact Hx | unfold G_ALLOW_CUST; clear - Ho; lia | clear - Ho; lia]. }
  split; [| exact BMC5].
  assert (CLE3 : cl_env m3 (Z_to_bv 8 1) canary) by (apply (cl_env_seg _ m2 m3 _ canary CLE2 MU3); cl_fp_lia).
  assert (CLE4 : cl_env m4 (Z_to_bv 8 1) canary).
  { apply (cl_env_pres_ex _ _ _ _ _ m3 m4 _ canary CLE3 PRES4). intros x Hx.
    pose proof (NQ x ltac:(right; left; exact (cl_cell_static _ Hx))). clear - H HLEN HLT HNGT. lia. }
  apply (cl_env_seg _ m4 m5 _ canary CLE4 MU5). cl_fp_lia.
Qed.
End CGr.
