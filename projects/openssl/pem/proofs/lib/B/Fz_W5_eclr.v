(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.pem.lib.B Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_M_malloc Fz_env Fz_M_free Fz_T_sa Fz_W5_glx Fz_W5_icb Fz_W5_gsi Fz_ukit.
From OSSVerify.Proofs.openssl.pem.lib.B Require Import Fz_W5_rep Fz_W5_vset Fz_W5_new Fz_I3_eclw.
From OSSVerify.Proofs.openssl.pem.lib.B Require Export Fz_W5_agr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

(* [comment removed for export] *)
Definition ecr_frame (rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c : word) (j : list byte) : list cell :=
  [CB 8 j; C8 s9c; C8 s8c; C8 s7c; C8 s6c; C8 s5c; C8 s4c; C8 s3c; C8 s2c; C8 s1c; C8 s0c; C8 rac].
Definition ECR_LNW : word := Z_to_bv 64 (-1).

(* [comment removed for export] *)
Definition ecr_sA_post (sp gp tp s4 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (ra0 s0' s1' s2' s3' s5' s6' s7' s8' : word)
    (E i top bot lo : Z) (fl mk buf fs ls fn : list word) (wf : word) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_ecr_free1) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp (Z_to_bv 64 E) wf (Z_to_bv 64 NEW_FILE_LIT) (Z_to_bv 64 112)
                 a3 a4 a5 a6 a7 (Z_to_bv 64 (E + 576 + i * 8)) (Z_to_bv 64 ((E + 576 + i * 8) ≫ 3 + 2147450880)) s4 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (i * 8)) (Z_to_bv 64 (i * 4))
                 (Z_to_bv 64 ((E + i * 4 + 512) ≫ 3 + 2147450880)) s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_CRYPTO_free) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (E, E + 896)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' (bv_unsigned sp + -96) (ecr_frame ra0 s0' s1' s2' s3' s4 s5' s6' s7' s8' s9 j)
    /\ stk bsegs m' lo (bv_unsigned sp + -96)
    /\ es_rep m' E top bot (upd fl (Z.to_nat i) (Z_to_bv 64 0)) (upd mk (Z.to_nat i) (Z_to_bv 64 0)) (upd buf (Z.to_nat i) (Z_to_bv 64 0)) fs (upd ls (Z.to_nat i) ECR_LNW) fn.

Lemma ecr_sA_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a2 a3 a4 a5 a6 a7 s2' s3' s4 s5' s6' s7' s8' s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (E i top bot : Z) (fl mk buf fs ls fn : list word) (wf : word),
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 96 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells bsegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  es_rep m E top bot fl mk buf fs ls fn -> 0 <= i < 16 -> nth_error fs (Z.to_nat i) = Some wf ->
  acc bsegs m E 904 -> E mod 8 = 0 -> 0x10007fff8000 <= E -> E + 904 <= lo -> mem_inv bsegs m ->
  evt bsegs (ecr_sA_post sp gp (Z_to_bv 64 0xbd66f0) s4 s9 s10 s11 F fc ra0 s0' s1' s2' s3' s5' s6' s7' s8' E i top bot lo fl mk buf fs ls fn wf m)
    (MS (mkR ra0 sp gp (Z_to_bv 64 0xbd66f0) t0 t1 t2 s0' s1' (Z_to_bv 64 E) (Z_to_bv 64 i) a2 a3 a4 a5 a6 a7 s2' s3' s4 s5' s6' s7' s8' s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_err_clear) fc None m (seg_rom bsegs)).
Proof.
  intros until wf. intros ST HLO HLOS SPH UT SHC ES HI FSI ACCE EAL EHI ELO MI. unfold e_err_clear, g_shadow_memory_dynamic_address in *.
  pose proof ES as (A1 & L1 & A2 & L2 & A3 & L3 & A4 & A5 & A6 & A7 & L7 & A8 & L8 & A9 & L9 & TB & HT & HB).
  pose proof (repeat_length (Z_to_bv 8 0) 128) as LZ128. pose proof (repeat_length (Z_to_bv 8 0) 64) as LZ64.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 96, SP); (E, E + 896)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (HWU : ut_fp [(SP - 96, SP); (E, E + 896)]) by ut_fp_lia. assert (HWS : sh_fp [(SP - 96, SP); (E, E + 896)]) by sh_fp_lia.
  th_frame 96%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  zstep. do 11 zstep. zstep. replace (SP + -96 + 96) with SP by lia.
  zstep.
  if_cases KE; zify_cond KE. { exfalso. rewrite ?unsigned_lit in KE by lia. lia. }
  zstep. zstep. zstep. ubs_if.
  zstep. zstep. if_cases KT1; zify_cond KT1. { exfalso. rewrite ?unsigned_lit in KT1 by lia. lia. }
  zstep. rewrite (Z.shiftl_mul_pow2 i 2) by lia. change (2 ^ 2) with 4. zstep. zstep.
  zstep. if_cases KO1; zify_cond KO1. { exfalso. rewrite ?unsigned_lit in KO1 by lia. lia. }
  do 3 zstep.
  do 3 zstep. zstep. th_if_lit.
  pose proof (u8arr_read bsegs m0 (E + 512) (repeat (Z_to_bv 8 0) 64) (i * 4) (Z_to_bv 8 0) (Z_to_bv 64 (E + i * 4 + 512)) A6
                ltac:(apply nth_error_repeat; lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zstep. clear RD. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0.
  zstep. zstep. rewrite (Z.shiftl_mul_pow2 i 3) by lia. change (2 ^ 3) with 8. zstep. th_if_lit.
  zstep. zstep. zstep. if_cases KO2; zify_cond KO2. { exfalso. rewrite ?unsigned_lit, ?ubs_lxor_ones in KO2 by lia. lia. }
  zstep. do 3 zstep. zstep. th_if_lit.
  zstep. zstep.
  zstore A4 (E + 256) 128%nat (i * 8) 8%nat (E + 256 + i * 8).
  zstep. if_cases KO3; zify_cond KO3. { exfalso. rewrite ?unsigned_lit, ?ubs_lxor_ones in KO3 by lia. lia. }
  zstep. do 3 zstep. zstep.
  th_if_lit.
  zstore A5 (E + 384) 128%nat (i * 8) 8%nat (E + 384 + i * 8).
  zstep. if_cases KNZ; zify_cond KNZ. { exfalso. rewrite ?unsigned_lit in KNZ by lia. lia. }
  zstep. zstep. zstep. th_if_lit.
  zstore A6 (E + 512) 64%nat (i * 4) 4%nat (E + i * 4 + 512).
  zstep. zstep. zstep. if_cases KO4; zify_cond KO4. { exfalso. rewrite ?unsigned_lit, ?ubs_lxor_ones in KO4 by lia. lia. }
  do 4 zstep. zstep. th_if_lit. zstep.
  wstore32 A2 (E + 64) mk i (E + 64 + i * 4).
  zstep. if_cases KO5; zify_cond KO5. { exfalso. rewrite ?unsigned_lit, ?ubs_lxor_ones in KO5 by lia. lia. }
  do 3 zstep. zstep. th_if_lit. zstep. zstep.
  wstore32 A1 E fl i (E + i * 4).
  zstep. if_cases KO6; zify_cond KO6. { exfalso. rewrite ?unsigned_lit, ?ubs_lxor_ones in KO6 by lia. lia. }
  do 4 zstep. zstep. th_if_lit. zstep. zstep.
  wstore64 A3 (E + 128) buf i (E + 128 + i * 8).
  zstep. if_cases KO7; zify_cond KO7. { exfalso. rewrite ?unsigned_lit, ?ubs_lxor_ones in KO7 by lia. lia. }
  do 4 zstep. zstep. th_if_lit. zstep. zstep. zstep.
  wstore32 A8 (E + 704) ls i (E + 704 + i * 4).
  zstep. if_cases KO8; zify_cond KO8. { exfalso. rewrite ?unsigned_lit in KO8 by lia. lia. }
  zstep. zstep. zstep. zstep. th_if_lit.
  pose proof (u64arr_read bsegs _ (E + 576) fs i wf (Z_to_bv 64 (E + 576 + i * 8)) A7 FSI ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zstep. clear RD. zstep. zstep. zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold ecr_sA_post, SITE_ecr_free1, e_CRYPTO_free, NEW_FILE_LIT, ecr_frame, ECR_LNW. apply evt_done. do 14 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [eassumption|]. split; [assumption|].
  unfold es_rep; repeat (split; [first [eassumption | rewrite upd_length; assumption | lia] |]); lia.
Qed.

(* [comment removed for export] *)
Definition ecr_sB_post (sp gp tp s4 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (E i top bot : Z) (fl mk buf fs ls fn : list word) (wn : word) (m : mem)
    : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_ecr_free2) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp (Z_to_bv 64 (E + 768 + i * 8)) wn (Z_to_bv 64 NEW_FILE_LIT) (Z_to_bv 64 114)
                 a3 a4 a5 a6 a7 (Z_to_bv 64 (E + 576 + i * 8)) (Z_to_bv 64 ((E + 576 + i * 8) ≫ 3 + 2147450880)) s4 (Z_to_bv 64 ((E + 768 + i * 8) ≫ 3 + 2147450880))
                 (Z_to_bv 64 (i * 8)) (Z_to_bv 64 (i * 4)) (Z_to_bv 64 ((E + i * 4 + 512) ≫ 3 + 2147450880)) s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_CRYPTO_free) fc None m' (seg_rom bsegs)
    /\ munch [(E, E + 896)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ es_rep m' E top bot fl mk buf (upd fs (Z.to_nat i) (Z_to_bv 64 0)) ls fn.

Lemma ecr_sB_walk : forall sp gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (E i top bot : Z) (fl mk buf fs ls fn : list word) (wn : word),
  lo <= bv_unsigned sp - 96 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> img_untouched m ->
  es_rep m E top bot fl mk buf fs ls fn -> 0 <= i < 16 -> nth_error fn (Z.to_nat i) = Some wn ->
  acc bsegs m E 904 -> E mod 8 = 0 -> 0x10007fff8000 <= E -> E + 904 <= lo -> mem_inv bsegs m ->
  evt bsegs (ecr_sB_post sp gp (Z_to_bv 64 0xbd66f0) s4 s9 s10 s11 F fc E i top bot fl mk buf fs ls fn wn m)
    (MS (mkR (Z_to_bv 64 SITE_ecr_free1) (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 0xbd66f0) t0 t1 t2 sp (Z_to_bv 64 E) a0 a1 a2
             a3 a4 a5 a6 a7 (Z_to_bv 64 (E + 576 + i * 8)) (Z_to_bv 64 ((E + 576 + i * 8) ≫ 3 + 2147450880)) s4 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (i * 8)) (Z_to_bv 64 (i * 4))
             (Z_to_bv 64 ((E + i * 4 + 512) ≫ 3 + 2147450880)) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_ecr_free1) fc None m (seg_rom bsegs)).
Proof.
  intros until wn. intros HLO HLOS SPH UT ES HI FNI ACCE EAL EHI ELO MI. unfold SITE_ecr_free1 in *.
  pose proof ES as (A1 & L1 & A2 & L2 & A3 & L3 & A4 & A5 & A6 & A7 & L7 & A8 & L8 & A9 & L9 & TB & HT & HB).
  pose proof (repeat_length (Z_to_bv 8 0) 128) as LZ128. pose proof (repeat_length (Z_to_bv 8 0) 64) as LZ64.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(E, E + 896)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (HWU : ut_fp [(E, E + 896)]) by ut_fp_lia. assert (HWS : sh_fp [(E, E + 896)]) by sh_fp_lia.
  zstep. if_cases KNZ; zify_cond KNZ. { exfalso. rewrite ?unsigned_lit in KNZ by lia. lia. }
  zstep. zstep. th_if_lit. zstep. zstep.
  wstore64 A7 (E + 576) fs i (E + 576 + i * 8).
  zstep. if_cases KO9; zify_cond KO9. { exfalso. rewrite ?unsigned_lit in KO9 by lia. lia. }
  zstep. zstep. zstep. zstep. th_if_lit.
  pose proof (u64arr_read bsegs _ (E + 768) fn i wn (Z_to_bv 64 (E + 768 + i * 8)) A9 FNI ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zstep. clear RD. zstep. zstep. zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold ecr_sB_post, SITE_ecr_free2, e_CRYPTO_free, NEW_FILE_LIT. apply evt_done. do 13 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|].
  unfold es_rep; repeat (split; [first [eassumption | rewrite upd_length; assumption | lia] |]); lia.
Qed.

(* [comment removed for export] *)
Definition ecr_sC_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (E i top bot lo : Z) (fl mk buf fs ls fn : list word) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10 s11 t3 t4 t5 t6)
            F (ret_pc ra0) fc None m' (seg_rom bsegs)
    /\ munch [(E, E + 896)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ es_rep m' E top bot fl mk buf fs ls (upd fn (Z.to_nat i) (Z_to_bv 64 0)).

Lemma ecr_sC_walk : forall sp gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' : word) (j : list byte) (F : bvmap 5 word) fc (m : mem) (lo : Z) (E i top bot : Z) (fl mk buf fs ls fn : list word),
  stk bsegs m lo (bv_unsigned sp + -96) -> lo <= bv_unsigned sp - 96 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> img_untouched m ->
  rw_cells bsegs m (bv_unsigned sp + -96) (ecr_frame ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' j) ->
  es_rep m E top bot fl mk buf fs ls fn -> 0 <= i < 16 ->
  acc bsegs m E 904 -> E mod 8 = 0 -> 0x10007fff8000 <= E -> E + 904 <= lo -> mem_inv bsegs m ->
  evt bsegs (ecr_sC_post ra0 sp gp (Z_to_bv 64 0xbd66f0) s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10 s11 F fc E i top bot lo fl mk buf fs ls fn m)
    (MS (mkR (Z_to_bv 64 SITE_ecr_free2) (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 0xbd66f0) t0 t1 t2 sp (Z_to_bv 64 (E + 768 + i * 8)) a0 a1 a2
             a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 ((E + 768 + i * 8) ≫ 3 + 2147450880)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_ecr_free2) fc None m (seg_rom bsegs)).
Proof.
  intros until fn. intros ST HLO HLOS SPH UT FR ES HI ACCE EAL EHI ELO MI. unfold SITE_ecr_free2, ecr_frame in *.
  pose proof ES as (A1 & L1 & A2 & L2 & A3 & L3 & A4 & A5 & A6 & A7 & L7 & A8 & L8 & A9 & L9 & TB & HT & HB).
  pose proof (repeat_length (Z_to_bv 8 0) 128) as LZ128. pose proof (repeat_length (Z_to_bv 8 0) 64) as LZ64.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(E, E + 896)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (HWU : ut_fp [(E, E + 896)]) by ut_fp_lia. assert (HWS : sh_fp [(E, E + 896)]) by sh_fp_lia.
  zstep. if_cases KNZ; zify_cond KNZ. { exfalso. rewrite ?unsigned_lit in KNZ by lia. lia. }
  zstep. zstep. th_if_lit.
  wstore64 A9 (E + 768) fn i (E + 768 + i * 8).
  do 11 zstep. zstep. release_frame FR ST SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold ecr_sC_post. apply evt_done. do 16 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  unfold es_rep; repeat (split; [first [eassumption | rewrite upd_length; assumption | lia] |]); lia.
Qed.

Definition ECR_SITES : list (Z * Z) := [(SITE_ecr_free1, e_err_clear); (SITE_ecr_free2, e_err_clear)].
Definition ECR_CALLS : list (Z * Z) := [(SITE_ecr_free1, e_CRYPTO_free); (SITE_ecr_free1, e_free); (SITE_ecr_free2, e_CRYPTO_free); (SITE_ecr_free2, e_free)].
Definition ECR_W (E : Z) : list (Z * Z) := [(E, E + 904)].

Section CEcr.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_FRN : crypto_free_null_env_stmt RT.
Hypothesis C_FRC : crypto_free_env_stmt RT.

(* [comment removed for export] *)
Lemma crypto_free_opt :
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (bad : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xbd66f0 -> slot_free_ok (rt_live RT Σ) bad a0 ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  cg_ctx (rt_cg RT Σ) e_CRYPTO_free (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> In (bv_unsigned ra, e_free) (cg_call (rt_cg RT Σ)) ->
  cl_env m lb canary ->
  cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_CRYPTO_free m)))
    (fun c => exists (Σ' : rts RT) (v : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
           /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ') (rt_frames RT Σ) (bv_unsigned sp) m m' /\ cl_env m' lb canary
           /\ (bv_unsigned a0 = 0 -> wmono bsegs m m')) c
       /\ rt_live RT Σ' = rmw a0 (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_cg RT Σ' = rt_cg RT Σ).
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary bad
    FDO MST TP SOK ART0 MI0 CALL CTX UWC TAIL ENV T c HA Hk.
  destruct SOK as [Z0 | ((n & HIN) & _)].
  - assert (E0 : a0 = Z_to_bv 64 0) by (apply bv_eq; rewrite Z_to_bv_unsigned; rewrite Z0; reflexivity).
    apply (C_FRN Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary
             FDO MST E0 TP ART0 MI0 CALL CTX UWC TAIL ENV T c HA).
    intros c' (v & Hc'). apply Hk. exists Σ, v. unfold rmw. rewrite Z0. cbn [Z.eqb].
    split; [| repeat split; reflexivity].
    apply (ASTA_conseq RT Σ PMc _ _ c' Hc'). intros ms (m' & RS & AFT & PRES & ENV'). exists m'.
    split; [exact RS|]. split; [exact (rt_after_f_of _ _ _ _ _ _ AFT)|]. split; [exact PRES|]. split; [exact ENV'|].
    intros _. destruct AFT as (_ & _ & WM' & _). exact WM'.
  - assert (E1 : a0 = Z_to_bv 64 (bv_unsigned a0)) by (symmetry; apply Z_to_bv_bv_unsigned).
    pose proof (af_live_range RT AF Σ m _ _ ART0 HIN) as (P0 & _).
    apply (C_FRC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (bv_unsigned a0) n lo outer lb canary
             FDO MST E1 TP HIN ART0 MI0 CALL CTX UWC TAIL ENV T c HA).
    intros c' (Σ' & v & Hc' & LV & FRS & SP & CR & CG). apply Hk. exists Σ', v. unfold rmw. replace (bv_unsigned a0 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    split; [| exact (conj LV (conj FRS (conj SP (conj CR CG))))].
    apply (ASTA_conseq RT Σ' PMc _ _ c' Hc'). intros ms (m' & RS & AFT & PRES & ENV'). exists m'.
    split; [exact RS|]. split; [exact AFT|]. split; [exact PRES|]. split; [exact ENV'|]. intros Z0. exfalso. lia.
Qed.

(* [comment removed for export] *)
Definition err_clear_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (bad : list Z) (E i top bot : Z) (fl mk buf fs ls fn : list word) (wf wn : word) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xbd66f0 -> a0 = Z_to_bv 64 E -> a1 = Z_to_bv 64 i ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 96 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_err_clear (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) ECR_SITES ECR_CALLS ->
  In (E, 904) (rt_live RT Σ) -> E mod 8 = 0 -> In E bad -> es_rep m E top bot fl mk buf fs ls fn -> 0 <= i < 16 ->
  nth_error fs (Z.to_nat i) = Some wf -> nth_error fn (Z.to_nat i) = Some wn ->
  slot_free_ok (rt_live RT Σ) bad wf -> slot_free_ok (rt_live RT Σ) bad wn -> (bv_unsigned wf <> 0 -> bv_unsigned wf <> bv_unsigned wn) ->
  cl_env m lb canary ->
  cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_err_clear m)))
    (fun c => exists (Σ' : rts RT) (v : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
           /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
           /\ (bv_unsigned wf = 0 -> bv_unsigned wn = 0 -> wmono bsegs m m')
           /\ rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ) (bv_unsigned sp) (ECR_W E) m m'
           /\ es_rep m' E top bot (upd fl (Z.to_nat i) (Z_to_bv 64 0)) (upd mk (Z.to_nat i) (Z_to_bv 64 0)) (upd buf (Z.to_nat i) (Z_to_bv 64 0))
                    (upd fs (Z.to_nat i) (Z_to_bv 64 0)) (upd ls (Z.to_nat i) ECR_LNW) (upd fn (Z.to_nat i) (Z_to_bv 64 0))
           /\ cl_env m' lb canary) c
       /\ rt_live RT Σ' = rmw wn (rmw wf (rt_live RT Σ)) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem err_clear_cps : err_clear_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer bad E i top bot fl mk buf fs ls fn wf wn lb canary
    FDO MST -> -> -> ART0 MI0 CALL HSTK CTX UWC CGH INE EAL INB ES HI FSI FNI SOKF SOKN DIS CLE.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *. set (usp1 := usp + -96).
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 96 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP /\ lo + RT_STACK <= usp1 /\ usp1 + 16 <= USTACK_TOP)
    by (unfold usp1, RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (SPA1 : usp1 mod 16 = 0).
  { unfold usp1. apply Z.mod_divide; [lia|]. apply Z.mod_divide in SPA; [|lia]. destruct SPA as (q & Hq). exists (q - 6). lia. }
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  pose proof (af_live_range RT AF Σ m E 904 ART0 INE) as (R4a & R4 & _).
  pose proof (afp_live_hi RT GOBJ AFP Σ m E 904 ART0 INE ltac:(lia)) as EHI.
  assert (ELO : E + 904 <= lo) by (clear - R4 LOW; lia).
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (proj2 (af_acc_live RT AF Σ m E 904 ART0 INE)) as ACCE.
  (* [comment removed for export] *)
  assert (KEEPE : forall w L, slot_free_ok L bad w -> forall live, In (E, 904) live -> In (E, 904) (rmw w live)).
  { intros w L SOK live Hin. destruct SOK as [Z0 | (_ & NB)]; [unfold rmw; rewrite Z0; exact Hin|].
    apply rmw_keep; [exact Hin|]. cbn [fst]. intros EQ. apply NB. rewrite <- EQ. exact INB. }
  (* [comment removed for export] *)
  pose proof (ecr_sA_walk ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo E i top bot fl mk buf fs ls fn wf
                ST ltac:(fold usp; clear - NUM; unfold usp1, RT_STACK in *; lia) ltac:(clear - NUM; lia) SPH UT SHC ES HI FSI ACCE EAL EHI ELO MI0) as W1.
  cl_lift W1 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (u0 & u1 & u2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & jf & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1 & ES1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  assert (A01 : forall x : word, ~ (E <= bv_unsigned x < E + 904) -> ~ (usp - 96 <= bv_unsigned x < usp) -> m1 x = m x).
  { intros x Hx1 Hx2. apply MU1. cbn [outside]. clear - Hx1 Hx2. lia. }
  assert (ART1 : ART RT Σ m1).
  { apply (af_frame RT AF Σ m m1 usp1 ART0 ltac:(clear - NUM; unfold usp1; lia)); [| exact WM1].
    intros x Hx. apply A01.
    - intros Hin; apply Hx. apply (acl_live _ _ _ E 904); [exact INE | clear - Hin; lia].
    - intros Hin; apply Hx. left. clear - Hin NUM. unfold usp1. lia. }
  assert (AG01 : agree_on (fun x => usp <= x < USTACK_TOP) m m1).
  { intros x Hx. cbv beta in Hx. apply A01; clear - Hx ELO NUM; unfold usp1, RT_STACK in *; lia. }
  assert (CLE1 : cl_env m1 lb canary) by (apply (cl_env_seg _ m m1 lb canary CLE MU1); cl_fp_lia).
  assert (FRR1 : rw_cells bsegs m1 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp1 + Z.of_nat (cells_size [CB 8 jf; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; unfold usp1; lia).
    exact (rw_cells_skip m1 usp1 [CB 8 jf; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR1). }
  destruct (cl_chain_call (rt_cg RT Σ) e_err_clear e_CRYPTO_free SITE_ecr_free1 m m1 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH _ ltac:(left; reflexivity)) (proj2 CGH _ ltac:(left; reflexivity)) UWC AG01 FRR1 ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTX1 & UWC1).
  assert (CO1 : call_ok RT Σ m1 (Z_to_bv 64 usp1) lo) by (unfold call_ok; rewrite EU1; clear - ST1 LOW NUM SPA1; tauto).
  (* [comment removed for export] *)
  apply (crypto_free_opt Σ PMc (Z_to_bv 64 SITE_ecr_free1) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xbd66f0) u0 u1 u2 sp (Z_to_bv 64 E) wf (Z_to_bv 64 NEW_FILE_LIT) (Z_to_bv 64 112)
           b3 b4 b5 b6 b7 (Z_to_bv 64 (E + 576 + i * 8)) (Z_to_bv 64 ((E + 576 + i * 8) ≫ 3 + 2147450880)) s4 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (i * 8)) (Z_to_bv 64 (i * 4))
           (Z_to_bv 64 ((E + i * 4 + 512) ≫ 3 + 2147450880)) s9 s10 s11 u3 u4 u5 u6 F fc m1 lo (bv_unsigned ra :: outer) lb canary bad
           FDO MST eq_refl SOKF ART1 MI1 CO1).
  { rewrite (unsigned_lit SITE_ecr_free1) by (unfold SITE_ecr_free1; lia). exact CTX1. }
  { exact UWC1. }
  { rewrite (unsigned_lit SITE_ecr_free1) by (unfold SITE_ecr_free1; lia). apply (proj2 CGH). right; left; reflexivity. }
  { exact CLE1. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & v1 & Hc2 & LV1 & FRS1 & SP1 & CR1 & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & ST2) & PRES2 & CLE2 & WMF1) & Hc2'). clear Hc2.
  destruct RS2 as (w0 & w1 & w2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_ecr_free1) in Hc2' by (unfold SITE_ecr_free1; lia).
  assert (INE1 : In (E, 904) (rt_live RT Σ1)) by (rewrite LV1; exact (KEEPE wf _ SOKF _ INE)).
  assert (SUB1 : forall e, In e (rt_live RT Σ1) -> In e (rt_live RT Σ)) by (rewrite LV1; intros e He; exact (rmw_sub _ _ _ He)).
  assert (A12 : forall x : word, aclient (rt_live RT Σ1) (rt_frames RT Σ) usp1 (bv_unsigned x) -> m2 x = m1 x) by (intros x Hx; exact (PRES2 x Hx)).
  assert (ES2 : es_rep m2 E top bot (upd fl (Z.to_nat i) (Z_to_bv 64 0)) (upd mk (Z.to_nat i) (Z_to_bv 64 0)) (upd buf (Z.to_nat i) (Z_to_bv 64 0)) fs (upd ls (Z.to_nat i) ECR_LNW) fn).
  { apply (es_rep_agree_nw m1 m2 _ _ _ _ _ _ _ _ _ ES1). intros x Hx. cbv beta in Hx. apply A12. apply (acl_live _ _ _ E 904); [exact INE1 | clear - Hx; lia]. }
  assert (FR2 : rw_cells bsegs m2 usp1 (ecr_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 jf)).
  { apply (rw_cells_agree_nw bsegs m1 m2 _ _ FR1). intros x Hx. cbv beta in Hx. unfold ecr_frame in Hx. cbn [cells_size csize Nat.add] in Hx. apply A12. left. unfold usp1, USTACK_TOP in *. clear - Hx NUM; lia. }
  assert (AG02 : agree_on (fun x => usp <= x < USTACK_TOP) m m2).
  { intros x Hx. cbv beta in Hx. rewrite (A12 x ltac:(left; unfold usp1; clear - Hx; lia)). exact (AG01 x Hx). }
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & SHC2 & _ & _ & UT2).
  pose proof (proj2 (af_acc_live RT AF Σ1 m2 E 904 ART2 INE1)) as ACCE2.
  (* [comment removed for export] *)
  pose proof (ecr_sB_walk sp gp w0 w1 w2 v1 g1 g2 g3 g4 g5 g6 g7 s4 s9 s10 s11 w3 w4 w5 w6 F2 fc2 m2 lo E i top bot
                (upd fl (Z.to_nat i) (Z_to_bv 64 0)) (upd mk (Z.to_nat i) (Z_to_bv 64 0)) (upd buf (Z.to_nat i) (Z_to_bv 64 0)) fs (upd ls (Z.to_nat i) ECR_LNW) fn wn
                ltac:(fold usp; clear - NUM; unfold usp1, RT_STACK in *; lia) ltac:(clear - NUM; lia) SPH UT2 ES2 HI FNI ACCE2 EAL EHI ELO MI2) as W2.
  fold usp usp1 in W2.
  cl_lift W2 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (x0 & x1 & x2 & h3 & h4 & h5 & h6 & h7 & x3 & x4 & x5 & x6 & m3 & -> & MU3 & WM3 & MI3 & ES3) & Hc3'). clear Hc3.
  fold usp in Hc3'. fold usp1 in Hc3'.
  assert (ART3 : ART RT Σ1 m3).
  { apply (af_frame RT AF Σ1 m2 m3 usp1 ART2 ltac:(rewrite SP1; clear - NUM; unfold usp1; lia)); [| exact WM3].
    intros x Hx. apply MU3. cbn [outside]. split; [| exact I]. intros Hin; apply Hx. apply (acl_live _ _ _ E 904); [exact INE1 | clear - Hin; lia]. }
  assert (A23 : forall x : word, ~ (E <= bv_unsigned x < E + 904) -> m3 x = m2 x) by (intros x Hx; apply MU3; cbn [outside]; clear - Hx; lia).
  assert (ST3 : stk bsegs m3 lo usp1) by (apply (stk_agree_nw bsegs m2 m3 _ _ ST2); intros x Hx; cbv beta in Hx; apply A23; clear - Hx ELO; lia).
  assert (FR3 : rw_cells bsegs m3 usp1 (ecr_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 jf)).
  { apply (rw_cells_agree_nw bsegs m2 m3 _ _ FR2). intros x Hx. cbv beta in Hx. unfold ecr_frame in Hx. cbn [cells_size csize Nat.add] in Hx. apply A23. unfold usp1, RT_STACK in *; clear - Hx ELO NUM; lia. }
  assert (AG03 : agree_on (fun x => usp <= x < USTACK_TOP) m m3).
  { intros x Hx. cbv beta in Hx. rewrite (A23 x ltac:(unfold usp1, RT_STACK in *; clear - Hx ELO NUM; lia)). exact (AG02 x Hx). }
  assert (CLE3 : cl_env m3 lb canary) by (apply (cl_env_seg _ m2 m3 lb canary CLE2 MU3); cl_fp_lia).
  assert (FRR3 : rw_cells bsegs m3 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp1 + Z.of_nat (cells_size [CB 8 jf; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; unfold usp1; lia).
    exact (rw_cells_skip m3 usp1 [CB 8 jf; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR3). }
  destruct (cl_chain_call (rt_cg RT Σ) e_err_clear e_CRYPTO_free SITE_ecr_free2 m m3 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH _ ltac:(right; left; reflexivity)) (proj2 CGH _ ltac:(right; right; left; reflexivity)) UWC AG03 FRR3 ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT)
    as (CTX3 & UWC3).
  rewrite <- CG1 in CTX3.
  assert (CO3 : call_ok RT Σ1 m3 (Z_to_bv 64 usp1) lo) by (unfold call_ok; rewrite EU1, SP1; clear - ST3 LOW NUM SPA1; tauto).
  assert (SOKN1 : slot_free_ok (rt_live RT Σ1) bad wn).
  { destruct SOKN as [Z0 | ((n & HIN) & NB)]; [left; exact Z0 | right]. split; [| exact NB]. exists n. rewrite LV1.
    destruct SOKF as [ZF | _]; [unfold rmw; rewrite ZF; exact HIN|]. apply rmw_keep; [exact HIN|]. cbn [fst]. intros EQ.
    destruct (Z.eq_dec (bv_unsigned wf) 0) as [ZF|NZ]; [| exact (DIS NZ (eq_sym EQ))].
    pose proof (af_live_range RT AF Σ m _ _ ART0 HIN) as (P0 & _). lia. }
  (* [comment removed for export] *)
  apply (crypto_free_opt Σ1 PMc (Z_to_bv 64 SITE_ecr_free2) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xbd66f0) x0 x1 x2 sp (Z_to_bv 64 (E + 768 + i * 8)) wn (Z_to_bv 64 NEW_FILE_LIT) (Z_to_bv 64 114)
           h3 h4 h5 h6 h7 (Z_to_bv 64 (E + 576 + i * 8)) (Z_to_bv 64 ((E + 576 + i * 8) ≫ 3 + 2147450880)) s4 (Z_to_bv 64 ((E + 768 + i * 8) ≫ 3 + 2147450880))
           (Z_to_bv 64 (i * 8)) (Z_to_bv 64 (i * 4)) (Z_to_bv 64 ((E + i * 4 + 512) ≫ 3 + 2147450880)) s9 s10 s11 x3 x4 x5 x6 F2 fc2 m3 lo (bv_unsigned ra :: outer) lb canary bad
           FDO MST eq_refl SOKN1 ART3 MI3 CO3).
  { rewrite (unsigned_lit SITE_ecr_free2) by (unfold SITE_ecr_free2; lia). exact CTX3. }
  { exact UWC3. }
  { rewrite (unsigned_lit SITE_ecr_free2) by (unfold SITE_ecr_free2; lia). rewrite CG1. apply (proj2 CGH). right; right; right; left; reflexivity. }
  { exact CLE3. }
  { exact Hc3'. }
  clear Hc3'. intros c4 (Σ2 & v2 & Hc4 & LV2 & FRS2 & SP2 & CR2 & CG2).
  destruct (ASTA_unpack RT Σ2 _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & ST4) & PRES4 & CLE4 & WMF2) & Hc4'). clear Hc4.
  destruct RS4 as (y0 & y1 & y2 & k1 & k2 & k3 & k4 & k5 & k6 & k7 & y3 & y4 & y5 & y6 & F4 & fc4 & ->).
  rewrite EU1 in ST4, PRES4. rewrite (ret_pc_even SITE_ecr_free2) in Hc4' by (unfold SITE_ecr_free2; lia).
  assert (INE2 : In (E, 904) (rt_live RT Σ2)) by (rewrite LV2; exact (KEEPE wn _ SOKN1 _ INE1)).
  assert (SUB2 : forall e, In e (rt_live RT Σ2) -> In e (rt_live RT Σ1)) by (rewrite LV2; intros e He; exact (rmw_sub _ _ _ He)).
  assert (A34 : forall x : word, aclient (rt_live RT Σ2) (rt_frames RT Σ) usp1 (bv_unsigned x) -> m4 x = m3 x) by (intros x Hx; rewrite <- FRS1 in Hx; exact (PRES4 x Hx)).
  assert (ES4 : es_rep m4 E top bot (upd fl (Z.to_nat i) (Z_to_bv 64 0)) (upd mk (Z.to_nat i) (Z_to_bv 64 0)) (upd buf (Z.to_nat i) (Z_to_bv 64 0))
                  (upd fs (Z.to_nat i) (Z_to_bv 64 0)) (upd ls (Z.to_nat i) ECR_LNW) fn).
  { apply (es_rep_agree_nw m3 m4 _ _ _ _ _ _ _ _ _ ES3). intros x Hx. cbv beta in Hx. apply A34. apply (acl_live _ _ _ E 904); [exact INE2 | clear - Hx; lia]. }
  assert (FR4 : rw_cells bsegs m4 usp1 (ecr_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 jf)).
  { apply (rw_cells_agree_nw bsegs m3 m4 _ _ FR3). intros x Hx. cbv beta in Hx. unfold ecr_frame in Hx. cbn [cells_size csize Nat.add] in Hx. apply A34. left. unfold usp1, USTACK_TOP in *. clear - Hx NUM; lia. }
  destruct (af_client_consts RT AF Σ2 m4 ART4) as (_ & SHC4 & _ & _ & UT4).
  pose proof (proj2 (af_acc_live RT AF Σ2 m4 E 904 ART4 INE2)) as ACCE4.
  (* [comment removed for export] *)
  pose proof (ecr_sC_walk sp gp y0 y1 y2 v2 k1 k2 k3 k4 k5 k6 k7 (Z_to_bv 64 (E + 576 + i * 8)) (Z_to_bv 64 ((E + 576 + i * 8) ≫ 3 + 2147450880)) s4
                (Z_to_bv 64 (i * 8)) (Z_to_bv 64 (i * 4)) (Z_to_bv 64 ((E + i * 4 + 512) ≫ 3 + 2147450880)) s9 s10 s11 y3 y4 y5 y6
                ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 jf F4 fc4 m4 lo E i top bot
                (upd fl (Z.to_nat i) (Z_to_bv 64 0)) (upd mk (Z.to_nat i) (Z_to_bv 64 0)) (upd buf (Z.to_nat i) (Z_to_bv 64 0)) (upd fs (Z.to_nat i) (Z_to_bv 64 0)) (upd ls (Z.to_nat i) ECR_LNW) fn
                ST4 ltac:(fold usp; clear - NUM; unfold usp1, RT_STACK in *; lia) ltac:(clear - NUM; lia) SPH UT4 FR4 ES4 HI ACCE4 EAL EHI ELO MI4) as W3.
  fold usp usp1 in W3.
  cl_lift W3 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ2 _ _ c5 Hc5) as (ms5 & (z0 & z1 & z2 & q0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & z3 & z4 & z5 & z6 & m5 & -> & MU5 & WM5 & MI5 & ST5 & ES5) & Hc5'). clear Hc5.
  fold usp in ST5.
  assert (ART5 : ART RT Σ2 m5).
  { apply (af_frame RT AF Σ2 m4 m5 usp1 ART4 ltac:(rewrite SP2, SP1; clear - NUM; unfold usp1; lia)); [| exact WM5].
    intros x Hx. apply MU5. cbn [outside]. split; [| exact I]. intros Hin; apply Hx. apply (acl_live _ _ _ E 904); [exact INE2 | clear - Hin; lia]. }
  assert (A45 : forall x : word, ~ (E <= bv_unsigned x < E + 904) -> m5 x = m4 x) by (intros x Hx; apply MU5; cbn [outside]; clear - Hx; lia).
  assert (A05 : forall x : word, aclient (rt_live RT Σ2) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (E <= bv_unsigned x < E + 904) -> m5 x = m x).
  { intros x Hx HnE. rewrite (A45 x HnE).
    rewrite (A34 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; clear; lia])). rewrite (A23 x HnE).
    rewrite (A12 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [exact SUB2 | auto | unfold usp1; clear; lia])). apply (A01 x HnE).
    assert (HS : rt_sp0 RT Σ2 - STACK_WIN <= usp - 96) by (rewrite SP2, SP1; clear - NUM; lia).
    assert (Hx' : aclient (rt_live RT Σ2) (rt_frames RT Σ2) usp (bv_unsigned x)) by (rewrite FRS2, FRS1; exact Hx).
    destruct (cl_split RT AF Σ2 m5 usp 96 _ ART5 HS ltac:(lia) Hx') as [Q|Q]; clear - Q; lia. }
  assert (LV2' : rt_live RT Σ2 = rmw wn (rmw wf (rt_live RT Σ))) by (rewrite LV2, LV1; reflexivity).
  apply Hk. exists Σ2, q0.
  split; [| exact (conj LV2' (conj (eq_trans FRS2 FRS1) (conj (eq_trans SP2 SP1) (conj (eq_trans CR2 CR1) (eq_trans CG2 CG1)))))].
  eapply ASTA_conseq; [exact Hc5'|]. intros ms <-. exists m5.
  split; [exists z0, z1, z2, q1, q2, q3, q4, q5, q6, q7, z3, z4, z5, z6, F4, fc4; reflexivity|].
  split; [exact (conj ART5 (conj MI5 ST5))|].
  split. { intros ZF ZN. exact (wmono_trans bsegs _ _ _ WM1 (wmono_trans bsegs _ _ _ (WMF1 ZF) (wmono_trans bsegs _ _ _ WM3 (wmono_trans bsegs _ _ _ (WMF2 ZN) WM5)))). }
  split. { intros x Hx Ho. unfold ECR_W in Ho. cbn [outside] in Ho. exact (A05 x Hx ltac:(clear - Ho; lia)). }
  split; [exact ES5|].
  apply (cl_env_seg _ m4 m5 lb canary CLE4 MU5); cl_fp_lia.
Qed.
End CEcr.
