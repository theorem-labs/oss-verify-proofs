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
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout PLayout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_G_kit Fz_ckit Fz_env Fz_M_malloc Th_tsd Th_key Th_once Fz_T_once Fz_T_local Fz_T_master1 Fz_I3_dctki Fz_G_default_context_do_init_ossl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Definition e_gdc : Z := 0x1f76c0.
Definition SITE_gdc_once1 : Z := 0x1f76e4.
Definition SITE_gdc_once2 : Z := 0x1f7708.
Definition SITE_gdc_getl : Z := 0x1f7724.

(* [comment removed for export] *)
Definition gdc_w0_post (sp gp tp t1 t2 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rae s0e : word) (F : bvmap 5 word) (fc : bv 32)
    (lo j : Z) (sh oldcb canary : word) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0' a0' a1' a2' a3' a4' a5' a6' a7' : word) (junk : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 ONCE_RET_INIT) (Z_to_bv 64 (bv_unsigned sp + -16 + -128)) gp tp t0' t1 t2 (Z_to_bv 64 0xb9f780) (Z_to_bv 64 e_dcdi)
                 a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 0) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 2) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_dcdi) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 304, bv_unsigned sp); (0xb9f740, 0xb9f740 + 4); (0xb9f780, 0xb9f780 + 4); (0xb9f720, 0xb9f720 + 4); (0xb9f760, 0xb9f760 + 4);
              (NEXT_KEY, NEXT_KEY + 12); (KEYS + 8 * j, KEYS + 8 * j + 8); (TP_A + -96, TP_A + -88)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -16) [C8 s0e; C8 rae]
    /\ rw_cells asegs m' (bv_unsigned sp + -16 + -16) [C8 sp; C8 (Z_to_bv 64 SITE_gdc_once2)]
    /\ rw_cells asegs m' (bv_unsigned sp + -16 + -32) [CB 8 junk; C8 (Z_to_bv 64 RUN_ONCE_RET)]
    /\ rw_cells asegs m' (bv_unsigned sp + -16 + -128) (once_full_cells 0xb9f780 oldcb canary s6 s5 s4 s3 s2 s1 (Z_to_bv 64 (bv_unsigned sp + -16)))
    /\ rw_cells asegs m' (TP_A + -96) [C8 (Z_to_bv 64 (bv_unsigned sp + -16 + -128))]
    /\ rw_cells asegs m' 0xb9f780 [C4 (Z_to_bv 64 1)] /\ rw_cells asegs m' 0xb9f740 [C4 (Z_to_bv 64 2)]
    /\ rw_cells asegs m' 0xb9f720 [C4 (Z_to_bv 64 j)] /\ rw_cells asegs m' 0xb9f760 [C4 (Z_to_bv 64 1)]
    /\ rw_cells asegs m' NEXT_KEY [C4 (Z_to_bv 64 j)] /\ rw_cells asegs m' KEY_LOCK [C4 z64; C4 z64; C4 sh] /\ rw_cells asegs m' (KEYS + 8 * j) [C8 (Z_to_bv 64 NODTOR)]
    /\ ssp_cells m' canary /\ stk asegs m' lo (bv_unsigned sp + -16 + -128).

Lemma gdc_w0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (lo nk j : Z) (sh kold w r oldcb canary : word),
  tp = Z_to_bv 64 TP_A ->
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 304 -> bv_unsigned sp <= 2^47 ->
  img_untouched m ->
  rw_cells asegs m 0xb9f740 [C4 z64] -> rw_cells asegs m 0xb9f780 [C4 z64] ->
  rw_cells asegs m 0xb9f720 [C4 kold] -> rw_cells asegs m 0xb9f760 [C4 r] ->
  ro_cells asegs m (TP_A + -88) [C8 (Z_to_bv 64 TSD_MAIN)] ->
  rw_cells asegs m NEXT_KEY [C4 (Z_to_bv 64 nk)] -> 0 <= nk < 128 ->
  rw_cells asegs m KEY_LOCK [C4 z64; C4 z64; C4 sh] ->
  rw_cells asegs m (KEYS + 8 * j) [C8 z64] -> ro_cells asegs m (KEYS + 8 * nk) [C8 w] ->
  ((j = nk /\ w = z64) \/ (j = (nk + 1) mod 128 /\ bv_unsigned w <> 0)) ->
  ssp_cells m canary -> rw_cells asegs m (TP_A + -96) [C8 oldcb] ->
  mem_inv asegs m ->
  evt asegs (gdc_w0_post sp gp tp t1 t2 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 F fc lo j sh oldcb canary m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_gdc) fc None m (seg_rom asegs)).
Proof.
  intros until canary. intros -> ST HLOS HLO SPH UT O1 O2 KC RC TC NK HNK KL KJ PROBE CASE SSP CBC MI.
  destruct SSP as [GOT GU]. unfold got_ssp, ssp_guard in GOT, GU. unfold e_gdc.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  assert (HJ : 0 <= j < 128) by (destruct CASE as [[-> _] | [-> _]]; [lia | apply Z.mod_pos_bound; lia]).
  pose proof (munch_refl [(SP - 304, SP); (0xb9f740, 0xb9f740 + 4); (0xb9f780, 0xb9f780 + 4); (0xb9f720, 0xb9f720 + 4); (0xb9f760, 0xb9f760 + 4);
                          (NEXT_KEY, NEXT_KEY + 12); (KEYS + 8 * j, KEYS + 8 * j + 8); (TP_A + -96, TP_A + -88)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 304, SP); (0xb9f740, 0xb9f740 + 4); (0xb9f780, 0xb9f780 + 4); (0xb9f720, 0xb9f720 + 4); (0xb9f760, 0xb9f760 + 4);
                      (NEXT_KEY, NEXT_KEY + 12); (KEYS + 8 * j, KEYS + 8 * j + 8); (TP_A + -96, TP_A + -88)]) by ut_fp_lia.
  carve_frame 16%nat ST.
  do 9 zstep.
  tcall (T_run_once_enter_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo e_dctki oldcb canary).
  all: try first [eassumption | reflexivity | split; assumption | unfold e_dctki, got_ssp, ssp_guard; lia | unfold got_ssp, ssp_guard; left; lia].
  cbv beta delta [mkR]. rewrite (ret_pc_even e_dctki) by (unfold e_dctki; lia).
  tcall (dctki_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo nk j sh kold w r).
  all: try first [eassumption | reflexivity | rewrite unsigned_lit by lia; lia | lia].
  cbv beta delta [mkR]. rewrite (ret_pc_even ONCE_RET_INIT) by (unfold ONCE_RET_INIT; lia).
  replace (SP + -16 + -128) with (SP + -16 + -128) by lia.
  tcall (T_run_once_leave_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (SP + -16) 0xb9f740 _ oldcb canary _ _ _ _ _ _ _ _ _).
  all: try first [eassumption | reflexivity | split; assumption | unfold got_ssp, ssp_guard; lia | unfold got_ssp, ssp_guard; left; lia].
  cbv beta delta [mkR]. rewrite (ret_pc_even 0x1f76e4) by lia.
  zstep. if_false. zstep. zstep. zstep. if_false.
  do 5 zstep.
  tcall (T_run_once_enter_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo e_dcdi oldcb canary).
  all: try first [eassumption | reflexivity | split; assumption | unfold e_dcdi, got_ssp, ssp_guard; lia | unfold got_ssp, ssp_guard; left; lia].
  cbv beta delta [mkR]. rewrite (ret_pc_even e_dcdi) by (unfold e_dcdi; lia).
  subst SP. rewrite ?Z_to_bv_bv_unsigned. rewrite ?Z_to_bv_bv_unsigned in POST.
  unfold gdc_w0_post, SITE_gdc_once2. apply evt_done. do 11 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  repeat (split; [first [eassumption | split; eassumption] |]). eassumption.
Qed.

(* [comment removed for export] *)
Definition gdc_w1_post (sp gp tp t0 t2 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rae s0e : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (oldcb canary : word) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t1' a1' a2' a3' : word) (m' : mem),
    ms = MS (mkR rae sp gp tp t0 t1' t2 s0e s1 (Z_to_bv 64 0xb9f580) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc rae) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 304, bv_unsigned sp); (0xb9f780, 0xb9f780 + 4); (TP_A + -96, TP_A + -88)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' 0xb9f780 [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m' (TP_A + -96) [C8 oldcb]
    /\ ssp_cells m' canary /\ stk asegs m' lo (bv_unsigned sp).

Lemma gdc_w1 : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rae s0e : word)
    (F : bvmap 5 word) fc (m : mem) (lo j sb : Z) (sh oldcb canary : word) (junk : list byte),
  tp = Z_to_bv 64 TP_A -> 0 <= j < 128 -> (sb = 0 \/ sb = 4) ->
  stk asegs m lo (bv_unsigned sp + -16 + -128) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 304 -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  rw_cells asegs m (bv_unsigned sp + -16) [C8 s0e; C8 rae] ->
  rw_cells asegs m (bv_unsigned sp + -16 + -16) [C8 sp; C8 (Z_to_bv 64 SITE_gdc_once2)] ->
  rw_cells asegs m (bv_unsigned sp + -16 + -32) [CB 8 junk; C8 (Z_to_bv 64 RUN_ONCE_RET)] ->
  rw_cells asegs m (bv_unsigned sp + -16 + -128) (once_full_cells 0xb9f780 oldcb canary s6 s5 s4 s3 s2 s1 (Z_to_bv 64 (bv_unsigned sp + -16))) ->
  rw_cells asegs m (TP_A + -96) [C8 (Z_to_bv 64 (bv_unsigned sp + -16 + -128))] ->
  rw_cells asegs m 0xb9f780 [C4 (Z_to_bv 64 1)] -> rw_cells asegs m 0xb9f7a0 [C4 (Z_to_bv 64 1)] ->
  ro_cells asegs m 0xb9f720 [C4 (Z_to_bv 64 j)] -> ro_cells asegs m (0xb9f720 / 8 + 2147450880) [C1 (Z_to_bv 8 sb)] ->
  ro_cells asegs m (TP_A + -88) [C8 (Z_to_bv 64 TSD_MAIN)] -> ro_cells asegs m (TSD_MAIN + 8 * j) [C8 z64] ->
  rw_cells asegs m 0xb9f560 [C1 (Z_to_bv 8 1)] ->
  ssp_cells m canary ->
  mem_inv asegs m ->
  evt asegs (gdc_w1_post sp gp tp t0 t2 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rae s0e F fc lo oldcb canary m)
    (MS (mkR (Z_to_bv 64 ONCE_RET_INIT) (Z_to_bv 64 (bv_unsigned sp + -16 + -128)) gp tp t0 t1 t2 (Z_to_bv 64 0xb9f780) (Z_to_bv 64 e_dcdi)
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 2) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ONCE_RET_INIT) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros -> HJ HSB ST HLOS HLO SPH UT SHC FR REC RR OFC CBP O2 DRET KEYC KSH TC TSD INI SSP MI.
  destruct SSP as [GOT GU]. unfold got_ssp, ssp_guard in GOT, GU. unfold g_shadow_memory_dynamic_address, SHB in SHC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl [(SP - 304, SP); (0xb9f780, 0xb9f780 + 4); (TP_A + -96, TP_A + -88)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 304, SP); (0xb9f780, 0xb9f780 + 4); (TP_A + -96, TP_A + -88)]) by ut_fp_lia.
  tcall (T_run_once_leave_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (SP + -16) 0xb9f780 _ oldcb canary _ _ _ _ _ _ _ _ _).
  all: try first [eassumption | reflexivity | split; assumption | unfold got_ssp, ssp_guard; lia | unfold got_ssp, ssp_guard; left; lia].
  cbv beta delta [mkR]. unfold SITE_gdc_once2. rewrite (ret_pc_even 0x1f7708) by lia.
  zstep. if_false. zstep. zstep. zstep. if_false.
  do 3 zstep.
  tcall (T_get_local_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo TSD_MAIN j sb z64).
  all: try first [eassumption | reflexivity | rewrite unsigned_lit by lia; first [eassumption | lia] | lia].
  all: try exact (ut_munch _ m _ UT MU HWU).
  cbv beta delta [mkR].
  zstep. if_false.
  do 5 zstep.
  zstep. do 3 zstep.
  lazymatch goal with H : stk asegs _ lo _ |- _ => release_frame FR H SP end.
  zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold gdc_w1_post. apply evt_done. do 5 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  repeat (split; [first [eassumption | split; eassumption] |]). eassumption.
Qed.
