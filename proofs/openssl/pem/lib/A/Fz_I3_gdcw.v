(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
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
    /\ munch [(bv_unsigned sp - 272, bv_unsigned sp); (0xb9f720, 0xb9f720 + 4); (0xb9f740, 0xb9f740 + 4); (0xb9f760, 0xb9f760 + 4); (0xb9f780, 0xb9f780 + 4);
              (NEXT_KEY, NEXT_KEY + 12); (KEYS + 8 * j, KEYS + 8 * j + 8); (TP_A + -96, TP_A + -88)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -16) [C8 s0e; C8 rae]
    /\ rw_cells asegs m' (bv_unsigned sp + -16 + -16) [C8 sp; C8 (Z_to_bv 64 SITE_gdc_once2)]
    /\ rw_cells asegs m' (bv_unsigned sp + -16 + -32) [CB 8 junk; C8 (Z_to_bv 64 RUN_ONCE_RET)]
    /\ rw_cells asegs m' (bv_unsigned sp + -16 + -128) (once_full_cells 0xb9f780 oldcb canary s6 s5 s4 s3 s2 s1 (Z_to_bv 64 (bv_unsigned sp + -16)))
    /\ rw_cells asegs m' (TP_A + -96) [C8 (Z_to_bv 64 (bv_unsigned sp + -16 + -128))]
    /\ rw_cells asegs m' 0xb9f780 [C4 (Z_to_bv 64 1)]
    /\ rw_cells asegs m' 0xb9f740 [C4 (Z_to_bv 64 2)]
    /\ rw_cells asegs m' 0xb9f720 [C4 (Z_to_bv 64 j)]
    /\ rw_cells asegs m' 0xb9f760 [C4 (Z_to_bv 64 1)]
    /\ rw_cells asegs m' NEXT_KEY [C4 (Z_to_bv 64 j)]
    /\ rw_cells asegs m' KEY_LOCK [C4 z64; C4 z64; C4 sh]
    /\ rw_cells asegs m' (KEYS + 8 * j) [C8 (Z_to_bv 64 NODTOR)]
    /\ ssp_cells m' canary
    /\ stk asegs m' lo (bv_unsigned sp + -16 + -128).

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
  intros until canary.
  intros TpIs StackOk LoFloor LoRoom SpCap ImgClean KeyOnceZ CtxOnceZ KeyCell KeyRetCell TsdPtr NextKeyCell NkBound KeyLockCells KeySlotJ KeySlotNk SlotChoice Canary CbSlot MemOk.
  subst tp. unfold e_gdc, ssp_cells in *. destruct Canary as [GotSspCell GuardCell].
  unfold got_ssp in GotSspCell. unfold ssp_guard in GotSspCell, GuardCell.
  pose proof (bv_unsigned_in_range 64 sp) as SpRange. unfold bv_modulus in SpRange. cbn [Z.of_N] in SpRange.
  pose proof (munch_refl [(bv_unsigned sp - 272, bv_unsigned sp); (0xb9f720, 0xb9f720 + 4); (0xb9f740, 0xb9f740 + 4); (0xb9f760, 0xb9f760 + 4);
              (0xb9f780, 0xb9f780 + 4); (NEXT_KEY, NEXT_KEY + 12); (KEYS + 8 * j, KEYS + 8 * j + 8); (TP_A + -96, TP_A + -88)] m) as Touched.
  pose proof (wmono_refl asegs m) as Grown.
  carve_frame 16%nat StackOk.
  do 4 zstep. do 5 zstep.
  tcall (T_run_once_enter_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 0x1f7640 oldcb canary);
    [ first [ eassumption | split; eassumption | reflexivity | unfold got_ssp, ssp_guard; lia ] .. | ].
  rename PC into Stack1, PC1 into KeyOnceBusy, PC2 into CbFrame1, PC3 into OnceFrame1, PC4 into OnceRa1, POST into RunOnceFrame1.
  clear PC0.
  unfold ONCE_RET_INIT.
  tcall (dctki_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo nk j sh kold w r);
    [ first [ reflexivity | eassumption | lia ] .. | ].
  rename PC into Stack2, PC0 into KeyIsJ, PC1 into KeyRetOne, PC2 into NextKeyJ, PC3 into KeyLockAfter, POST into KeySlotDtor.
  tcall (T_run_once_leave_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -16) 0xb9f740
           (Z_to_bv 64 (bv_unsigned sp + -16 + -128)) oldcb canary (Z_to_bv 64 0x1f76e4) sp s1 s2 s3 s4 s5 s6 _);
    [ first [ eassumption | split; eassumption | reflexivity | unfold got_ssp, ssp_guard; lia ] .. | ].
  rename PC into Stack3, PC1 into KeyOnceDone, POST into CbBack. clear PC0.
  zstep.
  th_if_lit.
  do 2 zstep. zstep.
  th_if_lit.
  do 5 zstep.
  tcall (T_run_once_enter_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 0x1f767c oldcb canary);
    [ first [ eassumption | split; eassumption | reflexivity | unfold got_ssp, ssp_guard; lia ] .. | ].
  finish.
  eassumption.
Qed.

(* [comment removed for export] *)
Definition gdc_w1_post (sp gp tp t0 t2 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rae s0e : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (oldcb canary : word) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t1' a1' a2' a3' : word) (m' : mem),
    ms = MS (mkR rae sp gp tp t0 t1' t2 s0e s1 (Z_to_bv 64 0xb9f580) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc rae) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 176, bv_unsigned sp); (0xb9f780, 0xb9f780 + 4); (TP_A + -96, TP_A + -88)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' 0xb9f780 [C4 (Z_to_bv 64 2)]
    /\ rw_cells asegs m' (TP_A + -96) [C8 oldcb]
    /\ ssp_cells m' canary
    /\ stk asegs m' lo (bv_unsigned sp).

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
  intros until junk.
  intros TpIs KeyBound ShadowChoice StackOk LoFloor LoRoom SpCap ImgClean ShadowBase GdcFrame RunOnceFrame OnceRa OnceFrame CbFrame
    CtxOnceBusy CtxRetOne KeyIsJ KeyShadow TsdPtr TsdSlotEmpty InitedFlag Canary MemOk.
  subst tp. unfold ssp_cells in Canary. destruct Canary as [GotSspCell GuardCell].
  unfold got_ssp in GotSspCell. unfold ssp_guard in GotSspCell, GuardCell. unfold g_shadow_memory_dynamic_address in ShadowBase.
  pose proof (bv_unsigned_in_range 64 sp) as SpRange. unfold bv_modulus in SpRange. cbn [Z.of_N] in SpRange.
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp); (0xb9f780, 0xb9f780 + 4); (TP_A + -96, TP_A + -88)] m) as Touched.
  pose proof (wmono_refl asegs m) as Grown.
  assert (OutsideImg : ut_fp [(bv_unsigned sp - 176, bv_unsigned sp); (0xb9f780, 0xb9f780 + 4); (TP_A + -96, TP_A + -88)]) by ut_fp_lia.
  tcall (T_run_once_leave_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -16) 0xb9f780
           (Z_to_bv 64 (bv_unsigned sp + -16 + -128)) oldcb canary (Z_to_bv 64 0x1f7708) sp s1 s2 s3 s4 s5 s6 junk);
    [ first [ eassumption | split; eassumption | reflexivity | unfold got_ssp, ssp_guard; lia ] .. | ].
  rename PC into Stack1, PC1 into CtxOnceDone, POST into CbBack. clear PC0.
  zstep. th_if_lit.
  do 2 zstep. zstep. th_if_lit.
  do 3 zstep.
  tcall (T_get_local_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo TSD_MAIN j sb z64);
    [ first [ eassumption | reflexivity | lia | exact (ut_munch _ m _ ImgClean Touched OutsideImg) ] .. | ].
  rename POST into Stack2.
  zstep. th_if_lit.
  do 6 zstep.
  do 2 zstep.
  release_frame GdcFrame Stack2 (bv_unsigned sp).
  do 2 zstep.
  finish.
  split; assumption.
Qed.
