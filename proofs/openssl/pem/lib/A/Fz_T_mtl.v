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
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit Fz_T_ekit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout PLayout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_mkit Fz_G_kit Fz_ckit Fz_env Fz_M_malloc Fz_M_zalloc Fz_M_locknew Fz_G_CRYPTO_calloc Fz_G_OPENSSL_sk_new_null Fz_G_OPENSSL_sk_set_cmp_thunks Fz_G_OPENSSL_sk_set_copy_thunks Fz_G_OPENSSL_sk_set_thunks Fz_G_create_global_tevent_register_ossl Th_tsd Th_key Th_mutex Th_once Fz_T_once Fz_T_local Fz_T_lock Fz_T_sk Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation zeros n := (repeat (Z_to_bv 8 0) n) (only parsing).
Notation TP_A := (0xba3ef0)%Z (only parsing).
Notation DTOR_KEY := (0x5a9f20)%Z (only parsing).      (* [comment removed for export] *)
Notation TEV_ONCE := (0xb9f4a0)%Z (only parsing).      (* [comment removed for export] *)
Notation TEV_RET := (0xb9f4c0)%Z (only parsing).
Notation TEV_REG := (0xb9f4e0)%Z (only parsing).
Definition e_mtl : Z := 0x1f4984.
Definition SITE_mtl_zalloc : Z := 0x1f4a04.
Definition SITE_mtl_once : Z := 0x1f4a44.
Definition SITE_mtl_push : Z := 0x1f4a9c.
Definition MTL_FILE : Z := 0x49180.

(* [comment removed for export] *)
Lemma mtl_w0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo k : Z),
  tp = Z_to_bv 64 TP_A ->
  rw_cells asegs m DTOR_KEY [C4 (Z_to_bv 64 k); C4 (Z_to_bv 64 0xffffffff)] -> 1 <= k < 128 ->
  ro_cells asegs m (DTOR_KEY / 8 + 2147450880) [C1 (Z_to_bv 8 0)] ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  ro_cells asegs m (TP_A + -88) [C8 (Z_to_bv 64 TSD_MAIN)] -> ro_cells asegs m (TSD_MAIN + 8 * k) [C8 z64] ->
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 80 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (t1' : word) (m' : mem),
       ms = MS (mkR (Z_to_bv 64 SITE_mtl_zalloc) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1' t2 sp z64 (Z_to_bv 64 8) (Z_to_bv 64 MTL_FILE) (Z_to_bv 64 143) a3 a4 a5 a6 a7
                    z64 (Z_to_bv 64 1) (Z_to_bv 64 0x5a99b8) (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_CRYPTO_zalloc) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ rw_cells asegs m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
       /\ stk asegs m' lo (bv_unsigned sp + -64))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) z64 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_mtl) fc None m (seg_rom asegs)).
Proof.
  intros until k. intros -> DK4 HK KSB UT SHC TSD SLOT ST LO0 LO HTOP MI. unfold e_mtl, g_shadow_memory_dynamic_address, SHB, SITE_mtl_zalloc, MTL_FILE, e_CRYPTO_zalloc in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  pose proof (proj1 (t_cells_halves asegs m DTOR_KEY k 0xffffffff ltac:(lia) ltac:(lia)) DK4) as DK8.
  assert (DKr : ro_cells asegs m DTOR_KEY [C4 (Z_to_bv 64 k)]).
  { pose proof DK4 as X. change [C4 (Z_to_bv 64 k); C4 (Z_to_bv 64 4294967295)] with ([C4 (Z_to_bv 64 k)] ++ [C4 (Z_to_bv 64 4294967295)]) in X.
    apply (proj1 (rw_cells_app _ _ _ _)) in X. exact (proj1 (proj1 X)). }
  set (Pk := TSD_MAIN + 8 * k) in *.
  th_frame 64%nat [8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  do 10 zstep. zstep. do 2 zstep. zstep. zstep. zstep. do 2 zstep.
  zstep. if_cases KD; zify_cond KD. { exfalso. rewrite ?unsigned_lit in KD by lia. lia. }
  do 2 zstep. zstep.
  tcall (T_get_local_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo TSD_MAIN k 0 (Z_to_bv 64 0));
    [exact DKr | lia | reflexivity | vm_compute; discriminate | lia | exact KSB | left; reflexivity | exact (ut_munch _ m _ UT MU HWU) | exact SHC | exact TSD | lia | lia | exact SLOT | lia | lia
    | eassumption | lia | lia | lia | assumption |].
  cbv delta [mkR].
  zstep. zstep. th_if_lit. zstep. th_if_lit.
  do 4 zstep. zstep.
  apply evt_done. do 2 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption | assumption].
Qed.

(* [comment removed for export] *)
Lemma mtl_w1 : forall (sp gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo k H : Z) (u : byte) (oldcb canary : word) (rav s0v s1v s2v s3v s4v s5v s6v : word),
  rw_cells asegs m DTOR_KEY [C4 (Z_to_bv 64 k); C4 (Z_to_bv 64 0xffffffff)] -> 1 <= k < 128 ->
  ro_cells asegs m (DTOR_KEY / 8 + 2147450880) [C1 (Z_to_bv 8 0)] ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  ro_cells asegs m (TP_A + -88) [C8 (Z_to_bv 64 TSD_MAIN)] -> rw_cells asegs m (TSD_MAIN + 8 * k) [C8 z64] -> rw_cells asegs m (TP_A + -150) [C1 u] ->
  rw_cells asegs m TEV_ONCE [C4 z64] -> ssp_cells m canary -> rw_cells asegs m (TP_A + -96) [C8 oldcb] ->
  0x10007fff8000 <= H -> H + 8 <= lo ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk asegs m lo (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 192 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (a0' a1' a2' a3' : word) (junk : list byte) (u' : byte) (m' : mem),
       ms = MS (mkR (Z_to_bv 64 ONCE_RET_INIT) (Z_to_bv 64 (bv_unsigned sp + -192)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 TEV_ONCE) (Z_to_bv 64 e_create_global_tevent_register_ossl)
                    a0' a1' a2' a3' a4 a5 a6 a7 z64 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 2) s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_create_global_tevent_register_ossl) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp - 192, bv_unsigned sp - 64); (TSD_MAIN + 8 * k, TSD_MAIN + 8 * k + 8); (TP_A + -150, TP_A + -149); (TEV_ONCE, TEV_ONCE + 4); (TP_A + -96, TP_A + -88)]%Z m m'
       /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ rw_cells asegs m' (bv_unsigned sp + -64) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]
       /\ stk asegs m' lo (bv_unsigned sp + -192) /\ ssp_cells m' canary
       /\ rw_cells asegs m' (TSD_MAIN + 8 * k) [C8 (Z_to_bv 64 H)] /\ rw_cells asegs m' (TP_A + -150) [C1 u']
       /\ rw_cells asegs m' TEV_ONCE [C4 (Z_to_bv 64 1)]
       /\ rw_cells asegs m' (TP_A + -96) [C8 (Z_to_bv 64 (bv_unsigned sp + -192))]
       /\ rw_cells asegs m' (bv_unsigned sp + -192) (once_full_cells TEV_ONCE oldcb canary s6 (Z_to_bv 64 SHB) (Z_to_bv 64 0x5a99b8) (Z_to_bv 64 1) (Z_to_bv 64 DTOR_KEY) (Z_to_bv 64 H) (Z_to_bv 64 (bv_unsigned sp + -64)))
       /\ rw_cells asegs m' (bv_unsigned sp + -96) [CB 8 junk; C8 (Z_to_bv 64 RUN_ONCE_RET)]
       /\ rw_cells asegs m' (bv_unsigned sp + -80) [C8 sp; C8 (Z_to_bv 64 SITE_mtl_once)])
    (MS (mkR (Z_to_bv 64 SITE_mtl_zalloc) (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp z64 (Z_to_bv 64 H) a1 a2 a3 a4 a5 a6 a7
            z64 (Z_to_bv 64 1) (Z_to_bv 64 0x5a99b8) (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_mtl_zalloc) fc None m (seg_rom asegs)).
Proof.
  intros until s6v. intros DK4 HK KSB UT SHC TSD SLOT UC ONC SSP CBC HHI HLO FR ST LO0 LO HTOP MI.
  unfold g_shadow_memory_dynamic_address, SHB, SITE_mtl_zalloc, SITE_mtl_once, e_create_global_tevent_register_ossl in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 192, bv_unsigned sp - 64); (TSD_MAIN + 8 * k, TSD_MAIN + 8 * k + 8); (TP_A + -150, TP_A + -149); (TEV_ONCE, TEV_ONCE + 4); (TP_A + -96, TP_A + -88)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (UTN : IMG_UT_HI + 150 <= TP_A /\ IMG_UT_HI <= TSD_MAIN) by (unfold IMG_UT_HI; lia).
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  pose proof (proj1 (t_cells_halves asegs m DTOR_KEY k 0xffffffff ltac:(lia) ltac:(lia)) DK4) as DK8.
  assert (DKr : ro_cells asegs m DTOR_KEY [C4 (Z_to_bv 64 k)]).
  { pose proof DK4 as X. change [C4 (Z_to_bv 64 k); C4 (Z_to_bv 64 4294967295)] with ([C4 (Z_to_bv 64 k)] ++ [C4 (Z_to_bv 64 4294967295)]) in X.
    apply (proj1 (rw_cells_app _ _ _ _)) in X. exact (proj1 (proj1 X)). }
  set (Pk := TSD_MAIN + 8 * k) in *. assert (HPk : TSD_MAIN + 8 <= Pk /\ Pk + 8 <= TSD_MAIN + 1024) by (unfold Pk; lia).
  cl_eu (bv_unsigned sp) (-64) EU1.
  zstep. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  zstep. zstep. zstep. zstep. if_cases KD; zify_cond KD. { exfalso. rewrite ?unsigned_lit in KD by lia. lia. }
  do 2 zstep. do 2 zstep. zstep.
  tcall (T_set_local_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo TSD_MAIN k 0 (Z_to_bv 64 0) u);
    [exact DKr | lia | reflexivity | vm_compute; discriminate | lia | exact KSB | left; reflexivity | exact (ut_munch _ m _ UT MU HWU) | exact SHC | exact TSD | lia | lia | exact SLOT | lia | lia | exact UC
    | lia | lia | lia | lia | exact (proj2 UTN) | exact (proj1 UTN) | eassumption | lia | lia | lia | assumption |].
  cbv delta [mkR].
  zstep. th_if_lit.
  do 4 zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (SSPc : rw_cells asegs mc got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells asegs mc ssp_guard [C8 canary])
      by (unfold got_ssp, ssp_guard in *; split; [apply (rw_cells_agree asegs m mc _ _ (proj1 SSP)) | apply (rw_cells_agree asegs m mc _ _ (proj2 SSP))];
          [ | exact WM | | exact WM]; intros y Hy; apply MU; cbv beta in Hy; unfold got_ssp, ssp_guard in Hy; cbn [outside cells_size csize Nat.add] in *; repeat split; try exact I; lia) end.
  unfold got_ssp, ssp_guard in SSPc.
  pose proof T_run_once_enter_proof as OE. unfold T_run_once_enter_stmt, ssp_cells, got_ssp, ssp_guard in OE.
  tcall (OE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 0x1f4b64 oldcb canary).
  1-21: first [eassumption | reflexivity | lia | split; eassumption].
  clear OE. cbv beta delta [mkR]. try th_ret_lit.
  replace (bv_unsigned sp + -64 + -128) with (bv_unsigned sp + -192) in * by lia. replace (bv_unsigned sp + -64 + -32) with (bv_unsigned sp + -96) in * by lia.
  replace (bv_unsigned sp + -64 + -16) with (bv_unsigned sp + -80) in * by lia.
  finish. all: eassumption.
Qed.

(* [comment removed for export] *)
Lemma mtl_w2 : forall (sp gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo H G SK LK : Z) (oldcb canary : word) (junk : list byte) (rav s0v s1v s2v s3v s4v s5v s6v : word),
  rw_cells asegs m TEV_ONCE [C4 (Z_to_bv 64 1)] -> ssp_cells m canary -> rw_cells asegs m (TP_A + -96) [C8 (Z_to_bv 64 (bv_unsigned sp + -192))] ->
  rw_cells asegs m (bv_unsigned sp + -192) (once_full_cells TEV_ONCE oldcb canary s6 (Z_to_bv 64 SHB) (Z_to_bv 64 0x5a99b8) (Z_to_bv 64 1) (Z_to_bv 64 DTOR_KEY) (Z_to_bv 64 H) (Z_to_bv 64 (bv_unsigned sp + -64))) ->
  rw_cells asegs m (bv_unsigned sp + -96) [CB 8 junk; C8 (Z_to_bv 64 RUN_ONCE_RET)] -> rw_cells asegs m (bv_unsigned sp + -80) [C8 sp; C8 (Z_to_bv 64 SITE_mtl_once)] ->
  rw_cells asegs m TEV_RET [C4 (Z_to_bv 64 1)] -> rw_cells asegs m TEV_REG [C8 (Z_to_bv 64 G)] ->
  0x10007fff8000 <= G -> G mod 8 = 0 -> G + 16 <= lo -> rw_cells asegs m G [C8 (Z_to_bv 64 SK); C8 (Z_to_bv 64 LK)] -> acc asegs m G 16 ->
  0x10007fff8000 <= LK -> LK mod 8 = 0 -> LK + 40 <= lo -> rw_cells asegs m LK (mutex_cells z64 z64) -> (G + 16 <= LK \/ LK + 40 <= G) ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk asegs m lo (bv_unsigned sp + -192) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 224 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (a2' a3' a4' a5' : word) (m' : mem),
       ms = MS (mkR (Z_to_bv 64 SITE_mtl_push) (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp (Z_to_bv 64 H) (Z_to_bv 64 SK) (Z_to_bv 64 H) a2' a3' a4' a5' a6 a7
                    (Z_to_bv 64 DTOR_KEY) (Z_to_bv 64 (G + 8)) (Z_to_bv 64 G) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.shiftr (G + 8) 3 + SHB)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_sk_push) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp - 224, bv_unsigned sp - 64); (TEV_ONCE, TEV_ONCE + 4); (TP_A + -96, TP_A + -88); (LK + 4, LK + 8)]%Z m m'
       /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ rw_cells asegs m' (bv_unsigned sp + -64) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]
       /\ stk asegs m' lo (bv_unsigned sp + -64) /\ ssp_cells m' canary
       /\ rw_cells asegs m' TEV_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m' (TP_A + -96) [C8 oldcb]
       /\ rw_cells asegs m' LK (mutex_cells z64 (Z_to_bv 64 16)) /\ rw_cells asegs m' G [C8 (Z_to_bv 64 SK); C8 (Z_to_bv 64 LK)])
    (MS (mkR (Z_to_bv 64 ONCE_RET_INIT) (Z_to_bv 64 (bv_unsigned sp + -192)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 TEV_ONCE) (Z_to_bv 64 e_create_global_tevent_register_ossl)
            (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 z64 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 2) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ONCE_RET_INIT) fc None m (seg_rom asegs)).
Proof.
  intros until s6v. intros ONC SSP CBC FULL JR FRW TRET TREG GHI GAL GLO GC ACCG LKHI LKAL LKLO LKC DISJ UT SHC FR ST LO0 LO HTOP MI.
  unfold g_shadow_memory_dynamic_address, SHB, SITE_mtl_once, SITE_mtl_push, e_sk_push, e_create_global_tevent_register_ossl in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp - 64); (TEV_ONCE, TEV_ONCE + 4); (TP_A + -96, TP_A + -88); (LK + 4, LK + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  cl_eu (bv_unsigned sp) (-64) EU1. cl_eu (bv_unsigned sp) (-192) EU3.
  unfold mutex_cells in LKC.
  pose proof (T_run_once_leave_proof) as OL. unfold T_run_once_leave_stmt, ssp_cells, got_ssp, ssp_guard, ONCE_RET_INIT in OL. unfold ssp_cells, got_ssp, ssp_guard in SSP. unfold ONCE_RET_INIT, ssp_guard, got_ssp. replace (bv_unsigned sp + -192) with (bv_unsigned sp + -64 + -128) in * by lia.
  replace (bv_unsigned sp + -96) with (bv_unsigned sp + -64 + -32) in JR by lia. replace (bv_unsigned sp + -80) with (bv_unsigned sp + -64 + -16) in FRW by lia.
  tcall (OL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -64) TEV_ONCE (Z_to_bv 64 (bv_unsigned sp + -64 + -128)) oldcb canary
              (Z_to_bv 64 0x1f4a44) sp (Z_to_bv 64 H) (Z_to_bv 64 DTOR_KEY) (Z_to_bv 64 1) (Z_to_bv 64 0x5a99b8) (Z_to_bv 64 2147450880) s6 junk).
  1-22: first [eassumption | reflexivity | lia | split; eassumption].
  clear OL. cbv beta delta [mkR].
  zstep. th_if_lit. zstep. zstep. zstep. th_if_lit.
  zstep. zstep. zstep. if_cases KG; zify_cond KG. { exfalso. rewrite ?unsigned_lit in KG by lia. lia. }
  zstep. do 2 zstep. zstep. zstep. th_if_lit.
  zstep. zstep.
  tcall (T_write_lock_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo);
    [first [eassumption | rewrite unsigned_lit by lia; first [eassumption | lia | clear - LKAL; Z.div_mod_to_equations; lia] | lia] .. |].
  cbv delta [mkR].
  zstep. th_if_lit. do 2 zstep. zstep. zstep. th_if_lit. zstep. zstep. zstep.
  unfold mutex_cells. finish. all: try eassumption.
  all: lazymatch goal with |- ssp_cells ?mc _ => split;
        [ apply (rw_cells_agree asegs m mc _ _ (proj1 SSP)) | apply (rw_cells_agree asegs m mc _ _ (proj2 SSP)) ];
        [ | exact WM | | exact WM ]; intros y Hy; apply MU; cbv beta in Hy; cbn [outside cells_size csize Nat.add] in *; repeat split; try exact I; lia end.
Qed.

(* [comment removed for export] *)
Lemma mtl_w3 : forall (sp gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo H G LK : Z) (rav s0v s1v s2v s3v s4v s5v s6v : word),
  0x10007fff8000 <= G -> G mod 8 = 0 -> G + 16 <= lo -> acc asegs m G 16 ->
  0x10007fff8000 <= LK -> LK mod 8 = 0 -> LK + 40 <= lo -> rw_cells asegs m LK (mutex_cells z64 (Z_to_bv 64 16)) -> rw_cells asegs m (G + 8) [C8 (Z_to_bv 64 LK)] ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk asegs m lo (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 224 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (a1' a2' a3' : word) (m' : mem),
       ms = MS (mkR rav sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0v s1v (Z_to_bv 64 H) a1' a2' a3' a4 a5 a6 a7 s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc rav) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp - 176, bv_unsigned sp - 64); (LK + 4, LK + 8)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' LK (mutex_cells z64 z64))
    (MS (mkR (Z_to_bv 64 SITE_mtl_push) (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp (Z_to_bv 64 H) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
            (Z_to_bv 64 DTOR_KEY) (Z_to_bv 64 (G + 8)) (Z_to_bv 64 G) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.shiftr (G + 8) 3 + SHB)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_mtl_push) fc None m (seg_rom asegs)).
Proof.
  intros until s6v. intros GHI GAL GLO ACCG LKHI LKAL LKLO LKC GC8 UT SHC FR ST LO0 LO HTOP MI.
  unfold g_shadow_memory_dynamic_address, SHB, SITE_mtl_push in *. unfold mutex_cells in LKC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp - 64); (LK + 4, LK + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  cl_eu (bv_unsigned sp) (-64) EU1.
  zstep. zstep. th_if_lit. zstep. zstep. zstep.
  tcall (T_unlock_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo);
    [first [eassumption | rewrite unsigned_lit by lia; first [eassumption | lia | clear - LKAL; Z.div_mod_to_equations; lia] | lia] .. |].
  cbv delta [mkR].
  zstep. th_if_lit. zstep. do 8 zstep. th_release FR (bv_unsigned sp). do 2 zstep.
  unfold mutex_cells. finish. all: eassumption.
Qed.

Section CMtl.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_CZ : crypto_zalloc_env_stmt RT.
Hypothesis C_CALLOC : CRYPTO_calloc_stmt RT.
Hypothesis C_TEV : create_global_tevent_register_ossl_stmt RT.
Hypothesis GO_dtor : GOBJ DTOR_KEY 8.
(* [comment removed for export] *)
Hypothesis TSD : forall Σ m, ART RT Σ m -> rw_cells asegs m (TP_A + -88) [C8 (Z_to_bv 64 TSD_MAIN)].

Definition TEV_SITES : list (Z * Z) :=
  [(SITE_create_global_tevent_register_ossl_1, e_create_global_tevent_register_ossl); (SITE_create_global_tevent_register_ossl_2, e_create_global_tevent_register_ossl);
   (SITE_create_global_tevent_register_ossl_3, e_create_global_tevent_register_ossl); (SITE_create_global_tevent_register_ossl_4, e_create_global_tevent_register_ossl);
   (SITE_create_global_tevent_register_ossl_5, e_create_global_tevent_register_ossl); (SITE_create_global_tevent_register_ossl_6, e_create_global_tevent_register_ossl);
   (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc); (SITE_OPENSSL_sk_new_null_1, e_OPENSSL_sk_new_null); (SITE_ln_zalloc, e_lock_new)].
Definition TEV_CALLS : list (Z * Z) :=
  [(SITE_create_global_tevent_register_ossl_1, e_CRYPTO_zalloc); (SITE_create_global_tevent_register_ossl_2, e_OPENSSL_sk_new_null);
   (SITE_create_global_tevent_register_ossl_3, e_OPENSSL_sk_set_cmp_thunks); (SITE_create_global_tevent_register_ossl_4, e_OPENSSL_sk_set_copy_thunks);
   (SITE_create_global_tevent_register_ossl_5, e_OPENSSL_sk_set_thunks); (SITE_create_global_tevent_register_ossl_6, e_lock_new); (SITE_cz_malloc, e_CRYPTO_malloc);
   (SITE_cm_malloc, e_malloc); (SITE_OPENSSL_sk_new_null_1, e_CRYPTO_zalloc); (SITE_ln_zalloc, e_CRYPTO_zalloc)].
Definition MTL_SITES : list (Z * Z) := [(SITE_mtl_zalloc, e_mtl); (SITE_mtl_push, e_mtl)] ++ TEV_SITES ++ SKI_SITES.
Definition MTL_CALLS : list (Z * Z) :=
  [(SITE_mtl_zalloc, e_CRYPTO_zalloc); (SITE_mtl_push, e_sk_push); (SITE_mtl_push, e_sk_insert); (ONCE_RET_INIT, e_create_global_tevent_register_ossl)] ++ TEV_CALLS ++ SKI_CALLS.
Definition MTL_W (k : Z) : list (Z * Z) :=
  [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (TSD_MAIN + 8 * k, TSD_MAIN + 8 * k + 8); (TP_A + -150, TP_A + -149); (TEV_ONCE, TEV_ONCE + 4); (TEV_RET, TEV_RET + 4); (TEV_REG, TEV_REG + 8);
   (TP_A + -96, TP_A + -88)].
Definition TEV_CMP : Z := 2051308. Definition TEV_FREE : Z := 2051268. Definition TEV_COPY : Z := 2051352.

(* [comment removed for export] *)
Definition mtl_first_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (k : Z) (u : byte) (r0 g0 oldcb : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 1 -> a1 = Z_to_bv 64 0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x2f0 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_mtl (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) MTL_SITES MTL_CALLS ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 5 <= LIVE_MAX -> 1 <= rt_credit RT Σ -> cl_env m lb canary ->
  rw_cells asegs m DTOR_KEY [C4 (Z_to_bv 64 k); C4 (Z_to_bv 64 0xffffffff)] -> 1 <= k < 128 ->
  rw_cells asegs m (TSD_MAIN + 8 * k) [C8 z64] -> rw_cells asegs m (TP_A + -150) [C1 u] ->
  rw_cells asegs m TEV_ONCE [C4 z64] -> rw_cells asegs m TEV_RET [C4 r0] -> rw_cells asegs m TEV_REG [C8 g0] -> rw_cells asegs m (TP_A + -96) [C8 oldcb] ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_mtl m)))
    (fun c => exists (Σ' : rts RT) (H G SK LK D : Z) (u' : byte),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 H) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (MTL_W k) m m'
           /\ cl_env m' (Z_to_bv 8 1) canary
           /\ rw_cells asegs m' (TSD_MAIN + 8 * k) [C8 (Z_to_bv 64 H)] /\ rw_cells asegs m' (TP_A + -150) [C1 u']
           /\ rw_cells asegs m' TEV_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m' TEV_RET [C4 (Z_to_bv 64 1)] /\ rw_cells asegs m' TEV_REG [C8 (Z_to_bv 64 G)]
           /\ rw_cells asegs m' (TP_A + -96) [C8 oldcb]
           /\ rw_cells asegs m' H [C8 z64] /\ rw_cells asegs m' G [C8 (Z_to_bv 64 SK); C8 (Z_to_bv 64 LK)]
           /\ rw_cells asegs m' SK (sk_cells (Z_to_bv 64 1) z64 (Z_to_bv 64 D) (Z_to_bv 64 1) (Z_to_bv 64 4) z64 (Z_to_bv 64 TEV_CMP) (Z_to_bv 64 TEV_FREE) (Z_to_bv 64 TEV_COPY))
           /\ rw_cells asegs m' LK (mutex_cells z64 z64) /\ rw_cells asegs m' D [C8 (Z_to_bv 64 H); CB 24 (zeros 24)]) c
       /\ rt_live RT Σ' = [(D, 32); (LK, 40); (SK, 56); (G, 16); (H, 8)] ++ rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - 1 /\ rt_cg RT Σ' = rt_cg RT Σ
       /\ Forall (fun b => 0x10007fff8000 <= fst b /\ fst b mod 16 = 0 /\ fst b + snd b < USTACK_TOP) [(D, 32); (LK, 40); (SK, 56); (G, 16); (H, 8)]).

Theorem mtl_first_cps : mtl_first_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary k u r0 g0 oldcb
    FDO MST -> -> -> ART0 MI0 CALL HSTK CTX UWC CGH Hfr Hlen Hcr CLE DK4 HK SLOT UC ONC TRET TREG CBC.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 752 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -64). set (usp2 := usp + -192).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (EU2 : bv_unsigned (Z_to_bv 64 usp2) = usp2) by (apply unsigned_lit; unfold usp2, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (HLO1 : lo <= usp - 224) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (afp_gsh_byte RT GOBJ AFP Σ m _ _ DTOR_KEY ART0 GO_dtor ltac:(lia) ltac:(lia) ltac:(reflexivity)) as KSB0. cbn [Z.ltb Z.sub Z.add Z.leb] in KSB0.
  (* [comment removed for export] *)
  pose proof (mtl_w0 ra sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo k
                eq_refl DK4 HK KSB0 UT SHC (proj1 (TSD Σ m ART0)) (proj1 SLOT) ST HLOS ltac:(lia) SPH MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (u1 & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 80 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 80 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG01 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  assert (BELOW1 : forall P : Z -> Prop, (forall x, P x -> x < usp - 80) -> agree_on P m m1) by (intros P HP a Ha; apply MU1; cbn [outside]; pose proof (HP _ Ha); split; [lia| exact I]).
  pose proof (cl_env_seg _ m m1 lb canary CLE MU1 ltac:(cl_fp_lia)) as CLE1.
  assert (STAT1 : forall a cs, rw_cells asegs m a cs -> a + Z.of_nat (cells_size cs) <= 0xbc6000 -> rw_cells asegs m1 a cs).
  { intros a cs X H1. apply (rw_cells_agree asegs m m1 _ _ X); [| exact WM1]. apply BELOW1. intros; lia. }
  pose proof (STAT1 _ _ DK4 ltac:(cbn; lia)) as DK4_1. pose proof (STAT1 _ _ SLOT ltac:(cbn; lia)) as SLOT1. pose proof (STAT1 _ _ UC ltac:(cbn; lia)) as UC1.
  pose proof (STAT1 _ _ ONC ltac:(cbn; lia)) as ONC1. pose proof (STAT1 _ _ TRET ltac:(cbn; lia)) as TRET1. pose proof (STAT1 _ _ TREG ltac:(cbn; lia)) as TREG1. pose proof (STAT1 _ _ CBC ltac:(cbn; lia)) as CBC1.
  assert (FRR1 : rw_cells asegs m1 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp1 + Z.of_nat (cells_size [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; unfold usp1; lia).
    exact (rw_cells_skip m1 usp1 [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR1). }
  destruct (cl_chain_call (rt_cg RT Σ) e_mtl e_CRYPTO_zalloc SITE_mtl_zalloc m m1 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH _ ltac:(left; reflexivity)) (proj2 CGH _ ltac:(left; reflexivity)) UWC AG01 FRR1 ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTX1 & UWC1).
  pose proof (uw_chain_agree outer m m1 sp s0 UWC AG01) as UWCm1.
  (* [comment removed for export] *)
  apply (C_CZ Σ PMc (Z_to_bv 64 SITE_mtl_zalloc) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) t0 u1 t2 sp (Z_to_bv 64 0) (Z_to_bv 64 8) (Z_to_bv 64 MTL_FILE) (Z_to_bv 64 143) a3 a4 a5 a6 a7
           (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0x5a99b8) (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 8 lo (bv_unsigned ra :: outer) lb canary
           FDO MST eq_refl eq_refl ltac:(lia) ART1 MI1).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 4. }
  { rewrite EU1. unfold usp1, RT_STACK in *. clear - HSTK. lia. }
  { rewrite (unsigned_lit SITE_mtl_zalloc) by (unfold SITE_mtl_zalloc; lia). exact CTX1. }
  { exact UWC1. }
  { apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { lia. } { change (mcost 8) with 0. lia. } { exact CLE1. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & H & Hc2 & LV1 & FRS1 & SP1 & CR1 & H0 & H16 & HU & CG1). change (mcost 8) with 0 in CR1.
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & CLE2 & WRH & ACCH & ZH) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & q1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_mtl_zalloc) in Hc2' by (unfold SITE_mtl_zalloc; lia). change (Z.to_nat 8) with 8%nat in ZH.
  assert (INH : In (H, 8) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
  pose proof (af_live_range RT AF Σ1 m2 H 8 ART2 INH) as (_ & HLO & _). rewrite SP1 in HLO.
  pose proof (afp_live_hi RT GOBJ AFP Σ1 m2 H 8 ART2 INH ltac:(lia)) as HHI.
  assert (AG2 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp1 x /\ x <> G_ALLOW_CUST) -> agree_on P m1 m2).
  { intros P HP a Ha. destruct (HP _ Ha) as (X1 & X2). apply PRES2; [exact X1|]. unfold G_ALLOW_CUST in *. cbn [outside]. split; [lia | exact I]. }
  assert (STAT2 : forall a cs, rw_cells asegs m1 a cs ->
            (0x5a9d08 <= a /\ a + Z.of_nat (cells_size cs) <= 0x6694d8) \/ (0xb8f190 <= a /\ a + Z.of_nat (cells_size cs) <= 0xba3e98 /\ (a + Z.of_nat (cells_size cs) <= 0xb9f7c0 \/ 0xb9f7c1 <= a))
            \/ (0xbc52a0 <= a /\ a + Z.of_nat (cells_size cs) <= 0xbc57d0) -> rw_cells asegs m2 a cs).
  { intros a cs X H1. apply (rw_cells_agree asegs m1 m2 _ _ X); [| exact WM2]. apply AG2. intros x Hx. split; [right; left; apply client_static_intro; lia | unfold G_ALLOW_CUST; lia]. }
  pose proof (STAT2 _ _ DK4_1 ltac:(cbn; lia)) as DK4_2. pose proof (STAT2 _ _ SLOT1 ltac:(cbn; lia)) as SLOT2. pose proof (STAT2 _ _ UC1 ltac:(cbn; lia)) as UC2.
  pose proof (STAT2 _ _ ONC1 ltac:(cbn; lia)) as ONC2. pose proof (STAT2 _ _ TRET1 ltac:(cbn; lia)) as TRET2. pose proof (STAT2 _ _ TREG1 ltac:(cbn; lia)) as TREG2. pose proof (STAT2 _ _ CBC1 ltac:(cbn; lia)) as CBC2.
  eassert (FR2 : rw_cells asegs m2 usp1 _).
  { apply (rw_cells_agree asegs m1 m2 _ _ FR1); [| exact WM2]. apply AG2. cbn [cells_size csize Nat.add]. intros x Hx. split; [left; unfold usp1, USTACK_TOP in *; lia | unfold G_ALLOW_CUST, usp1, STACK_WIN, RT_STACK in *; lia]. }
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & SHC2 & _ & _ & UT2).
  pose proof (afp_gsh_byte RT GOBJ AFP Σ1 m2 _ _ DTOR_KEY ART2 GO_dtor ltac:(lia) ltac:(lia) ltac:(reflexivity)) as KSB2. cbn [Z.ltb Z.sub Z.add Z.leb] in KSB2.
  pose proof (uw_chain_agree outer m1 m2 sp s0 UWCm1 ltac:(apply AG2; intros x Hx; cbv beta in Hx; split; [left; unfold usp1; lia | unfold G_ALLOW_CUST, USTACK_TOP, STACK_WIN, RT_STACK in *; lia])) as UWCm2.
  (* [comment removed for export] *)
  pose proof (mtl_w1 sp gp u0 q1 u2 b1 b2 b3 b4 b5 b6 b7 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 lo k H u oldcb canary ra s0 s1 s2 s3 s4 s5 s6
                DK4_2 HK KSB2 UT2 SHC2 (proj1 (TSD Σ1 m2 ART2)) SLOT2 UC2 ONC2 (cl_env_ssp m2 _ canary UT2 CLE2) CBC2 HHI ltac:(clear - HLO LOW; lia)
                FR2 ST2 HLOS ltac:(clear - HLO1; lia) SPH MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (a0' & a1' & a2' & a3' & junk & u' & m3 & -> & MU3 & WM3 & MI3 & FR3 & ST3 & SSP3 & SLOT3 & UC3 & ONC3 & CBC3 & FULL3 & JR3 & FRW3) & Hc3'). clear Hc3.
  fold usp in MU3, ST3, FR3, CBC3, FULL3, JR3, FRW3. fold usp1 in FR3. fold usp2 in ST3, CBC3, FULL3.
  assert (MU3' : munch ([(TSD_MAIN + 8 * k, TSD_MAIN + 8 * k + 8); (TP_A + -150, TP_A + -149); (TEV_ONCE, TEV_ONCE + 4); (TP_A + -96, TP_A + -88)] ++ [(usp - 192, usp)]) m2 m3)
    by (eapply munch_weaken; [| exact MU3]; unfold sub_fp; cbn [outside app]; intros; lia).
  pose proof (cl_seg_ART RT AF Σ1 m2 m3 usp 192 _ ART2 ltac:(rewrite SP1; lia) ltac:(unfold USTACK_TOP in *; lia) MU3' ltac:(intros x Hx; apply client_static_intro; cbn [outside app] in Hx; lia) WM3) as ART3.
  assert (AG23 : agree_on (fun x => usp <= x < USTACK_TOP) m2 m3) by (intros a Ha; apply MU3; cbn [outside]; cbv beta in Ha; unfold USTACK_TOP in *; repeat split; try exact I; lia).
  pose proof (cl_env_seg _ m2 m3 _ canary CLE2 MU3 ltac:(cl_fp_lia)) as CLE3.
  pose proof (uw_chain_agree outer m2 m3 sp s0 UWCm2 AG23) as UWCm3.
  assert (OFF3 : forall P : Z -> Prop, (forall x, P x -> ~ (usp - 192 <= x < usp - 64) /\ ~ (TSD_MAIN + 8 * k <= x < TSD_MAIN + 8 * k + 8) /\ ~ (TP_A + -150 <= x < TP_A + -149)
                                                   /\ ~ (TEV_ONCE <= x < TEV_ONCE + 4) /\ ~ (TP_A + -96 <= x < TP_A + -88)) -> agree_on P m2 m3).
  { intros P HP a Ha. apply MU3. cbn [outside]. destruct (HP _ Ha) as (X1 & X2 & X3 & X4 & X5). repeat split; try exact I; lia. }
  assert (DK4_3 : rw_cells asegs m3 DTOR_KEY [C4 (Z_to_bv 64 k); C4 (Z_to_bv 64 0xffffffff)]) by (apply (rw_cells_agree asegs m2 m3 _ _ DK4_2); [apply OFF3; cbn [cells_size csize Nat.add]; intros; lia | exact WM3]).
  assert (TRET3 : rw_cells asegs m3 TEV_RET [C4 r0]) by (apply (rw_cells_agree asegs m2 m3 _ _ TRET2); [apply OFF3; cbn [cells_size csize Nat.add]; intros; lia | exact WM3]).
  assert (TREG3 : rw_cells asegs m3 TEV_REG [C8 g0]) by (apply (rw_cells_agree asegs m2 m3 _ _ TREG2); [apply OFF3; cbn [cells_size csize Nat.add]; intros; lia | exact WM3]).
  assert (HC3 : rw_cells asegs m3 H [C8 (Z_to_bv 64 0)]).
  { assert (HC2 : rw_cells asegs m2 H [C8 (Z_to_bv 64 0)]) by (split; [split; [cbn; repeat split; reflexivity | exact ZH] | exact WRH]).
    apply (rw_cells_agree asegs m2 m3 _ _ HC2); [apply OFF3; cbn [cells_size csize Nat.add]; unfold usp in *; intros; lia | exact WM3]. }
  rewrite <- CG1 in CGH.
  (* [comment removed for export] *)
  apply (C_TEV Σ1 PMc (Z_to_bv 64 ONCE_RET_INIT) (Z_to_bv 64 usp2) gp (Z_to_bv 64 TP_A) u0 q1 u2 (Z_to_bv 64 TEV_ONCE) (Z_to_bv 64 e_create_global_tevent_register_ossl) a0' a1' a2' a3' b4 b5 b6 b7
           (Z_to_bv 64 0) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 2) s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m3 lo [] (Z_to_bv 8 1) canary r0 g0
           FDO MST eq_refl ART3 MI3).
  { unfold call_ok. rewrite EU2. split; [exact ST3|]. split; [rewrite SP1; exact LOW|]. split; [unfold usp2, RT_STACK in *; lia|]. split; [unfold usp2, USTACK_TOP in *; lia|].
    unfold usp2. fold usp in SPA. clear - SPA. Z.div_mod_to_equations. lia. }
  { rewrite EU2. unfold usp2, RT_STACK in *. lia. }
  { rewrite (unsigned_lit ONCE_RET_INIT) by (unfold ONCE_RET_INIT; lia). split; [| exact I]. apply (proj2 CGH). cbn [MTL_CALLS In app]. tauto. }
  { cbn [uw_chain]. left. rewrite (unsigned_lit TEV_ONCE), EU2 by lia. unfold usp2, RT_STACK in *. lia. }
  { apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { rewrite FRS1. exact Hfr. }
  { rewrite LV1. cbn [length]. lia. }
  { rewrite CR1. change (mcost 16 + mcost 56 + 1) with 1. lia. }
  { exact CLE3. } { exact TRET3. } { exact TREG3. }
  { exact Hc3'. }
  clear Hc3'. intros c4 (Σ2 & G & SK & LK & Hc4 & LV2 & FRS2 & SP2 & CR2 & G0 & G16 & GU & SK0 & SK16 & SKU & LK0 & LK16 & LKU & CG2). change (mcost 16 + mcost 56 + 1) with 1 in CR2.
  destruct (ASTA_unpack RT Σ2 _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & CLE4 & WRG & ACCG & WRS & ACCS & WRL & ACCL & TRET4 & GC4 & TREG4 & SKC4 & LKC4) & Hc4'). clear Hc4.
  destruct RS4 as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F4 & fc4 & ->).
  rewrite EU2 in ST4, PRES4. rewrite (ret_pc_even ONCE_RET_INIT) in Hc4' by (unfold ONCE_RET_INIT; lia).
  assert (ING : In (G, 16) (rt_live RT Σ2)) by (rewrite LV2; right; right; left; reflexivity).
  assert (INSK : In (SK, 56) (rt_live RT Σ2)) by (rewrite LV2; right; left; reflexivity).
  assert (INLK : In (LK, 40) (rt_live RT Σ2)) by (rewrite LV2; left; reflexivity).
  assert (INH2 : In (H, 8) (rt_live RT Σ2)) by (rewrite LV2; right; right; right; exact INH).
  pose proof (af_live_range RT AF Σ2 m4 G 16 ART4 ING) as (_ & GLO & _). rewrite SP2, SP1 in GLO.
  pose proof (af_live_range RT AF Σ2 m4 LK 40 ART4 INLK) as (_ & LKLO & _). rewrite SP2, SP1 in LKLO.
  pose proof (af_live_range RT AF Σ2 m4 SK 56 ART4 INSK) as (_ & SKLO & _). rewrite SP2, SP1 in SKLO.
  pose proof (afp_live_hi RT GOBJ AFP Σ2 m4 G 16 ART4 ING ltac:(lia)) as GHI. pose proof (afp_live_hi RT GOBJ AFP Σ2 m4 LK 40 ART4 INLK ltac:(lia)) as LKHI.
  pose proof (afp_live_hi RT GOBJ AFP Σ2 m4 SK 56 ART4 INSK ltac:(lia)) as SKHI.
  pose proof (af_live_disj RT AF Σ2 m4 LK 40 G 16 [] ((SK, 56) :: (G, 16) :: rt_live RT Σ1) ART4 LV2 ltac:(right; left; reflexivity)) as DJ_LG.
  pose proof (af_live_disj RT AF Σ2 m4 LK 40 SK 56 [] ((SK, 56) :: (G, 16) :: rt_live RT Σ1) ART4 LV2 ltac:(left; reflexivity)) as DJ_LS.
  pose proof (af_live_disj RT AF Σ2 m4 SK 56 G 16 [(LK, 40)] ((G, 16) :: rt_live RT Σ1) ART4 LV2 ltac:(right; left; reflexivity)) as DJ_SG.
  assert (AG4 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp2 x /\ x <> G_ALLOW_CUST /\ ~ (TEV_REG <= x < TEV_REG + 8) /\ ~ (TEV_RET <= x < TEV_RET + 4)) -> agree_on P m3 m4).
  { intros P HP a Ha. destruct (HP _ Ha) as (X1 & X2 & X3 & X4). apply PRES4; [exact X1|]. unfold G_ALLOW_CUST in *. cbn [outside]. repeat split; try exact I; lia. }
  assert (STK4 : forall a cs, rw_cells asegs m3 a cs -> usp2 <= a -> a + Z.of_nat (cells_size cs) <= usp -> rw_cells asegs m4 a cs).
  { intros a cs X H1 H2. apply (rw_cells_agree asegs m3 m4 _ _ X); [| exact WM4]. apply AG4. intros x Hx. split; [left; unfold USTACK_TOP in *; lia|]. unfold G_ALLOW_CUST, usp2, STACK_WIN, RT_STACK in *. lia. }
  pose proof (STK4 _ _ FR3 ltac:(unfold usp1, usp2; lia) ltac:(cbn; unfold usp1; lia)) as FR4.
  pose proof (STK4 _ _ FULL3 ltac:(lia) ltac:(cbn; unfold usp2; lia)) as FULL4.
  pose proof (STK4 _ _ JR3 ltac:(unfold usp2; lia) ltac:(cbn; lia)) as JR4. pose proof (STK4 _ _ FRW3 ltac:(unfold usp2; lia) ltac:(cbn; lia)) as FRW4.
  assert (STAT4 : forall a cs, rw_cells asegs m3 a cs ->
            (0x5a9d08 <= a /\ a + Z.of_nat (cells_size cs) <= 0x6694d8) \/ (0xb8f190 <= a /\ a + Z.of_nat (cells_size cs) <= 0xba3e98 /\ (a + Z.of_nat (cells_size cs) <= 0xb9f4c0 \/ 0xb9f4e8 <= a) /\ (a + Z.of_nat (cells_size cs) <= 0xb9f7c0 \/ 0xb9f7c1 <= a))
            \/ (0xbc52a0 <= a /\ a + Z.of_nat (cells_size cs) <= 0xbc57d0) -> rw_cells asegs m4 a cs).
  { intros a cs X H1. apply (rw_cells_agree asegs m3 m4 _ _ X); [| exact WM4]. apply AG4. intros x Hx. split; [right; left; apply client_static_intro; lia | unfold G_ALLOW_CUST; lia]. }
  pose proof (STAT4 _ _ DK4_3 ltac:(cbn; lia)) as DK4_4. pose proof (STAT4 _ _ SLOT3 ltac:(cbn; lia)) as SLOT4. pose proof (STAT4 _ _ UC3 ltac:(cbn; lia)) as UC4.
  pose proof (STAT4 _ _ ONC3 ltac:(cbn; lia)) as ONC4. pose proof (STAT4 _ _ CBC3 ltac:(cbn; lia)) as CBC4.
  assert (HC4 : rw_cells asegs m4 H [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_agree asegs m3 m4 _ _ HC3); [| exact WM4]. apply AG4. cbn [cells_size csize Nat.add]. intros x Hx. split; [apply (acl_live _ _ _ H 8); [exact INH | lia]|]. unfold G_ALLOW_CUST. lia. }
  destruct (af_client_consts RT AF Σ2 m4 ART4) as (_ & SHC4 & _ & _ & UT4).
  pose proof (proj2 (af_acc_live RT AF Σ2 m4 G 16 ART4 ING)) as ACCG4.
  pose proof (uw_chain_agree outer m3 m4 sp s0 UWCm3 ltac:(apply AG4; intros x Hx; cbv beta in Hx; split; [left; unfold usp2, USTACK_TOP in *; lia | unfold G_ALLOW_CUST, RT_STACK, USTACK_TOP in *; repeat split; lia])) as UWCm4.
  (* [comment removed for export] *)
  pose proof (mtl_w2 sp gp v0 v1 v2 d1 d2 d3 d4 d5 d6 d7 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F4 fc4 m4 lo H G SK LK oldcb canary junk ra s0 s1 s2 s3 s4 s5 s6
                ONC4 (cl_env_ssp m4 _ canary UT4 CLE4) CBC4 FULL4 JR4 FRW4 TRET4 TREG4 GHI ltac:(clear - G16; Z.div_mod_to_equations; lia) ltac:(clear - GLO LOW; lia) GC4 ACCG4
                LKHI ltac:(clear - LK16; Z.div_mod_to_equations; lia) ltac:(clear - LKLO LOW; lia) LKC4 ltac:(clear - DJ_LG; lia) UT4 SHC4 FR4 ST4 HLOS HLO1 SPH MI4) as W2.
  fold usp usp1 usp2 in W2.
  cl_lift W2 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ2 _ _ c5 Hc5) as (ms5 & (e2 & e3 & e4 & e5 & m5 & -> & MU5 & WM5 & MI5 & FR5 & ST5 & SSP5 & ONC5 & CBC5 & LKC5 & GC5) & Hc5'). clear Hc5.
  fold usp in MU5, ST5, FR5. fold usp1 in ST5, FR5.
  assert (ART5 : ART RT Σ2 m5).
  { apply (af_frame RT AF Σ2 m4 m5 (usp - 224) ART4 ltac:(rewrite SP2, SP1; lia)); [| exact WM5].
    intros x Hx. apply MU5. cbn [outside]. repeat split; try exact I; intros Hin; apply Hx.
    - left. unfold USTACK_TOP in *. lia.
    - right; left. apply client_static_intro. lia.
    - right; left. apply client_static_intro. lia.
    - apply (acl_live _ _ _ LK 40); [exact INLK | lia]. }
  pose proof (cl_env_seg _ m4 m5 _ canary CLE4 MU5 ltac:(cl_fp_lia)) as CLE5.
  assert (AG45 : agree_on (fun x => usp <= x < USTACK_TOP) m4 m5) by (intros a Ha; apply MU5; cbn [outside]; cbv beta in Ha; repeat split; try exact I; unfold RT_STACK, USTACK_TOP in *; lia).
  pose proof (uw_chain_agree outer m4 m5 sp s0 UWCm4 AG45) as UWCm5.
  assert (OFF5 : forall P : Z -> Prop, (forall x, P x -> ~ (usp - 224 <= x < usp - 64) /\ ~ (TEV_ONCE <= x < TEV_ONCE + 4) /\ ~ (TP_A + -96 <= x < TP_A + -88) /\ ~ (LK + 4 <= x < LK + 8)) -> agree_on P m4 m5).
  { intros P HP a Ha. apply MU5. cbn [outside]. destruct (HP _ Ha) as (X1 & X2 & X3 & X4). repeat split; try exact I; lia. }
  assert (SKC5 : rw_cells asegs m5 SK (sk_cells (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 TEV_CMP) (Z_to_bv 64 TEV_FREE) (Z_to_bv 64 TEV_COPY))).
  { apply (rw_cells_agree asegs m4 m5 _ _ SKC4); [| exact WM5]. apply OFF5. cbn [cells_size csize Nat.add]. clear - SKLO LOW HSTK SKHI DJ_LS. unfold RT_STACK in *. intros; lia. }
  assert (KEEP5 : forall a cs, rw_cells asegs m4 a cs -> a + Z.of_nat (cells_size cs) <= 0xbc6000 -> (a + Z.of_nat (cells_size cs) <= TEV_ONCE \/ TEV_ONCE + 4 <= a) ->
            (a + Z.of_nat (cells_size cs) <= TP_A + -96 \/ TP_A + -88 <= a) -> rw_cells asegs m5 a cs).
  { intros a cs X H1 H2 H3. apply (rw_cells_agree asegs m4 m5 _ _ X); [| exact WM5]. apply OFF5. clear - H1 H2 H3 LKHI HLOS HLO1. intros; lia. }
  pose proof (KEEP5 _ _ DK4_4 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as DK4_5. pose proof (KEEP5 _ _ SLOT4 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as SLOT5.
  pose proof (KEEP5 _ _ UC4 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as UC5. pose proof (KEEP5 _ _ TRET4 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as TRET5.
  pose proof (KEEP5 _ _ TREG4 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as TREG5.
  assert (HC5 : rw_cells asegs m5 H [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_agree asegs m4 m5 _ _ HC4); [| exact WM5]. apply OFF5. cbn [cells_size csize Nat.add].
    pose proof (af_live_disj RT AF Σ2 m4 LK 40 H 8 [] ((SK, 56) :: (G, 16) :: rt_live RT Σ1) ART4 LV2 ltac:(right; right; exact INH)) as DJ. clear - HLO LOW HSTK HHI DJ. unfold RT_STACK in *. intros; lia. }
  assert (FRR5 : rw_cells asegs m5 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp1 + Z.of_nat (cells_size [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; unfold usp1; lia).
    exact (rw_cells_skip m5 usp1 [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR5). }
  rewrite <- CG2 in CGH. rewrite <- CG1, <- CG2 in CTX.
  destruct (cl_chain_call (rt_cg RT Σ2) e_mtl e_sk_push SITE_mtl_push m5 m5 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH _ ltac:(right; left; reflexivity)) (proj2 CGH _ ltac:(right; left; reflexivity)) UWCm5 ltac:(intros a _; reflexivity) FRR5 ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTX5 & UWC5).
  (* [comment removed for export] *)
  apply (sk_push_first_cps RT GOBJ AF AFP C_CALLOC Σ2 PMc (Z_to_bv 64 SITE_mtl_push) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) v0 v1 v2 sp (Z_to_bv 64 H) (Z_to_bv 64 SK) (Z_to_bv 64 H) e2 e3 e4 e5 d6 d7
           (Z_to_bv 64 DTOR_KEY) (Z_to_bv 64 (G + 8)) (Z_to_bv 64 G) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.shiftr (G + 8) 3 + SHB)) s7 s8 s9 s10 s11 v3 v4 v5 v6 F4 fc4 m5 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary SK
           (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 TEV_CMP) (Z_to_bv 64 TEV_FREE) (Z_to_bv 64 TEV_COPY) FDO MST eq_refl eq_refl ART5 MI5).
  { fold usp in SPA. unfold call_ok. rewrite EU1. split; [exact ST5|]. split; [rewrite SP2, SP1; exact LOW|]. split; [unfold usp1, RT_STACK in *; lia|]. split; [unfold usp1, USTACK_TOP in *; lia|].
    unfold usp1. clear - SPA. Z.div_mod_to_equations. lia. }
  { rewrite EU1. unfold usp1, RT_STACK in *. clear - HSTK. lia. }
  { rewrite (unsigned_lit SITE_mtl_push) by (unfold SITE_mtl_push; lia). exact CTX5. }
  { exact UWC5. }
  { rewrite (unsigned_lit SITE_mtl_push) by (unfold SITE_mtl_push; lia). apply (proj2 CGH). cbn [MTL_CALLS In app]. tauto. }
  { apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { rewrite LV2, LV1. cbn [length]. lia. } { rewrite CR2, CR1. lia. } { exact CLE5. }
  { exact INSK. } { clear - SK16. Z.div_mod_to_equations. lia. } { exact SKC5. }
  { exact Hc5'. }
  clear Hc5'. intros c6 (Σ3 & D & Hc6 & LV3 & FRS3 & SP3 & CR3 & D0 & D16 & DU & CG3).
  destruct (ASTA_unpack RT Σ3 _ _ c6 Hc6) as (ms6 & (m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & CLE6 & SKC6 & DC6) & Hc6'). clear Hc6.
  destruct RS6 as (w0 & w1 & w2 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & w3 & w4 & w5 & w6 & F6 & fc6 & ->).
  rewrite EU1 in ST6, PRES6. rewrite (ret_pc_even SITE_mtl_push) in Hc6' by (unfold SITE_mtl_push; lia).
  pose proof (af_live_disj RT AF Σ3 m6 D 32 LK 40 [] (rt_live RT Σ2) ART6 LV3 INLK) as DJ_DL.
  assert (INLK3 : In (LK, 40) (rt_live RT Σ3)) by (rewrite LV3; right; exact INLK). assert (ING3 : In (G, 16) (rt_live RT Σ3)) by (rewrite LV3; right; exact ING).
  assert (AG6 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ2) (rt_frames RT Σ2) usp1 x /\ x <> G_ALLOW_CUST /\ ~ (SK <= x < SK + 56)) -> agree_on P m5 m6).
  { intros P HP a Ha. destruct (HP _ Ha) as (X1 & X2 & X3). apply PRES6; [exact X1|]. unfold G_ALLOW_CUST in *. cbn [outside]. repeat split; try exact I; lia. }
  eassert (FR6 : rw_cells asegs m6 usp1 _).
  { apply (rw_cells_agree asegs m5 m6 _ _ FR5); [| exact WM6]. apply AG6. cbn [cells_size csize Nat.add]. intros x Hx. split; [left; unfold usp1, USTACK_TOP in *; lia|]. unfold G_ALLOW_CUST, usp1 in *. clear - Hx SKLO LOW HSTK SKHI. unfold RT_STACK in *. lia. }
  assert (LKC6 : rw_cells asegs m6 LK (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 16))).
  { apply (rw_cells_agree asegs m5 m6 _ _ LKC5); [| exact WM6]. apply AG6. cbn [cells_size csize Nat.add mutex_cells]. intros x Hx. split; [apply (acl_live _ _ _ LK 40); [exact INLK | lia]|]. unfold G_ALLOW_CUST. clear - Hx LKHI DJ_LS. lia. }
  assert (GC6 : rw_cells asegs m6 (G + 8) [C8 (Z_to_bv 64 LK)]).
  { pose proof (rw_cells_skip m5 G [C8 (Z_to_bv 64 SK)] [C8 (Z_to_bv 64 LK)] GC5) as X. cbn [cells_size csize Nat.add] in X.
    apply (rw_cells_agree asegs m5 m6 _ _ X); [| exact WM6]. apply AG6. cbn [cells_size csize Nat.add]. intros x Hx. split; [apply (acl_live _ _ _ G 16); [exact ING | lia]|]. unfold G_ALLOW_CUST. clear - Hx GHI DJ_SG. lia. }
  destruct (af_client_consts RT AF Σ3 m6 ART6) as (_ & SHC6 & _ & _ & UT6).
  pose proof (proj2 (af_acc_live RT AF Σ3 m6 G 16 ART6 ING3)) as ACCG6.
  (* [comment removed for export] *)
  pose proof (mtl_w3 sp gp w0 w1 w2 f1 f2 f3 f4 f5 f6 f7 s7 s8 s9 s10 s11 w3 w4 w5 w6 F6 fc6 m6 lo H G LK ra s0 s1 s2 s3 s4 s5 s6
                GHI ltac:(clear - G16; Z.div_mod_to_equations; lia) ltac:(clear - GLO LOW; lia) ACCG6 LKHI ltac:(clear - LK16; Z.div_mod_to_equations; lia) ltac:(clear - LKLO LOW; lia) LKC6 GC6
                UT6 SHC6 FR6 ST6 HLOS HLO1 SPH MI6) as W3.
  fold usp usp1 in W3.
  cl_lift W3 Hc6' c7 Hc7.
  destruct (ASTA_unpack RT Σ3 _ _ c7 Hc7) as (ms7 & (g1 & g2 & g3 & m7 & -> & MU7 & WM7 & MI7 & ST7 & LKC7) & Hc7'). clear Hc7. fold usp in MU7, ST7.
  assert (ART7 : ART RT Σ3 m7).
  { apply (af_frame RT AF Σ3 m6 m7 (usp - 176) ART6 ltac:(rewrite SP3, SP2, SP1; lia)); [| exact WM7].
    intros x Hx. apply MU7. cbn [outside]. repeat split; try exact I; intros Hin; apply Hx; [left; unfold USTACK_TOP in *; lia | apply (acl_live _ _ _ LK 40); [exact INLK3 | lia]]. }
  pose proof (cl_env_seg _ m6 m7 _ canary CLE6 MU7 ltac:(cl_fp_lia)) as CLE7.
  assert (OFF7 : forall P : Z -> Prop, (forall x, P x -> ~ (usp - 176 <= x < usp - 64) /\ ~ (LK + 4 <= x < LK + 8)) -> agree_on P m6 m7).
  { intros P HP a Ha. apply MU7. cbn [outside]. destruct (HP _ Ha) as (X1 & X2). repeat split; try exact I; lia. }
  (* [comment removed for export] *)
  pose proof (af_live_range RT AF Σ3 m6 D 32 ART6 ltac:(rewrite LV3; left; reflexivity)) as (_ & DLO & _). rewrite SP3, SP2, SP1 in DLO.
  pose proof (afp_live_hi RT GOBJ AFP Σ3 m6 D 32 ART6 ltac:(rewrite LV3; left; reflexivity) ltac:(lia)) as DHI.
  apply Hk. exists Σ3, H, G, SK, LK, D, u'.
  split.
  2:{ split; [rewrite LV3, LV2, LV1; reflexivity|]. split; [rewrite FRS3, FRS2; exact FRS1|]. split; [rewrite SP3, SP2; exact SP1|]. split; [rewrite CR3, CR2, CR1; lia|].
      split; [rewrite CG3, CG2; exact CG1|].
      repeat (apply Forall_cons; [cbn [fst snd]; split; [lia|]; split; [assumption | lia] |]). apply Forall_nil. }
  apply (ASTA_conseq RT Σ3 PMc _ _ c7 Hc7'). intros ms7 <-. exists m7.
  split; [exists w0, w1, w2, g1, g2, g3, f4, f5, f6, f7, w3, w4, w5, w6, F6, fc6; reflexivity|].
  split; [split; [exact ART7|]; split; [exact MI7|]; split; [exact (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 (wmono_trans asegs _ _ _ WM3 (wmono_trans asegs _ _ _ WM4 (wmono_trans asegs _ _ _ WM5 (wmono_trans asegs _ _ _ WM6 WM7)))))) | exact ST7]|].
  assert (NAP : forall p n x, In (p, n) [(D, 32); (LK, 40); (SK, 56); (G, 16); (H, 8)] -> 0 <= n -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x -> ~ (p <= x < p + n)).
  { intros p n x Hin Hn Hx. exact (wg_newchunk_apart RT AF Σ Σ3 m7 [(D, 32); (LK, 40); (SK, 56); (G, 16); (H, 8)] p n usp x ART7 ltac:(rewrite LV3, LV2, LV1; reflexivity) Hin
             ltac:(rewrite FRS3, FRS2; exact FRS1) ltac:(rewrite SP3, SP2; exact SP1) ltac:(lia) Hn Hx). }
  assert (ACL1 : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) usp x -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp2 x).
  { intros x Hx. apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e He; rewrite LV1; right; exact He | rewrite FRS1; intros e He; exact He | unfold usp2; lia]. }
  assert (ACL2 : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) usp x -> aclient (rt_live RT Σ2) (rt_frames RT Σ2) usp1 x).
  { intros x Hx. apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e He; rewrite LV2, LV1; do 4 right; exact He | rewrite FRS2, FRS1; intros e He; exact He | unfold usp1; lia]. }
  split.
  { intros a Ha Ho. pose proof (cl_split RT AF Σ m usp 752 _ ART0 ltac:(lia) ltac:(lia) Ha) as SPL. cbn [outside] in Ho. destruct Ho as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & _).
    pose proof (NAP D 32 _ ltac:(left; reflexivity) ltac:(lia) Ha) as ND. pose proof (NAP LK 40 _ ltac:(right; left; reflexivity) ltac:(lia) Ha) as NL.
    pose proof (NAP SK 56 _ ltac:(do 2 right; left; reflexivity) ltac:(lia) Ha) as NS. pose proof (NAP G 16 _ ltac:(do 3 right; left; reflexivity) ltac:(lia) Ha) as NG.
    pose proof (NAP H 8 _ ltac:(do 4 right; left; reflexivity) ltac:(lia) Ha) as NH.
    rewrite (MU7 a ltac:(cbn [outside]; repeat split; try exact I; lia)).
    rewrite (PRES6 a (ACL2 _ Ha) ltac:(cbn [outside]; repeat split; try exact I; lia)).
    rewrite (MU5 a ltac:(cbn [outside]; repeat split; try exact I; lia)).
    rewrite (PRES4 a (ACL1 _ Ha) ltac:(cbn [outside]; repeat split; try exact I; lia)).
    rewrite (MU3 a ltac:(cbn [outside]; unfold usp in *; repeat split; try exact I; lia)).
    rewrite (PRES2 a ltac:(apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He | intros e He; exact He | unfold usp1; lia]) ltac:(cbn [outside]; split; [lia | exact I])).
    apply PR1; [exact Ha | exact I]. }
  split; [exact CLE7|].
  assert (KEEP7 : forall a cs, rw_cells asegs m5 a cs -> a + Z.of_nat (cells_size cs) <= 0xbc6000 -> 0xb8f190 <= a ->
            (0x5a9d08 <= a /\ a + Z.of_nat (cells_size cs) <= 0x6694d8) \/ (0xb8f190 <= a /\ a + Z.of_nat (cells_size cs) <= 0xba3e98 /\ (a + Z.of_nat (cells_size cs) <= 0xb9f7c0 \/ 0xb9f7c1 <= a))
            \/ (0xbc52a0 <= a /\ a + Z.of_nat (cells_size cs) <= 0xbc57d0) -> rw_cells asegs m7 a cs).
  { intros a cs X H1 H2 H3. apply (rw_cells_agree asegs m5 m7 _ _ X); [| exact (wmono_trans asegs _ _ _ WM6 WM7)]. intros x Hx. cbv beta in Hx.
    rewrite (OFF7 (fun y => y = bv_unsigned x) ltac:(intros y ->; clear - Hx H1 H2 LKHI HLOS HLO1; split; lia) x eq_refl).
    rewrite (AG6 (fun y => y = bv_unsigned x) ltac:(intros y ->; clear - Hx H1 H2 H3 SKHI; split; [right; left; apply client_static_intro; destruct H3 as [H3|[H3|H3]]; lia|]; unfold G_ALLOW_CUST; split; lia) x eq_refl). reflexivity. }
  split; [exact (KEEP7 _ _ SLOT5 ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia))|]. split; [exact (KEEP7 _ _ UC5 ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia))|].
  split; [exact (KEEP7 _ _ ONC5 ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia))|]. split; [exact (KEEP7 _ _ TRET5 ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia))|].
  split; [exact (KEEP7 _ _ TREG5 ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia))|]. split; [exact (KEEP7 _ _ CBC5 ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia))|].
  assert (BLK7 : forall a cs p n, rw_cells asegs m5 a cs -> In (p, n) (rt_live RT Σ2) -> p <= a -> a + Z.of_nat (cells_size cs) <= p + n -> 0x10007fff8000 <= p ->
            (p + n <= SK \/ SK + 56 <= p) -> (p + n <= LK \/ LK + 40 <= p) -> p + n <= usp - 224 -> rw_cells asegs m7 a cs).
  { intros a cs p n X Hin H1 H2 H3 H4 H5 H6. apply (rw_cells_agree asegs m5 m7 _ _ X); [| exact (wmono_trans asegs _ _ _ WM6 WM7)]. intros x Hx. cbv beta in Hx.
    rewrite (OFF7 (fun y => y = bv_unsigned x) ltac:(intros y ->; clear - Hx H1 H2 H5 H6; split; lia) x eq_refl).
    rewrite (AG6 (fun y => y = bv_unsigned x) ltac:(intros y ->; split; [apply (acl_live _ _ _ p n); [exact Hin | lia]|]; unfold G_ALLOW_CUST; clear - Hx H1 H2 H3 H4; split; lia) x eq_refl). reflexivity. }
  assert (HFAR : H + 8 <= usp - 224) by (clear - HLO LOW HLO1; lia). assert (GFAR : G + 16 <= usp - 224) by (clear - GLO LOW HLO1; lia).
  pose proof (af_live_disj RT AF Σ2 m4 SK 56 H 8 [(LK, 40)] ((G, 16) :: rt_live RT Σ1) ART4 LV2 ltac:(right; right; exact INH)) as DJ_SH.
  pose proof (af_live_disj RT AF Σ2 m4 LK 40 H 8 [] ((SK, 56) :: (G, 16) :: rt_live RT Σ1) ART4 LV2 ltac:(right; right; exact INH)) as DJ_LH.
  split; [exact (BLK7 _ _ H 8 HC5 INH2 ltac:(lia) ltac:(cbn; lia) HHI ltac:(clear - DJ_SH; lia) ltac:(clear - DJ_LH; lia) HFAR)|].
  split; [exact (BLK7 _ _ G 16 GC5 ING ltac:(lia) ltac:(cbn; lia) GHI ltac:(clear - DJ_SG; lia) ltac:(clear - DJ_LG; lia) GFAR)|].
  split. { apply (rw_cells_agree asegs m6 m7 _ _ SKC6); [| exact WM7]. apply OFF7. cbn [cells_size csize Nat.add sk_cells]. clear - SKLO LOW HLO1 SKHI DJ_LS. intros; lia. }
  split; [exact LKC7|].
  apply (rw_cells_agree asegs m6 m7 _ _ DC6); [| exact WM7]. apply OFF7. cbn [cells_size csize Nat.add]. clear - DLO LOW HLO1 DHI DJ_DL. intros; lia.
Qed.
End CMtl.
