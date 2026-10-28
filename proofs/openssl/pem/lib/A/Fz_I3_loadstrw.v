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
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import LhPure LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout PLayout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_mkit Fz_G_kit Fz_ckit Fz_env Fz_M_malloc Fz_W5_icb Th_errno Th_tsd Th_key Th_once Th_mutex Fz_T_once Fz_T_lock Fz_T_local Fz_T_master1 Fz_T_sa Fz_T_sa_set Fz_T_master Fz_T_slx Fz_I1_img Fz_I1_hash Fz_I1_defs Fz_I1_loadw Fz_I1_errload Fz_I1_efirst Fz_I1_crypto Fz_I3_shelve.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation zeros n := (repeat (Z_to_bv 8 0) n) (only parsing).
Notation TP_A := (0xba3ef0)%Z (only parsing).
Notation ERRNO_A := (0xba3e4c)%Z (only parsing).
Notation MK_ONCE := (0xb9f500)%Z (only parsing).
Notation MK_KEY := (0xb9f520)%Z (only parsing).
Notation MK_INIT := (0xb9f540)%Z (only parsing).
Notation MK_CLEAN := (0x1f69dc)%Z (only parsing).

Definition e_loadstr : Z := 0x1f3bdc.
Definition SITE_ls_sm : Z := 0x1f3c30.          (* [comment removed for export] *)
Definition SITE_ls_shv : Z := 0x1f3cc4.         (* [comment removed for export] *)
Definition SITE_ls_crs : Z := 0x1f3cd0.         (* [comment removed for export] *)
Definition SITE_ls_ush : Z := 0x1f3ce0.         (* [comment removed for export] *)
Definition LS_EXIT : Z := 0x1f3ce8.             (* [comment removed for export] *)
Definition LS_RELEASE : Z := 0x1f3d2c.          (* [comment removed for export] *)
Definition G_LS_RET : Z := 0xb9f320.            (* [comment removed for export] *)
Definition LS_MAGIC : Z := 0x41b58ab3.
Definition LS_RETIRED : Z := 0x45e0360e.
Definition LS_DESCR : Z := 0x42528.             (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ls_w0_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo pad : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a1' : word) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_ls_sm) (Z_to_bv 64 (bv_unsigned sp + -64 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -64 - pad))
                 (Z_to_bv 64 64) a1' a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 0x7fff8000) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (e_stack_malloc 0)) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [C8 (Z_to_bv 64 0); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk asegs m' (bv_unsigned sp + -64 - pad) (bv_unsigned sp + -64)
    /\ stk asegs m' lo (bv_unsigned sp + -64 - pad).

Lemma ls_w0 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo pad : Z),
  (pad = 0 \/ pad = 16) -> bv_unsigned sp mod 32 = pad ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 80 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  ro_cells asegs m g_detect_stack_use_after_return [C4 (Z_to_bv 64 1)] -> mem_inv asegs m ->
  evt asegs (ls_w0_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo pad m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_loadstr) fc None m (seg_rom asegs)).
Proof.
  intros until pad. intros HP HPM ST HLO HLOS SPH UT SHC UAR MI. unfold e_loadstr, g_shadow_memory_dynamic_address, g_detect_stack_use_after_return in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 64, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 64, SP)]) by ut_fp_lia.
  carve_frame 64%nat ST.
  zstep. zstep; lfix. do 8 zstep. zstep.
  rewrite (land_m32_pad (SP + -64) pad) by (first [lia | replace (SP + -64) with (SP + (-2) * 32) by lia; rewrite Z.mod_add by lia; exact HPM]).
  zstep. zstep.
  do 2 zstep. zstep. zstep. zstep. zstep. if_false. do 2 zstep.
  destruct (stk_split asegs _ lo (SP + -64 - pad) (SP + -64) ST ltac:(lia)) as [ST1 GAP].
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold ls_w0_post, SITE_ls_sm, e_stack_malloc. apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [eassumption|]. split; [exact GAP| exact ST1].
Qed.
(* [comment removed for export] *)
Definition ls_w1_post (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' s3' s4' s5' : word) (f lo pad : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (j8 fr : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_ls_shv) (Z_to_bv 64 (bv_unsigned sp + -64 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -64 - pad))
                 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 LS_DESCR) (Z_to_bv 64 e_loadstr) a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
                 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_shelve) fc None m' (seg_rom asegs)
    /\ munch [(f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (bv_unsigned sp - 80, bv_unsigned sp - 56)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [CB 8 j8; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0]
    /\ rw_cells asegs m' f [C8 (Z_to_bv 64 LS_MAGIC); C8 (Z_to_bv 64 LS_DESCR); C8 (Z_to_bv 64 e_loadstr); CB 32 fr]
    /\ rw_cells asegs m' (f / 8 + 2147450880) [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))]
    /\ stk asegs m' (bv_unsigned sp + -64 - pad) (bv_unsigned sp + -64)
    /\ stk asegs m' lo (bv_unsigned sp + -64 - pad).

Lemma ls_w1 : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (ra0 s0' s1' s2' s3' s4' s5' : word) (F : bvmap 5 word) fc (m : mem) (f lo pad : Z) (fj sj : list byte),
  (pad = 0 \/ pad = 16) -> 0 < f -> f mod 64 = 0 -> 0xbc6000 <= f -> f + 64 <= lo -> (f + 64 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  lo <= bv_unsigned sp - 96 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 (Z_to_bv 64 0); C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0] ->
  stk asegs m (bv_unsigned sp + -64 - pad) (bv_unsigned sp + -64) -> stk asegs m lo (bv_unsigned sp + -64 - pad) ->
  rw_cells asegs m f [CB 56 fj] -> rw_cells asegs m (f / 8 + 2147450880) [CB 8 sj] ->
  mem_inv asegs m ->
  evt asegs (ls_w1_post sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ra0 s0' s1' s2' s3' s4' s5' f lo pad m)
    (MS (mkR (Z_to_bv 64 SITE_ls_sm) (Z_to_bv 64 (bv_unsigned sp + -64 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -64 - pad))
             (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 0x7fff8000) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_ls_sm) fc None m (seg_rom asegs)).
Proof.
  intros until sj. intros HP F0 F64 FIMG FLO FSH HLO HLOS SPH UT FR GAP ST FB SB MI.
  unfold SITE_ls_sm in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (SP - 80, SP - 56)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 8 <= 0x10007fff8000).
  { pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)). assert (f / 8 + 8 <= 2^44) by (Z.div_mod_to_equations; lia). lia. }
  assert (HWU : ut_fp [(f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (SP - 80, SP - 56)]) by (clear - F0 FIMG SHR HLO HLOS SPH FLO; ut_fp_lia).
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  pose proof (div8_facts f) as Q1.
  zstep. zstep. zstep. zstep. if_true.
  (* [comment removed for export] *)
  destruct HP as [-> | ->].
  1: replace (SP + -64 - 0) with (SP + -64) in * by lia.
  2: replace (SP + -64 - 16) with (SP + -80) in * by lia.
  2: th_frame 16%nat [8; 8]%nat GAP.
  all: zstep.
  all: zstep. all: zstep. all: zstep. all: (zstep; rewrite (shr3_div f) by lia). all: zstep. all: zstep. all: zstep. all: zstep. all: zstep.
  all: (zstep; lfix); (zstep; lfix); (zstep; lfix).
  all: zstep; (zstep; lfix); (zstep; lfix); (zstep; lfix); (zstep; lfix).
  all: zstep; (zstep; lfix); (zstep; lfix); (zstep; lfix); (zstep; lfix).
  all: zstep; zstep.
  1: pose proof (rw_cells_blur _ _ [_] _ FR) as FRB.
  2: pose proof (rw_cells_blur _ _ [_] _ FR) as FRB; th_release FR0 (SP + -64).
  all: cbn [cells_size csize Nat.add app cells_bytes cbytes] in FRB.
  all: subst SP; rewrite ?Z_to_bv_bv_unsigned.
  all: unfold ls_w1_post, SITE_ls_shv, e_shelve, LS_MAGIC, LS_DESCR, e_loadstr.
  all: try replace (bv_unsigned sp + -64 - 0) with (bv_unsigned sp + -64) by lia.
  all: try replace (bv_unsigned sp + -64 - 16) with (bv_unsigned sp + -80) by lia.
  all: apply evt_done; do 3 eexists; split; [reflexivity|].
  all: split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [exact FRB|]; split; [eassumption|]; split; [eassumption|]; split; assumption.
Qed.
(* [comment removed for export] *)
Lemma ls_w2 : forall sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists ra', ms = MS (mkR ra' sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 e_crypto_strs) fc None m (seg_rom asegs) /\ bv_unsigned ra' = SITE_ls_crs)
    (MS (mkR (Z_to_bv 64 SITE_ls_shv) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_ls_shv) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO0 LO HTOP MI. unfold SITE_ls_shv, SITE_ls_crs, e_crypto_strs in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  zstep. th_if_lit.
  zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity| apply unsigned_lit; lia].
Qed.
(* [comment removed for export] *)
Lemma ls_w3 : forall sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (lo res : Z),
  0 <= res -> res + 8 <= 2 ^ 64 -> rw_cells asegs m res [C8 z64] ->
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (eq (MS (mkR (Z_to_bv 64 SITE_ls_ush) sp gp tp t0 t1 t2 s0 s1 z64 z64 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 1) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 e_unshelve) fc None m (seg_rom asegs)))
    (MS (mkR (Z_to_bv 64 SITE_ls_crs) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 res) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_ls_crs) fc None m (seg_rom asegs)).
Proof.
  intros until res. intros R0 RHI RES ST LO0 LO HTOP MI. unfold SITE_ls_crs, SITE_ls_ush, e_unshelve in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUr : bv_unsigned (Z_to_bv 64 res) = res) by (apply unsigned_lit; lia).
  zstep. do 2 zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.
(* [comment removed for export] *)
Definition ls_wxa_post (rax sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 s6 s7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (f pad : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists m' : mem,
    ms = MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -64 - pad))
                 (Z_to_bv 64 (-11)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 1) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
                 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 LS_RELEASE) fc None m' (seg_rom asegs)
    /\ munch [(f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (G_LS_RET, G_LS_RET + 4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' G_LS_RET [C4 (Z_to_bv 64 1)].

Lemma ls_wxa : forall sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (rax : word) (f lo pad : Z) (x0 r0 : word)
    (b0 b1 b2 b3 b4 b5 b6 b7 : byte),
  0 < f -> f mod 64 = 0 -> 0xbc6000 <= f -> f + 64 <= lo -> (f + 64 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  rw_cells asegs m f [C8 x0] -> rw_cells asegs m (f / 8 + 2147450880) [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7] -> img_untouched m ->
  rw_cells asegs m G_LS_RET [C4 r0] ->
  stk asegs m lo (bv_unsigned sp + -64 - pad) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 96 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (ls_wxa_post rax sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 s6 s7 t3 t4 t5 t6 F fc f pad m)
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -64 - pad))
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 1) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
             s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (ret_pc (Z_to_bv 64 SITE_ls_ush)) fc None m (seg_rom asegs)).
Proof.
  intros until b7. intros F0 F64 FIMG FLO FSH FB SB UT RC ST LO0 LO HTOP MI. unfold SITE_ls_ush, G_LS_RET in *.
  rewrite (ret_pc_even 0x1f3ce0) by lia.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  pose proof (munch_refl [(f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (0xb9f320, 0xb9f320 + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 8 <= 0x10007fff8000).
  { pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)). assert (f / 8 + 8 <= 2^44) by (Z.div_mod_to_equations; lia). lia. }
  assert (HWU : ut_fp [(f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (0xb9f320, 0xb9f320 + 4)]) by (clear - F0 FIMG SHR FLO LO0; ut_fp_lia).
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  pose proof (div8_facts f) as Q1.
  zstep. zstep. (zstep; lfix). zstep. (zstep; lfix). zstep. zstep. (zstep; lfix).
  zstep. ifF. zstep. do 8 (zstep; lfix).
  apply evt_done. unfold ls_wxa_post, LS_RELEASE. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
Definition ls_wxb_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 a1 a2 a3 a4 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32)
    (fl lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 fl) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(fl, fl + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' fl [C1 (Z_to_bv 8 0)].

Lemma ls_wxb : forall sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (rax ra0 s0' s1' s2' s3' s4' s5' : word) (F : bvmap 5 word) fc (m : mem) (f fl lo pad : Z) (j8 : list byte),
  (pad = 0 \/ pad = 16) -> lo <= bv_unsigned sp - 96 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  0 < f -> f + 64 <= lo -> 0 < fl -> fl + 1 <= lo ->
  stk asegs m lo (bv_unsigned sp + -64 - pad) -> stk asegs m (bv_unsigned sp + -64 - pad) (bv_unsigned sp + -64) ->
  rw_cells asegs m (bv_unsigned sp + -64) [CB 8 j8; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0] ->
  ro_cells asegs m (f + 56) [C8 (Z_to_bv 64 fl)] -> rw_cells asegs m fl [C1 (Z_to_bv 8 1)] -> mem_inv asegs m ->
  evt asegs (ls_wxb_post ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 a1 a2 a3 a4 a5 a6 a7 F fc fl lo m)
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -64 - pad))
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) s3 s4 (Z_to_bv 64 f) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 LS_RELEASE) fc None m (seg_rom asegs)).
Proof.
  intros until j8. intros HP HLO HLOS SPH F0 FLO FL0 FLLO ST1 GAP FR FLG FLB MI. unfold LS_RELEASE in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EUfl : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply unsigned_lit; lia).
  zstep. clear FLG.
  zstep; lfix.
  zstep. zstep.
  do 7 zstep.
  pose proof (stk_merge asegs _ lo (SP + -64 - pad) (SP + -64) ST1 GAP ltac:(lia)) as ST2.
  zstep. release_frame FR ST2 SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold ls_wxb_post. apply evt_done. do 8 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption| assumption].
Qed.
