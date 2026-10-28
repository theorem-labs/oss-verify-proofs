(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout Th_mutex Th_mutex_init I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_M_malloc Fz_M_zalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition e_lock_new : Z := 0x1f5e3c.
Definition SITE_ln_smalloc : Z := 0x1f5e98.
Definition SITE_ln_zalloc : Z := 0x1f5f38.

(* [comment removed for export] *)
Definition locknew_s0_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo pad : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a1' : word) (j : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_ln_smalloc) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
                 (Z_to_bv 64 64) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (e_stack_malloc 0)) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -96) [CB 24 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk asegs m' (bv_unsigned sp + -96 - pad) (bv_unsigned sp + -96)
    /\ stk asegs m' lo (bv_unsigned sp + -96 - pad).

Lemma locknew_s0_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo pad : Z),
  (pad = 0 \/ pad = 16) -> bv_unsigned sp mod 32 = pad ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 112 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  ro_cells asegs m g_detect_stack_use_after_return [C4 (Z_to_bv 64 1)] -> mem_inv asegs m ->
  evt asegs (locknew_s0_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo pad m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_lock_new) fc None m (seg_rom asegs)).
Proof.
  intros until pad. intros HP HPM ST HLO HLOS SPH UT SHC UAR MI. unfold e_lock_new, g_shadow_memory_dynamic_address, g_detect_stack_use_after_return in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 96, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 96, SP)]) by ut_fp_lia.
  carve_frame 96%nat ST.
  zstep. zstep; lfix. do 10 zstep. zstep.
  rewrite (land_m32_pad (SP + -96) pad) by (first [lia | replace (SP + -96) with (SP + (-3) * 32) by lia; rewrite Z.mod_add by lia; exact HPM]).
  do 3 zstep. zstep. zstep. zstep. zstep. zstep. if_false. do 2 zstep.
  destruct (stk_split asegs _ lo (SP + -96 - pad) (SP + -96) ST ltac:(lia)) as [ST1 GAP].
  lazymatch goal with FRH : rw_cells asegs ?mm (SP + -96) (?c1 :: ?c2 :: ?rest) |- _ =>
    pose proof (rw_cells_blur mm (SP + -96) [c1; c2] rest FRH) as FRB end.
  cbn [cells_size csize Nat.add] in FRB.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold locknew_s0_post, SITE_ln_smalloc, e_stack_malloc. apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact FRB|]. split; [exact GAP| exact ST1].
Qed.

(* [comment removed for export] *)
Definition LN_MAGIC : Z := 0x41b58ab3.
Definition LN_DESCR : Z := 0x30a96.
Definition LN_PC : Z := 0x1f5e3c.
Definition ln_shadow : list cell :=
  [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))].

Definition locknew_s1_post (sp gp tp t0 t1 t2 s3 s4 s5 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' : word) (F : bvmap 5 word) (fc : bv 32)
    (f lo pad : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a3' : word) (j fr : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_ln_zalloc) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
                 (Z_to_bv 64 40) (Z_to_bv 64 0x491e0) (Z_to_bv 64 919) a3' a4 a5 a6 a7 (Z_to_bv 64 f) s3 s4 s5 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
                 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_CRYPTO_zalloc) fc None m' (seg_rom asegs)
    /\ munch [(f, f + 56); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -96) [CB 24 j; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0]
    /\ rw_cells asegs m' f [C8 (Z_to_bv 64 LN_MAGIC); C8 (Z_to_bv 64 LN_DESCR); C8 (Z_to_bv 64 LN_PC); CB 32 fr]
    /\ rw_cells asegs m' (f / 8 + 2147450880) ln_shadow.

Lemma locknew_s1_walk : forall ra0 sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (s0' s1' s2' s3' s4' s5' s6' s7' : word) (F : bvmap 5 word) fc (m : mem) (f lo pad : Z) (j fj sj : list byte),
  (pad = 0 \/ pad = 16) -> 0 < f -> f + 64 <= 2^47 ->
  (f + 56 <= 0x10000 \/ 0xbc6000 <= f) -> (f + 64 <= 0x7fff8000 \/ 0x10007fff8000 <= f) -> 0x10007fff8000 <= bv_unsigned sp - 112 -> bv_unsigned sp <= 2^47 ->
  (f + 56 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= f) ->
  img_untouched m ->
  rw_cells asegs m (bv_unsigned sp + -96) [CB 24 j; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0] ->
  rw_cells asegs m f [CB 56 fj] -> rw_cells asegs m (f / 8 + 2147450880) [CB 8 sj] -> mem_inv asegs m ->
  evt asegs (locknew_s1_post sp gp tp t0 t1 t2 s3 s4 s5 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 ra0 s0' s1' s2' s3' s4' s5' s6' s7' F fc f lo pad m)
    (MS (mkR (Z_to_bv 64 SITE_ln_smalloc) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
             (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_ln_smalloc) fc None m (seg_rom asegs)).
Proof.
  intros until sj. intros HP F0 FH FIMG FSH SPL SPH FSEP UT FR FB SB MI. unfold SITE_ln_smalloc in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(f, f + 56); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (SP - 96, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 8 <= 0x10007fff8000).
  { pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)). assert (f / 8 + 8 <= 2^44) by (Z.div_mod_to_equations; lia). lia. }
  assert (HWU : ut_fp [(f, f + 56); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (SP - 96, SP)]) by ut_fp_lia.
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  pose proof (div8_facts f) as Q1.
  do 3 zstep. zstep. if_true.
  destruct HP as [-> | ->].
  1: replace (SP + -96 - 0) with (SP + -96) by lia.
  2: replace (SP + -96 - 16) with (SP + -112) by lia.
  all: zstep.
  all: do 4 zstep.
  all: rewrite (shr3_div f) by lia.
  all: do 4 zstep.
  all: zstep.
  all: zstep; lfix.
  all: zstep; lfix.
  all: zstep; lfix.
  all: zstep.
  all: zstep; lfix.
  all: zstep; lfix.
  all: zstep; lfix.
  all: zstep; lfix.
  all: zstep.
  all: zstep; lfix.
  all: zstep; lfix.
  all: zstep; lfix.
  all: zstep; lfix.
  all: do 4 zstep.
  all: zstep.
  1: replace (SP + -96) with (SP + -96 - 0) by lia.
  2: replace (SP + -112) with (SP + -96 - 16) by lia.
  all: pose proof (rw_cells_blur _ _ [_; _] _ FR) as FRB.
  all: cbn [cells_size csize Nat.add] in FRB.
  all: subst; rewrite ?Z_to_bv_bv_unsigned.
  all: unfold locknew_s1_post, SITE_ln_zalloc, e_CRYPTO_zalloc, ln_shadow, LN_MAGIC, LN_DESCR, LN_PC; apply evt_done; do 4 eexists; (split; [reflexivity|]).
  all: (split; [assumption|]); (split; [assumption|]); (split; [assumption|]); (split; [exact FRB|]); (split; [eassumption| eassumption]).
Qed.

(* [comment removed for export] *)
Definition LN_RETIRED : Z := 0x45e0360e.
Definition SITE_ln_release : Z := 0x1f5fc8.
Definition ln_shadow_f5 : list cell :=
  [C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11))].

Definition locknew_s2_post (sp gp tp s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (p f lo pad : Z) (canary : word) (m : mem) : machine_state -> Prop :=
  fun ms => exists (ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
                 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 p) s4 s5 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 SITE_ln_release) fc None m' (seg_rom asegs)
    /\ munch [(p, p + 40); (f, f + 8); (f + 32, f + 36); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (bv_unsigned sp - 176, bv_unsigned sp - 96 - pad)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + -96 - pad)
    /\ rw_cells asegs m' p (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
    /\ rw_cells asegs m' (f / 8 + 2147450880) ln_shadow_f5.

Lemma locknew_s2_walk : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p f lo pad : Z) (aj pj : list byte) (canary : word),
  (pad = 0 \/ pad = 16) ->
  lo <= bv_unsigned sp - 176 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  0x10007fff8000 <= p -> p + 40 <= lo ->
  0xbc6000 <= f -> f + 64 <= lo -> (f + 64 <= 0x7fff8000 \/ 0x10007fff8000 <= f) -> (p + 40 <= f \/ f + 64 <= p) ->
  stk asegs m lo (bv_unsigned sp + -96 - pad) ->
  rw_cells asegs m f [C8 (Z_to_bv 64 LN_MAGIC)] -> rw_cells asegs m (f + 32) [CB 4 aj] ->
  rw_cells asegs m (f / 8 + 2147450880) ln_shadow -> rw_cells asegs m p [CB 40 pj] -> ssp_cells m canary -> mem_inv asegs m ->
  evt asegs (locknew_s2_post sp gp tp s8 s9 s10 s11 F fc p f lo pad canary m)
    (MS (mkR (Z_to_bv 64 SITE_ln_zalloc) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
             (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) s3 s4 s5 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_ln_zalloc) fc None m (seg_rom asegs)).
Proof.
  intros until canary. intros HP HLO HLOS SPH PHI PLO FIMG FLO FSH PF ST1 HDR ATTR SB PB SSP MI.
  unfold SITE_ln_zalloc, ln_shadow, LN_MAGIC in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl [(p, p + 40); (f, f + 8); (f + 32, f + 36); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (SP - 176, SP - 96 - pad)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (div8_facts f) as Q1.
  destruct SSP as [SSG SSC]. unfold got_ssp, ssp_guard in SSG, SSC.
  assert (EUp : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUa : bv_unsigned (Z_to_bv 64 (f + 32)) = f + 32) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 (SP + -96 - pad)) = SP + -96 - pad) by (apply unsigned_lit; lia).
  zstep. if_false.
  do 3 zstep. zstep.
  pose proof mutexattr_init_proof as MAI. unfold mutexattr_init_stmt in MAI.
  call MAI; [rewrite EUa; exact ATTR| assumption|].
  rewrite EUa in *.
  rename POST into ATTR1.
  do 2 zstep. zstep.
  pose proof mutex_init_attr_proof as MIA. unfold mutex_init_attr_stmt in MIA.
  call MIA; [rewrite EUp; exact PB| rewrite EUa; exact ATTR1| rewrite EUa; lia| split; [exact SSG| exact SSC]
     | rewrite EUs; exact ST1| rewrite EUs; lia| rewrite EUp, EUs; left; lia| rewrite EUa, EUs; left; lia| rewrite EUp, EUa; lia
     | rewrite EUs; unfold got_ssp; left; lia| rewrite EUs; unfold ssp_guard; left; lia| rewrite EUp; unfold got_ssp; left; lia| rewrite EUp; unfold ssp_guard; left; lia
     | assumption|].
  clear SSG SSC PC1 ATTR1.
  rewrite EUp, EUs in *.
  lazymatch goal with H : rw_cells asegs _ p (mutex_cells _ _) |- _ => rename H into PBM end. unfold mutex_cells in PBM.
  lazymatch goal with H : stk asegs _ lo (SP + -96 - pad) |- _ => rename H into ST2 end.
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  do 2 zstep. zstep.
  eapply evt_cut; [apply mutexattr_destroy_proof|]. intros ms' ->.
  replace (ret_pc (Z_to_bv 64 2056048)) with (Z_to_bv 64 2056048) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  zstep. if_true.
  zstep. zstep; lfix.
  do 2 zstep. zstep; lfix.
  zstep. if_false.
  zstep.
  zstep; lfix. zstep; lfix. zstep; lfix. zstep; lfix. zstep; lfix. zstep; lfix. zstep; lfix. zstep; lfix.
  subst SP.
  unfold locknew_s2_post, SITE_ln_release, ln_shadow_f5, mutex_cells. apply evt_done. do 19 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact PBM| exact SB].
Qed.

(* [comment removed for export] *)
Definition locknew_s3_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (p fl lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(fl, fl + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' fl [C1 (Z_to_bv 8 0)].

Lemma locknew_s3_walk : forall ra1 ra0 sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (s0' s1' s2' s3' s4' s5' s6' s7' : word) (F : bvmap 5 word) fc (m : mem) (p f fl lo pad : Z) (j : list byte),
  (pad = 0 \/ pad = 16) -> lo <= bv_unsigned sp - 112 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  0 < f -> f + 64 <= lo -> 0 < fl -> fl + 1 <= lo ->
  stk asegs m lo (bv_unsigned sp + -96 - pad) -> stk asegs m (bv_unsigned sp + -96 - pad) (bv_unsigned sp + -96) ->
  rw_cells asegs m (bv_unsigned sp + -96) [CB 24 j; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0] ->
  ro_cells asegs m (f + 56) [C8 (Z_to_bv 64 fl)] -> rw_cells asegs m fl [C1 (Z_to_bv 8 1)] -> mem_inv asegs m ->
  evt asegs (locknew_s3_post ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 F fc p fl lo m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 p) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_ln_release) fc None m (seg_rom asegs)).
Proof.
  intros until j. intros HP HLO HLOS SPH F0 FLO FL0 FLLO ST1 GAP FR FLG FLB MI. unfold SITE_ln_release in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EUfl : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply unsigned_lit; lia).
  zstep. clear FLG.
  zstep; lfix.
  do 3 zstep.
  do 9 zstep.
  pose proof (stk_merge asegs _ lo (SP + -96 - pad) (SP + -96) ST1 GAP ltac:(lia)) as ST2.
  zstep.
  release_frame FR ST2 SP.
  zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold locknew_s3_post. apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption| assumption].
Qed.

Section CLockNew.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis SM0 : stack_malloc_contract RT 0.
Hypothesis C_CZ : crypto_zalloc_stmt RT.

Definition crypto_lock_new_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x200 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_lock_new (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) [(SITE_ln_zalloc, e_lock_new); (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)]
                      [(SITE_ln_zalloc, e_CRYPTO_zalloc); (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)] ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 1 <= rt_credit RT Σ ->
  ro_cells asegs m G_MALLOC_IMPL [C8 (Z_to_bv 64 e_CRYPTO_malloc)] -> ro_cells asegs m G_GOT_CMALLOC [C8 (Z_to_bv 64 e_CRYPTO_malloc)] ->
  rw_cells asegs m G_ALLOW_CUST [C1 lb] -> (lb = Z_to_bv 8 0 \/ lb = Z_to_bv 8 1) -> ssp_cells m canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_lock_new m)))
    (fun c => exists (Σ' : rts RT) (p : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
           /\ rw_cells asegs m' G_ALLOW_CUST [C1 (Z_to_bv 8 1)] /\ ssp_cells m' canary
           /\ rw_cells asegs m' p (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) /\ acc asegs m' p 40) c
       /\ rt_live RT Σ' = (p, 40) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - 1 /\ 0 < p /\ p mod 16 = 0 /\ p + 40 < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem crypto_lock_new_cps : crypto_lock_new_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary
    FDO MST -> ART0 MI0 CALL HSTK CTX UWC CGH Hfr Hlen Hcr MIMP GOT LAT HLB SSP.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  set (pad := usp mod 32).
  assert (HP : pad = 0 \/ pad = 16) by (unfold pad; clear - SPA; Z.div_mod_to_equations; lia).
  assert (HPM : usp mod 32 = pad) by reflexivity. clearbody pad.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 176 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLOI : SEGTOP_A <= lo) by (unfold SEGTOP_A, STACK_WIN in *; lia).
  set (usp1 := usp + -96 - pad).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & UAR & UT).
  (* [comment removed for export] *)
  pose proof (locknew_s0_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pad
                HP HPM ST ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia) UT SHC UAR MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (a1' & j & m1 & -> & MU1 & WM1 & MI1 & FR1 & GAP1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, GAP1, ST1, Hc1'. fold usp1 in GAP1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 96 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 96 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  (* [comment removed for export] *)
  apply (SM0 Σ PMc (Z_to_bv 64 SITE_ln_smalloc) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 64) a1' a2 a3 a4 a5 a6 a7
           s2 s3 s4 s5 (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo FDO MST ltac:(left; reflexivity) eq_refl Hfr Hcr ART1 MI1).
  { unfold call_ok. rewrite EU1. split; [exact ST1|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|].
    fold usp in SPA. clear - SPA HP HPM. Z.div_mod_to_equations. lia. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & f & Hc2 & FRS1 & LV1 & SP1 & CR1 & F0 & F64 & FU & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WF2 & WS2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_ln_smalloc) in Hc2' by (unfold SITE_ln_smalloc; lia).
  assert (INF : In (f, 0%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  pose proof (af_frames_range RT AF Σ1 m2 f 0%nat ART2 INF) as (_ & FLO & _ & _).
  pose proof (af_frames_align RT AF Σ1 m2 f 0%nat ART2 INF) as (_ & FIMG).
  pose proof (af_frames_hi RT AF Σ1 m2 f 0%nat ART2 INF) as FSH.
  rewrite SP1 in FLO. change (fs_size 0) with 64 in FLO, FSH, FU, WF2, WS2. change (64 - 8) with 56 in WF2. change (64 / 8) with 8 in WS2.
  unfold shad, SHB in WS2. unfold SEGTOP_A in FIMG.
  assert (AG2 : forall a k, usp1 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m1 m2).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES2. left. lia. }
  cl_keep FR1 AG2 WM2 FR2.
  destruct (wr_at_rw_CB m2 f 56 WF2 ltac:(lia)) as (fj & FB2). destruct (wr_at_rw_CB m2 (f / 8 + 2147450880) 8 WS2 ltac:(lia)) as (sj & SB2).
  change (Z.to_nat 56) with 56%nat in FB2. change (Z.to_nat 8) with 8%nat in SB2.
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & _ & _ & _ & UT2).
  (* [comment removed for export] *)
  pose proof (locknew_s1_walk ra sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s7 s8 s9 s10 s11 u3 u4 u5 u6
                s0 s1 s2 s3 s4 s5 s6 s7 F2 fc2 m2 f lo pad j fj sj HP F0 ltac:(unfold USTACK_TOP in *; lia) ltac:(right; exact FIMG)
                ltac:(destruct FSH; [left | right]; lia) ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(fold usp; unfold USTACK_TOP in *; lia)
                ltac:(left; fold usp; unfold RT_STACK in *; lia) UT2 FR2 FB2 SB2 MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (a3' & j3 & fr & m3 & -> & MU3 & WM3 & MI3 & FR3 & HDR3 & SB3) & Hc3'). clear Hc3.
  fold usp in MU3, FR3, Hc3'. fold usp1 in Hc3'.
  assert (SHF : shad (f + 64) = shad f + 8) by (replace (f + 64) with (f + 64 * 1) by lia; rewrite (shad_add64 f 1 F64); lia).
  assert (ART3 : ART RT Σ1 m3).
  { apply (af_frame RT AF Σ1 m2 m3 (usp - 96) ART2 ltac:(rewrite SP1; lia)); [| exact WM3].
    intros a Ha. apply MU3. cbn [outside]. split; [| split; [| split; [| exact I]]]; intros Hin; apply Ha.
    - apply (acl_frame _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; lia].
    - apply (acl_fshadow _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; rewrite SHF; unfold shad, SHB; lia].
    - apply acl_stack. unfold USTACK_TOP in *. lia. }
  assert (Q1 := div8_facts f).
  assert (ST3 : stk asegs m3 lo usp1).
  { apply (stk_munch _ m2 m3 lo usp1 ST2 MU3 WM3). intros x Hx. cbn [outside]. unfold usp1 in Hx. lia. }
  assert (AG3 : forall a k, (usp <= a /\ a + k <= USTACK_TOP) \/ (0x10000 <= a /\ a + k <= 0xbc6000) -> agree_on (fun x => a <= x < a + k) m2 m3).
  { intros a k H. apply (agree_of_munch _ m2 m3 _ MU3). intros x Hx. cbv beta in Hx. cbn [outside]. unfold USTACK_TOP, RT_STACK in *. lia. }
  assert (AG03 : agree_on (fun x => usp <= x < USTACK_TOP) m m3).
  { intros a Ha. cbv beta in Ha. rewrite (AG3 usp (USTACK_TOP - usp) ltac:(left; lia) a ltac:(cbv beta; lia)).
    rewrite (PRES2 a ltac:(left; unfold usp1; lia)). exact (AG1 a Ha). }
  destruct (cl_chain_call (rt_cg RT Σ) e_lock_new e_CRYPTO_zalloc SITE_ln_zalloc m m3 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH _ ltac:(left; reflexivity)) (proj2 CGH _ ltac:(left; reflexivity)) UWC AG03
              ltac:(fold usp; replace (usp - 16) with (usp + -96 + Z.of_nat (cells_size [CB 24 j3; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m3 (usp + -96) [CB 24 j3; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR3))
              ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTX3 & UWC3).
  (* [comment removed for export] *)
  assert (AGS03 : forall a k, (0x5a9d08 <= a /\ a + k <= 0x6694d8) \/ (0xba3f30 <= a /\ a + k <= 0xbc41b0) \/ (0xb8f190 <= a /\ a + k <= 0xba3e98) ->
            agree_on (fun x => a <= x < a + k) m m3).
  { intros a k H x Hx. cbv beta in Hx.
    rewrite (AG3 a k ltac:(right; lia) x Hx).
    rewrite (PRES2 x ltac:(right; left; apply client_static_intro; lia)).
    apply PR1; [right; left; apply client_static_intro; lia | exact I]. }
  assert (WM03 : wmono asegs m m3) by exact (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 WM3)).
  assert (MIMP3 : ro_cells asegs m3 G_MALLOC_IMPL [C8 (Z_to_bv 64 e_CRYPTO_malloc)])
    by (apply (ro_cells_agree asegs m m3 _ _ MIMP); apply AGS03; cbn [cells_size csize Nat.add]; unfold G_MALLOC_IMPL; lia).
  assert (LAT3 : rw_cells asegs m3 G_ALLOW_CUST [C1 lb])
    by (apply (rw_cells_agree asegs m m3 _ _ LAT); [apply AGS03; cbn [cells_size csize Nat.add]; unfold G_ALLOW_CUST; lia | exact WM03]).
  destruct (af_client_consts RT AF Σ1 m3 ART3) as (_ & _ & _ & _ & UT3).
  assert (GOT3 : ro_cells asegs m3 G_GOT_CMALLOC [C8 (Z_to_bv 64 e_CRYPTO_malloc)])
    by (apply (ut_ro_cells m3 G_GOT_CMALLOC _ UT3); [exact (conj I I) | vm_compute; reflexivity | unfold IMG_UT_LO, G_GOT_CMALLOC; lia | unfold IMG_UT_HI, G_GOT_CMALLOC; cbn; lia]).
  (* [comment removed for export] *)
  rewrite <- CG1 in CTX3, CGH.
  apply (C_CZ Σ1 PMc (Z_to_bv 64 SITE_ln_zalloc) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 40) (Z_to_bv 64 0x491e0)
           (Z_to_bv 64 919) a3' b4 b5 b6 b7 (Z_to_bv 64 f) s3 s4 s5 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m3 40 lo
           (bv_unsigned ra :: outer) lb FDO MST eq_refl eq_refl ltac:(lia) ART3 MI3).
  { unfold call_ok. rewrite EU1, SP1. split; [exact ST3|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|].
    fold usp in SPA. clear - SPA HP HPM. Z.div_mod_to_equations. lia. }
  { rewrite EU1. unfold usp1, RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ln_zalloc) by (unfold SITE_ln_zalloc; lia). exact CTX3. }
  { exact UWC3. }
  { split; intros x Hx; [apply (proj1 CGH) | apply (proj2 CGH)]; right; exact Hx. }
  { rewrite LV1. exact Hlen. } { rewrite CR1. change (mcost 40) with 0. lia. } { exact MIMP3. } { exact GOT3. } { exact LAT3. } { exact HLB. }
  { exact Hc3'. }
  clear Hc3'. intros c4 (Σ2 & p & Hc4 & LV2 & FRS2 & SP2 & CR2 & Pp0 & Pp16 & PpU & CG2).
  destruct (ASTA_unpack RT Σ2 _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & LAT4 & WR4 & ACC4 & ZER4) & Hc4'). clear Hc4.
  destruct RS4 as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F4 & fc4 & ->).
  rewrite EU1 in ST4, PRES4. rewrite (ret_pc_even SITE_ln_zalloc) in Hc4' by (unfold SITE_ln_zalloc; lia).
  assert (INP : In (p, 40) (rt_live RT Σ2)) by (rewrite LV2; left; reflexivity).
  assert (INF2 : In (f, 0%nat) (rt_frames RT Σ2)) by (rewrite FRS2; exact INF).
  pose proof (afp_live_hi RT GOBJ AFP Σ2 m4 p 40 ART4 INP ltac:(lia)) as PHI.
  pose proof (af_live_range RT AF Σ2 m4 p 40 ART4 INP) as (_ & PLO & _). rewrite SP2, SP1 in PLO.
  pose proof (af_frames_range RT AF Σ2 m4 f 0%nat ART4 INF2) as (_ & _ & _ & PF). specialize (PF p 40 INP). change (fs_size 0) with 64 in PF.
  assert (AG4 : forall a k, (usp1 <= a /\ a + k <= USTACK_TOP) \/ (f <= a /\ a + k <= f + 56) \/ (f / 8 + 2147450880 <= a /\ a + k <= f / 8 + 2147450880 + 8)
                            \/ (0xba3f30 <= a /\ a + k <= 0xbc41b0) -> agree_on (fun x => a <= x < a + k) m3 m4).
  { intros a k H x Hx. cbv beta in Hx. apply PRES4.
    - destruct H as [H|[H|[H|H]]].
      + left. lia.
      + apply (acl_frame _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; lia].
      + apply (acl_fshadow _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; rewrite SHF; unfold shad, SHB; lia].
      + right; left. apply client_static_intro. lia.
    - cbn [outside]. unfold G_ALLOW_CUST. split; [| exact I]. unfold USTACK_TOP, RT_STACK, usp1 in *. lia. }
  assert (HDR4 : rw_cells asegs m4 f [C8 (Z_to_bv 64 LN_MAGIC)]).
  { apply (rw_cells_agree asegs m3 m4 _ _ (rw_cells_head m3 f _ _ HDR3)); [| exact WM4]. apply AG4. cbn [cells_size csize Nat.add]. lia. }
  assert (SB4 : rw_cells asegs m4 (f / 8 + 2147450880) ln_shadow).
  { apply (rw_cells_agree asegs m3 m4 _ _ SB3); [| exact WM4]. apply AG4. cbn [ln_shadow cells_size csize Nat.add]. lia. }
  destruct (wr_at_rw_CB m4 (f + 32) 4 (wr_at_wm m3 m4 _ _ (wr_at_wm m2 m3 _ _ (wr_at_sub m2 f 56 (f + 32) 4 WF2 ltac:(lia) ltac:(lia) ltac:(lia)) WM3) WM4) ltac:(lia)) as (aj & ATTR4).
  destruct (wr_at_rw_CB m4 p 40 WR4 ltac:(lia)) as (pj & PB4).
  change (Z.to_nat 4) with 4%nat in ATTR4. change (Z.to_nat 40) with 40%nat in PB4.
  destruct (af_client_consts RT AF Σ2 m4 ART4) as (_ & _ & _ & _ & UT4).
  assert (WM04 : wmono asegs m m4) by exact (wmono_trans asegs _ _ _ WM03 WM4).
  assert (SSP4 : ssp_cells m4 canary).
  { destruct SSP as [SSG SSC]. split.
    - split; [| exact (wr_at_transport asegs m m4 _ _ (proj2 SSG) WM04)].
      apply (ut_ro_cells m4 got_ssp _ UT4); [exact (conj I I) | vm_compute; reflexivity | unfold IMG_UT_LO, got_ssp; lia | unfold IMG_UT_HI, got_ssp; cbn; lia].
    - apply (rw_cells_agree asegs m m4 _ _ SSC); [| exact WM04]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. unfold ssp_guard in Hx.
      rewrite (AG4 ssp_guard 8 ltac:(unfold ssp_guard; lia) x ltac:(cbv beta; unfold ssp_guard; lia)).
      exact (AGS03 ssp_guard 8 ltac:(unfold ssp_guard; lia) x ltac:(cbv beta; unfold ssp_guard; lia)). }
  (* [comment removed for export] *)
  pose proof (locknew_s2_walk sp gp (Z_to_bv 64 0xba3ef0) v0 v1 v2 d1 d2 d3 d4 d5 d6 d7 s3 s4 s5 s8 s9 s10 s11 v3 v4 v5 v6 F4 fc4 m4 p f lo pad aj pj canary
                HP ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia) PHI ltac:(lia) FIMG ltac:(lia)
                ltac:(destruct FSH; [left | right]; lia) ltac:(destruct PF; [right | left]; lia) ST4 HDR4 ATTR4 SB4 PB4 SSP4 MI4) as W2.
  fold usp usp1 in W2.
  cl_lift W2 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ2 _ _ c5 Hc5) as (ms5 & (ra5 & w0 & w1 & w2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & x4 & x5 & w3 & w4 & w5 & w6 & m5 & -> & MU5 & WM5 & MI5 & ST5 & MX5 & SH5) & Hc5'). clear Hc5.
  fold usp in MU5, ST5, Hc5'. fold usp1 in ST5, Hc5'.
  assert (ART5 : ART RT Σ2 m5).
  { apply (af_frame RT AF Σ2 m4 m5 (usp - 176) ART4 ltac:(rewrite SP2, SP1; lia)); [| exact WM5].
    intros a Ha. apply MU5. cbn [outside]. split; [| split; [| split; [| split; [| split; [| exact I]]]]]; intros Hin; apply Ha.
    - apply (acl_live _ _ _ p 40); [exact INP | lia].
    - apply (acl_frame _ _ _ f 0%nat); [exact INF2 | change (fs_size 0) with 64; lia].
    - apply (acl_frame _ _ _ f 0%nat); [exact INF2 | change (fs_size 0) with 64; lia].
    - apply (acl_fshadow _ _ _ f 0%nat); [exact INF2 | change (fs_size 0) with 64; rewrite SHF; unfold shad, SHB; lia].
    - apply acl_stack. unfold USTACK_TOP in *. lia. }
  (* [comment removed for export] *)
  destruct (af_frame_release RT AF Σ2 m5 f 0%nat (rt_frames RT Σ) ART5 ltac:(rewrite FRS2; exact FRS1)) as (Σ3 & fl & FLC & NAC & FL0 & FLW & FW & REL).
  change (fs_size 0) with 64 in FW. replace (f + 64 - 8) with (f + 56) in FW by lia. rewrite SP2, SP1 in FLW.
  assert (AG5 : forall a k, (usp1 <= a /\ a + k <= USTACK_TOP) \/ (0x10000 <= a /\ a + k <= 0xbc6000) -> agree_on (fun x => a <= x < a + k) m4 m5).
  { intros a k H. apply (agree_of_munch _ m4 m5 _ MU5). intros x Hx. cbv beta in Hx. cbn [outside]. unfold USTACK_TOP, RT_STACK, usp1 in *. lia. }
  assert (GAP5 : stk asegs m5 usp1 (usp + -96)).
  { apply (stk_agree_nw asegs m4 m5); [apply (stk_agree_nw asegs m3 m4); [apply (stk_agree_nw asegs m2 m3); [apply (stk_agree_nw asegs m1 m2 _ _ GAP1)|]|]|].
    - intros x Hx. cbv beta in Hx. apply PRES2. left. unfold USTACK_TOP in *. lia.
    - apply (agree_of_munch _ m2 m3 _ MU3). intros x Hx. cbv beta in Hx. cbn [outside]. unfold USTACK_TOP, RT_STACK, usp1 in *. lia.
    - replace (usp + -96) with (usp1 + (usp + -96 - usp1)) by lia. apply AG4. left. unfold USTACK_TOP, usp1 in *. lia.
    - replace (usp + -96) with (usp1 + (usp + -96 - usp1)) by lia. apply AG5. left. unfold USTACK_TOP, usp1 in *. lia. }
  assert (FR5 : rw_cells asegs m5 (usp + -96) [CB 24 j3; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m4 m5); [apply (rw_cells_agree asegs m3 m4 _ _ FR3); [| exact WM4] | | exact WM5].
    - apply AG4. left. cbn [cells_size csize Nat.add]. unfold USTACK_TOP, usp1 in *. lia.
    - apply AG5. left. cbn [cells_size csize Nat.add]. unfold USTACK_TOP, usp1 in *. lia. }
  (* [comment removed for export] *)
  pose proof (locknew_s3_walk ra5 ra sp gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 e0 e1 e2 e3 e4 e5 e6 e7 x4 x5 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s8 s9 s10 s11 w3 w4 w5 w6
                s0 s1 s2 s3 s4 s5 s6 s7 F4 fc4 m5 p f fl lo pad j3 HP ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia)
                F0 ltac:(lia) FL0 ltac:(lia) ST5 GAP5 FR5 FW FLC MI5) as W3.
  fold usp usp1 in W3.
  cl_lift W3 Hc5' c6 Hc6.
  destruct (ASTA_unpack RT Σ2 _ _ c6 Hc6) as (ms6 & (y0 & y1 & y2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & y3 & y4 & y5 & y6 & m6 & -> & MU6 & WM6 & MI6 & ST6 & FLC6) & Hc6'). clear Hc6.
  fold usp in ST6.
  destruct (REL m6 MU6 WM6 FLC6) as (ART6 & FRS3 & LV3 & SP3 & CR3 & AL3 & AM3 & CG3).
  assert (LV3' : rt_live RT Σ3 = (p, 40) :: rt_live RT Σ) by (rewrite LV3, LV2, LV1; reflexivity).
  assert (INP3 : In (p, 40) (rt_live RT Σ3)) by (rewrite LV3'; left; reflexivity).
  (* [comment removed for export] *)
  assert (NFL : forall x, aclient (rt_live RT Σ2) (rt_frames RT Σ2) usp1 x -> x <> fl).
  { intros x Hx E. subst x. apply NAC. destruct Hx as [H|H]; [exfalso; unfold usp1, RT_STACK in *; lia | right; exact H]. }
  assert (AG6 : forall a k, (forall x, a <= x < a + k -> x <> fl) -> agree_on (fun x => a <= x < a + k) m5 m6).
  { intros a k H. apply (agree_of_munch _ m5 m6 _ MU6). intros x Hx. cbv beta in Hx. specialize (H x Hx). cbn [outside]. lia. }
  apply Hk. exists Σ3, p.
  split; [| split; [exact LV3' | split; [rewrite FRS3; reflexivity | split; [rewrite SP3, SP2; exact SP1 | split; [rewrite CR3, CR2, CR1; change (mcost 40) with 0; lia |
            split; [exact Pp0 | split; [exact Pp16 | split; [exact PpU | rewrite CG3, CG2; exact CG1]]]]]]]].
  eapply ASTA_conseq; [exact (ASTA_switch RT Σ2 Σ3 PMc _ c6 Hc6' AL3 AM3)|]. intros ms <-. exists m6.
  split; [exists y0, y1, y2, g1, g2, g3, g4, g5, g6, g7, y3, y4, y5, y6, F4, fc4; reflexivity|].
  split; [split; [exact ART6 | split; [exact MI6 | split; [exact (wmono_trans asegs _ _ _ WM04 (wmono_trans asegs _ _ _ WM5 WM6)) | exact ST6]]]|].
  split.
  { intros a Ha Ho.
    assert (A1 : aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp1 (bv_unsigned a))
      by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LV1; auto | rewrite FRS1; intros e He; right; exact He | unfold usp1; lia]).
    assert (A2 : aclient (rt_live RT Σ2) (rt_frames RT Σ2) usp1 (bv_unsigned a))
      by (apply (aclient_mono _ _ _ _ _ _ _ A1); [rewrite LV2; intros e He; right; exact He | rewrite FRS2; auto | lia]).
    destruct (newframe_apart RT AF Σ Σ1 m2 f 0%nat usp _ ART2 FRS1 LV1 SP1 ltac:(lia) Ha) as (N1 & N2).
    change (fs_size 0) with 64 in N1, N2. rewrite SHF in N2. unfold shad, SHB in N2.
    pose proof (newchunk_apart RT AF Σ1 Σ2 m4 p 40 usp1 _ ART4 LV2 FRS2 SP2 ltac:(rewrite SP1; unfold usp1; lia) ltac:(lia) A1) as N3.
    pose proof (cl_split RT AF Σ m usp 176 _ ART0 ltac:(lia) ltac:(lia) Ha) as N4.
    pose proof (NFL _ A2) as N5.
    rewrite (MU6 a ltac:(cbn [outside]; split; [lia | exact I])).
    rewrite (MU5 a ltac:(cbn [outside]; clear - N1 N2 N3 N4 HP; lia)).
    rewrite (PRES4 a A1 Ho).
    rewrite (MU3 a ltac:(cbn [outside]; lia)).
    rewrite (PRES2 a ltac:(apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto | auto | unfold usp1; lia])).
    exact (PR1 a Ha I). }
  split.
  { apply (rw_cells_agree asegs m5 m6); [apply (rw_cells_agree asegs m4 m5 _ _ LAT4); [| exact WM5] | | exact WM6].
    - apply AG5. right. cbn [cells_size csize Nat.add]. unfold G_ALLOW_CUST. lia.
    - apply AG6. intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply NFL. right; left. apply client_static_intro. unfold G_ALLOW_CUST in *. lia. }
  split.
  { destruct (af_client_consts RT AF Σ3 m6 ART6) as (_ & _ & _ & _ & UT6). destruct SSP4 as [SSG4 SSC4]. split.
    - split; [| exact (wr_at_transport asegs m4 m6 _ _ (proj2 SSG4) (wmono_trans asegs _ _ _ WM5 WM6))].
      apply (ut_ro_cells m6 got_ssp _ UT6); [exact (conj I I) | vm_compute; reflexivity | unfold IMG_UT_LO, got_ssp; lia | unfold IMG_UT_HI, got_ssp; cbn; lia].
    - apply (rw_cells_agree asegs m5 m6); [apply (rw_cells_agree asegs m4 m5 _ _ SSC4); [| exact WM5] | | exact WM6].
      + apply AG5. right. cbn [cells_size csize Nat.add]. unfold ssp_guard. lia.
      + apply AG6. intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply NFL. right; left. apply client_static_intro. unfold ssp_guard in *. lia. }
  split.
  { apply (rw_cells_agree asegs m5 m6 _ _ MX5); [| exact WM6]. apply AG6. intros x Hx. unfold mutex_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply NFL. apply (acl_live _ _ _ p 40); [exact INP | lia]. }
  exact (proj2 (af_acc_live RT AF Σ3 m6 p 40 ART6 INP3)).
Qed.

End CLockNew.
