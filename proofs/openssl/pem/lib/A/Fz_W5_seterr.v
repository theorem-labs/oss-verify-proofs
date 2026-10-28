(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_T_sa Fz_W5_glx Fz_W5_icb Fz_W5_gsi.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Fz_W5_rep Fz_W5_vset.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition e_set_error : Z := 0x1fcbb4.
Definition SITE_se_smalloc : Z := 0x1fcc30.      (* [comment removed for export] *)
Definition SITE_se_spilled : Z := 0x1fcc64.      (* [comment removed for export] *)
Definition SITE_se_vset : Z := 0x1fccd4.         (* [comment removed for export] *)
Definition SITE_se_release : Z := 0x1fcd10.      (* [comment removed for export] *)
Definition SE_MAGIC : Z := 0x41b58ab3.
Definition SE_DESCR : Z := 0x1bb82.
(* [comment removed for export] *)
Definition se_shadow : list cell :=
  [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))].

(* [comment removed for export] *)
Definition se_s0_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo pd : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a1' : word) (j : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_se_smalloc) (Z_to_bv 64 (bv_unsigned sp + -128 - pd)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -48)) (Z_to_bv 64 (bv_unsigned sp + -128 - pd))
                 (Z_to_bv 64 64) a1' a2 a3 a4 a5 a6 a7 a2 a1 a0 s5 (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (e_stack_malloc 0)) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 128, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -128) [C8 (Z_to_bv 64 0); C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra; CB 8 j; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7]
    /\ stk asegs m' (bv_unsigned sp + -128 - pd) (bv_unsigned sp + -128)
    /\ stk asegs m' lo (bv_unsigned sp + -128 - pd).

Lemma se_s0_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo pd : Z),
  (pd = 0 \/ pd = 16) -> bv_unsigned sp mod 32 = pd ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 144 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  ro_cells asegs m g_detect_stack_use_after_return [C4 (Z_to_bv 64 1)] -> mem_inv asegs m ->
  evt asegs (se_s0_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo pd m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_set_error) fc None m (seg_rom asegs)).
Proof.
  intros until pd. intros HP HPM ST HLO HLOS SPH UT SHC UAR MI. unfold e_set_error, g_shadow_memory_dynamic_address, g_detect_stack_use_after_return in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 128, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 128, SP)]) by ut_fp_lia.
  th_frame 128%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  zstep. zstep; lfix. do 10 zstep. zstep.
  rewrite (land_m32_pad (SP + -128) pd) by (first [lia | replace (SP + -128) with (SP + (-4) * 32) by lia; rewrite Z.mod_add by lia; exact HPM]).
  do 4 zstep. do 2 zstep. zstep. zstep. zstep. zstep. zstep. do 4 zstep. zstep. if_false. do 2 zstep.
  destruct (stk_split asegs _ lo (SP + -128 - pd) (SP + -128) ST ltac:(lia)) as [ST1 GAP].
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold se_s0_post, SITE_se_smalloc, e_stack_malloc. apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [eassumption|]. split; [exact GAP| exact ST1].
Qed.

(* [comment removed for export] *)
Definition se_s1a_post (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' e3 e4 e5 e6 e7 : word) (f lo pd : Z) (j : list byte) (fj sj : list byte) (m : mem) : machine_state -> Prop :=
  fun ms => exists (j0 : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_se_smalloc) (Z_to_bv 64 (bv_unsigned sp + -128 - pd)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -48)) (Z_to_bv 64 (bv_unsigned sp + -128 - pd))
                 (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 f) s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 SITE_se_spilled) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp - 120)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -128) [CB 8 j0; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0; CB 8 j; C8 e3; C8 e4; C8 e5; C8 e6; C8 e7]
    /\ stk asegs m' (bv_unsigned sp + -128 - pd) (bv_unsigned sp + -128)
    /\ stk asegs m' lo (bv_unsigned sp + -128 - pd)
    /\ rw_cells asegs m' f [CB 56 fj] /\ rw_cells asegs m' (f / 8 + 2147450880) [CB 8 sj].

Lemma se_s1a_walk : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' e3 e4 e5 e6 e7 : word) (c0 : word) (F : bvmap 5 word) fc (m : mem) (f lo pd : Z) (j fj sj : list byte),
  (pd = 0 \/ pd = 16) -> 0 < f -> 0xbc6000 <= f -> f + 64 <= lo -> (f + 64 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  lo <= bv_unsigned sp - 144 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  rw_cells asegs m (bv_unsigned sp + -128) [C8 c0; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0; CB 8 j; C8 e3; C8 e4; C8 e5; C8 e6; C8 e7] ->
  stk asegs m (bv_unsigned sp + -128 - pd) (bv_unsigned sp + -128) -> stk asegs m lo (bv_unsigned sp + -128 - pd) ->
  rw_cells asegs m f [CB 56 fj] -> rw_cells asegs m (f / 8 + 2147450880) [CB 8 sj] -> mem_inv asegs m ->
  evt asegs (se_s1a_post sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc ra0 s0' s1' s2' s3' s4' s5' s6' s7' e3 e4 e5 e6 e7 f lo pd j fj sj m)
    (MS (mkR (Z_to_bv 64 SITE_se_smalloc) (Z_to_bv 64 (bv_unsigned sp + -128 - pd)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -48)) (Z_to_bv 64 (bv_unsigned sp + -128 - pd))
             (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_se_smalloc) fc None m (seg_rom asegs)).
Proof.
  intros until sj. intros HP F0 FIMG FLO FSH HLO HLOS SPH FR GAP ST FB SB MI. unfold SITE_se_smalloc in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl [(SP - 144, SP - 120)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 8 <= 0x10007fff8000).
  { pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)). assert (f / 8 + 8 <= 2^44) by (Z.div_mod_to_equations; lia). lia. }
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  do 3 zstep. zstep. if_true.
  destruct HP as [-> | ->].
  1: replace (SP + -128 - 0) with (SP + -128) in * by lia.
  2: replace (SP + -128 - 16) with (SP + -144) in * by lia; carve_frame 16%nat GAP.
  all: zstep.
  all: pose proof (rw_cells_blur _ _ [_] _ FR) as FRB; cbn [cells_size csize Nat.add app cells_bytes cbytes] in FRB.
  all: try match goal with H : rw_cells _ _ ?a [C8 _; CB 8 _], G : stk _ _ ?a ?a |- _ => release_frame H G (SP + -128) end.
  all: subst SP.
  all: unfold se_s1a_post, SITE_se_spilled.
  all: try replace (bv_unsigned sp + -128 - 0) with (bv_unsigned sp + -128) by lia.
  all: try replace (bv_unsigned sp + -128 - 16) with (bv_unsigned sp + -144) by lia.
  all: apply evt_done; do 2 eexists; split; [reflexivity|].
  all: split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [exact FRB|]; split; [eassumption|]; split; [eassumption|]; split; assumption.
Qed.

(* [comment removed for export] *)
Definition se_s1b_post (sp gp tp t0 t1 t2 a4 a5 a6 a7 s2 s3 s4 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' e3 e4 e5 e6 e7 : word) (f lo pd : Z) (j0 j : list byte) (m : mem) : machine_state -> Prop :=
  fun ms => exists (hj tj : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_se_vset) (Z_to_bv 64 (bv_unsigned sp + -128 - pd)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -48)) (Z_to_bv 64 (bv_unsigned sp + -128 - pd))
                 s4 s3 s2 (Z_to_bv 64 (bv_unsigned sp + -40)) a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 f) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_vset_error) fc None m' (seg_rom asegs)
    /\ munch [(f, f + 40); (f / 8 + 2147450880, f / 8 + 2147450880 + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' f [C8 (Z_to_bv 64 SE_MAGIC); C8 (Z_to_bv 64 SE_DESCR); C8 (Z_to_bv 64 e_set_error); CB 8 hj; C8 (Z_to_bv 64 (bv_unsigned sp + -40)); CB 16 tj]
    /\ rw_cells asegs m' (f / 8 + 2147450880) se_shadow
    /\ rw_cells asegs m' (bv_unsigned sp + -128) [CB 8 j0; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0; CB 8 j; C8 e3; C8 e4; C8 e5; C8 e6; C8 e7]
    /\ stk asegs m' (bv_unsigned sp + -128 - pd) (bv_unsigned sp + -128)
    /\ stk asegs m' lo (bv_unsigned sp + -128 - pd).

Lemma se_s1b_walk : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s8 s9 s10 s11 t3 t4 t5 t6
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' e3 e4 e5 e6 e7 : word) (F : bvmap 5 word) fc (m : mem) (f lo pd : Z) (j0 j fj sj : list byte),
  (pd = 0 \/ pd = 16) -> 0 < f -> f mod 64 = 0 -> 0xbc6000 <= f -> f + 64 <= lo -> (f + 64 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  lo <= bv_unsigned sp - 144 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m ->
  rw_cells asegs m (bv_unsigned sp + -128) [CB 8 j0; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0; CB 8 j; C8 e3; C8 e4; C8 e5; C8 e6; C8 e7] ->
  stk asegs m (bv_unsigned sp + -128 - pd) (bv_unsigned sp + -128) -> stk asegs m lo (bv_unsigned sp + -128 - pd) ->
  rw_cells asegs m f [CB 56 fj] -> rw_cells asegs m (f / 8 + 2147450880) [CB 8 sj] -> mem_inv asegs m ->
  evt asegs (se_s1b_post sp gp tp t0 t1 t2 a4 a5 a6 a7 s2 s3 s4 s8 s9 s10 s11 t3 t4 t5 t6 F fc ra0 s0' s1' s2' s3' s4' s5' s6' s7' e3 e4 e5 e6 e7 f lo pd j0 j m)
    (MS (mkR (Z_to_bv 64 SITE_se_smalloc) (Z_to_bv 64 (bv_unsigned sp + -128 - pd)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -48)) (Z_to_bv 64 (bv_unsigned sp + -128 - pd))
             (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_se_spilled) fc None m (seg_rom asegs)).
Proof.
  intros until sj. intros HP F0 F64 FIMG FLO FSH HLO HLOS SPH UT FR GAP ST FB SB MI. unfold SITE_se_spilled in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl [(f, f + 40); (f / 8 + 2147450880, f / 8 + 2147450880 + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 8 <= 0x10007fff8000).
  { pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)). assert (f / 8 + 8 <= 2^44) by (Z.div_mod_to_equations; lia). lia. }
  assert (HWU : ut_fp [(f, f + 40); (f / 8 + 2147450880, f / 8 + 2147450880 + 8)]) by (clear - F0 FIMG SHR HLO HLOS SPH FLO; ut_fp_lia).
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  pose proof (div8_facts f) as Q1.
  apply (rw_cells_split_CB asegs _ f [] 56 fj [] [8; 8; 8; 8; 8; 16]%nat) in FB; [| reflexivity]. cbn [mk_CB_cells app] in FB.
  zstep. zstep. zstep. rewrite (shr3_div f) by lia. zstep. zstep. zstep. zstep. zstep.
  zstep; lfix. zstep; lfix. zstep; lfix.
  zstep. zstep; lfix. zstep; lfix. zstep; lfix. zstep; lfix.
  zstep. zstep; lfix. zstep; lfix. zstep; lfix. zstep; lfix.
  zstep. zstep.
  do 4 zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold se_s1b_post, SITE_se_vset, e_vset_error, SE_MAGIC, SE_DESCR, e_set_error, se_shadow. apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
Definition se_s2_post (sp gp tp s2 s3 s4 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' e3 e4 e5 e6 e7 : word) (f lo pd : Z) (j0 j : list byte) (m : mem) : machine_state -> Prop :=
  fun ms => exists (ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -128 - pd)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -48)) (Z_to_bv 64 (bv_unsigned sp + -128 - pd))
                 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 f) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 SITE_se_release) fc None m' (seg_rom asegs)
    /\ munch [(f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -128) [CB 8 j0; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0; CB 8 j; C8 e3; C8 e4; C8 e5; C8 e6; C8 e7]
    /\ stk asegs m' (bv_unsigned sp + -128 - pd) (bv_unsigned sp + -128)
    /\ stk asegs m' lo (bv_unsigned sp + -128 - pd).

Lemma se_s2_walk : forall ra1 sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s8 s9 s10 s11 t3 t4 t5 t6
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' e3 e4 e5 e6 e7 : word) (F : bvmap 5 word) fc (m : mem) (f lo pd : Z) (j0 j : list byte),
  (pd = 0 \/ pd = 16) -> 0 < f -> 0xbc6000 <= f -> f + 64 <= lo -> (f + 64 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  lo <= bv_unsigned sp - 144 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  rw_cells asegs m (bv_unsigned sp + -128) [CB 8 j0; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0; CB 8 j; C8 e3; C8 e4; C8 e5; C8 e6; C8 e7] ->
  stk asegs m (bv_unsigned sp + -128 - pd) (bv_unsigned sp + -128) -> stk asegs m lo (bv_unsigned sp + -128 - pd) ->
  rw_cells asegs m f [C8 (Z_to_bv 64 SE_MAGIC)] -> rw_cells asegs m (f / 8 + 2147450880) se_shadow -> mem_inv asegs m ->
  evt asegs (se_s2_post sp gp tp s2 s3 s4 s8 s9 s10 s11 F fc ra0 s0' s1' s2' s3' s4' s5' s6' s7' e3 e4 e5 e6 e7 f lo pd j0 j m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -128 - pd)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -48)) (Z_to_bv 64 (bv_unsigned sp + -128 - pd))
             a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 f) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_se_vset) fc None m (seg_rom asegs)).
Proof.
  intros until j. intros HP F0 FIMG FLO FSH HLO HLOS SPH FR GAP ST HDR SB MI. unfold SITE_se_vset, SE_MAGIC, se_shadow in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl [(f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 8 <= 0x10007fff8000).
  { pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)). assert (f / 8 + 8 <= 2^44) by (Z.div_mod_to_equations; lia). lia. }
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  pose proof (div8_facts f) as Q1.
  zstep. zstep; lfix. zstep. zstep. zstep; lfix.
  zstep. if_cases KF; zify_cond KF; [exfalso; lia|].
  zstep. do 8 (zstep; lfix).
  subst SP.
  unfold se_s2_post, SITE_se_release. apply evt_done. do 17 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
Definition se_s3_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (fl lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 fl) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(fl, fl + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' fl [C1 (Z_to_bv 8 0)].

Lemma se_s3_walk : forall ra1 ra0 sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s8 s9 s10 s11 t3 t4 t5 t6
    (s0' s1' s2' s3' s4' s5' s6' s7' e3 e4 e5 e6 e7 : word) (F : bvmap 5 word) fc (m : mem) (f fl lo pd : Z) (j0 j : list byte),
  (pd = 0 \/ pd = 16) -> lo <= bv_unsigned sp - 144 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  0 < f -> f + 64 <= lo -> 0 < fl -> fl + 1 <= lo ->
  stk asegs m lo (bv_unsigned sp + -128 - pd) -> stk asegs m (bv_unsigned sp + -128 - pd) (bv_unsigned sp + -128) ->
  rw_cells asegs m (bv_unsigned sp + -128) [CB 8 j0; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0; CB 8 j; C8 e3; C8 e4; C8 e5; C8 e6; C8 e7] ->
  ro_cells asegs m (f + 56) [C8 (Z_to_bv 64 fl)] -> rw_cells asegs m fl [C1 (Z_to_bv 8 1)] -> mem_inv asegs m ->
  evt asegs (se_s3_post ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 F fc fl lo m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -128 - pd)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -48)) (Z_to_bv 64 (bv_unsigned sp + -128 - pd))
             a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 f) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_se_release) fc None m (seg_rom asegs)).
Proof.
  intros until j. intros HP HLO HLOS SPH F0 FLO FL0 FLLO ST1 GAP FR FLG FLB MI. unfold SITE_se_release in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EUfl : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply unsigned_lit; lia).
  zstep. clear FLG.
  zstep; lfix.
  zstep. zstep.
  do 9 zstep.
  pose proof (stk_merge asegs _ lo (SP + -128 - pd) (SP + -128) ST1 GAP ltac:(lia)) as ST2.
  zstep. release_frame FR ST2 SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold se_s3_post. apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption| assumption].
Qed.

Section CSe.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis SM0 : stack_malloc_contract RT 0.
Hypothesis C_VSE : err_vset_error_stmt RT.

(* [comment removed for export] *)
Definition err_set_error_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (od e : word) (k MK SA NODES E LV : Z) (pad tw ne : word) (top bot : Z) (fl mk buf fs ls fn : list word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a2 = Z_to_bv 64 0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 448 <= bv_unsigned sp ->
  (S (length (rt_frames RT Σ)) < FRAMES_MAX)%nat -> 2 <= rt_credit RT Σ ->
  err_env m od e k MK SA NODES E LV pad tw ne -> err_blocks (rt_live RT Σ) MK SA NODES E -> es_rep m E top bot fl mk buf fs ls fn ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_set_error m)))
    (fun c => exists (Σ' : rts RT) (e' v : word) (buf' : list word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (VSE_W E) m m'
           /\ err_env m' od e' k MK SA NODES E LV pad tw ne /\ es_rep m' E top bot fl mk buf' fs ls fn) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - 2 /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem err_set_error_cps : err_set_error_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo od e k MK SA NODES E LV pad tw ne top bot fl mk buf fs ls fn
    FDO MST -> -> ART0 MI0 CALL HSTK Hfr Hcr ENV BLK ES.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  set (pd := usp mod 32).
  assert (HP : pd = 0 \/ pd = 16) by (unfold pd; clear - SPA; Z.div_mod_to_equations; lia).
  assert (HPM : usp mod 32 = pd) by reflexivity. clearbody pd.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 448 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLOI : SEGTOP_A <= lo) by (unfold SEGTOP_A, STACK_WIN in *; lia).
  set (usp1 := usp + -128 - pd).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & UAR & UT).
  pose proof BLK as (INM & INS & INN & INE & MKAL & SAAL & NAL & EAL).
  pose proof (af_live_range RT AF Σ m MK 72 ART0 INM) as R1. pose proof (af_live_range RT AF Σ m SA 32 ART0 INS) as R2.
  pose proof (af_live_range RT AF Σ m NODES 128 ART0 INN) as R3. pose proof (af_live_range RT AF Σ m E 904 ART0 INE) as R4.
  (* [comment removed for export] *)
  pose proof (se_s0_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pd
                HP HPM ST ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia) UT SHC UAR MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (a1' & j & m1 & -> & MU1 & WM1 & MI1 & FR1 & GAP1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, GAP1, ST1, Hc1'. fold usp1 in GAP1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 128 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 128 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  (* [comment removed for export] *)
  apply (SM0 Σ PMc (Z_to_bv 64 SITE_se_smalloc) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 (Z_to_bv 64 (usp + -48)) (Z_to_bv 64 usp1) (Z_to_bv 64 64) a1' (Z_to_bv 64 0) a3 a4 a5 a6 a7
           (Z_to_bv 64 0) a1 a0 s5 (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo FDO MST ltac:(left; reflexivity) eq_refl ltac:(clear - Hfr; lia) ltac:(clear - Hcr; lia) ART1 MI1).
  { unfold call_ok. rewrite EU1. split; [exact ST1|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|].
    fold usp in SPA. clear - SPA HP HPM. Z.div_mod_to_equations. lia. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & f & Hc2 & FRS1 & LV1 & SP1 & CR1 & F0 & F64 & FU & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WF2 & WS2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_se_smalloc) in Hc2' by (unfold SITE_se_smalloc; lia).
  assert (INF : In (f, 0%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  pose proof (af_frames_range RT AF Σ1 m2 f 0%nat ART2 INF) as (_ & FLO & _ & PF).
  assert (INE1 : In (E, 904) (rt_live RT Σ1)) by (rewrite LV1; exact INE).
  pose proof (PF E 904 INE1) as PFE. clear PF. pose proof (proj1 (af_fshadow_apart RT AF Σ1 m2 f 0%nat ART2 INF) E 904 INE1) as SLE.
  change (fs_size 0) with 64 in PFE, SLE.
  pose proof (af_frames_align RT AF Σ1 m2 f 0%nat ART2 INF) as (_ & FIMG).
  pose proof (af_frames_hi RT AF Σ1 m2 f 0%nat ART2 INF) as FSH.
  rewrite SP1 in FLO. change (fs_size 0) with 64 in FLO, FSH, FU, WF2, WS2. change (64 - 8) with 56 in WF2. change (64 / 8) with 8 in WS2.
  unfold shad, SHB in WS2. unfold SEGTOP_A in FIMG.
  assert (SHF : shad (f + 64) = shad f + 8) by (replace (f + 64) with (f + 64 * 1) by lia; rewrite (shad_add64 f 1 F64); lia).
  rewrite SHF in SLE. unfold shad, SHB in SLE.
  assert (AG2 : forall a n, usp1 <= a -> a + n <= USTACK_TOP -> agree_on (fun x => a <= x < a + n) m1 m2).
  { intros a n H1 H2 x Hx. cbv beta in Hx. apply PRES2. left. lia. }
  cl_keep FR1 AG2 WM2 FR2.
  assert (GAP2 : stk asegs m2 usp1 (usp + -128)).
  { apply (stk_agree_nw asegs m1 m2 _ _ GAP1). intros x Hx. cbv beta in Hx. apply PRES2. left. unfold USTACK_TOP in *. lia. }
  destruct (wr_at_rw_CB m2 f 56 WF2 ltac:(lia)) as (fj & FB2). destruct (wr_at_rw_CB m2 (f / 8 + 2147450880) 8 WS2 ltac:(lia)) as (sj & SB2).
  change (Z.to_nat 56) with 56%nat in FB2. change (Z.to_nat 8) with 8%nat in SB2.
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & _ & _ & _ & UT2).
  (* [comment removed for export] *)
  pose proof (se_s1a_walk sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 0) a1 a0 s5 (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 u3 u4 u5 u6
                ra s0 s1 s2 s3 s4 s5 s6 s7 a3 a4 a5 a6 a7 (Z_to_bv 64 0) F2 fc2 m2 f lo pd j fj sj
                HP F0 FIMG ltac:(lia) ltac:(destruct FSH; [left | right]; lia) ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia)
                FR2 GAP2 ST2 FB2 SB2 MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (j0 & m3 & -> & MU3 & WM3 & MI3 & FR3 & GAP3 & ST3 & FB3 & SB3) & Hc3'). clear Hc3.
  fold usp in MU3, FR3, GAP3, Hc3'. fold usp1 in GAP3, ST3, Hc3'.
  assert (ART3 : ART RT Σ1 m3).
  { apply (af_frame RT AF Σ1 m2 m3 (usp - 144) ART2 ltac:(rewrite SP1; lia)); [| exact WM3].
    intros a Ha. apply MU3. cbn [outside]. split; [| exact I]. intros Hin; apply Ha. apply acl_stack. unfold USTACK_TOP in *. lia. }
  destruct (af_client_consts RT AF Σ1 m3 ART3) as (_ & _ & _ & _ & UT3).
  (* [comment removed for export] *)
  pose proof (se_s1b_walk sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 0) a1 a0 s8 s9 s10 s11 u3 u4 u5 u6
                ra s0 s1 s2 s3 s4 s5 s6 s7 a3 a4 a5 a6 a7 F2 fc2 m3 f lo pd j0 j fj sj
                HP F0 F64 FIMG ltac:(lia) ltac:(destruct FSH; [left | right]; lia) ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia)
                UT3 FR3 GAP3 ST3 FB3 SB3 MI3) as W2.
  fold usp usp1 in W2.
  cl_lift W2 Hc3' c4 Hc4.
  destruct (ASTA_unpack RT Σ1 _ _ c4 Hc4) as (ms4 & (hj & tj & m4 & -> & MU4 & WM4 & MI4 & HDR4 & SB4 & FR4 & GAP4 & ST4) & Hc4'). clear Hc4.
  fold usp in MU4, HDR4, FR4, GAP4, Hc4'. fold usp1 in GAP4, ST4, Hc4'.
  assert (ART4 : ART RT Σ1 m4).
  { apply (af_frame RT AF Σ1 m3 m4 usp1 ART3 ltac:(rewrite SP1; unfold usp1; lia)); [| exact WM4].
    intros a Ha. apply MU4. cbn [outside]. split; [| split; [| exact I]]; intros Hin; apply Ha.
    - apply (acl_frame _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; lia].
    - apply (acl_fshadow _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; rewrite SHF; unfold shad, SHB; lia]. }
  (* [comment removed for export] *)
  assert (A04 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> (bv_unsigned x < usp - 144 \/ usp <= bv_unsigned x) -> m4 x = m x).
  { intros x Hx Hlt.
    destruct (newframe_apart RT AF Σ Σ1 m2 f 0%nat usp _ ART2 FRS1 LV1 SP1 ltac:(lia) Hx) as (N1 & N2).
    change (fs_size 0) with 64 in N1, N2. rewrite SHF in N2. unfold shad, SHB in N2.
    rewrite (MU4 x ltac:(cbn [outside]; clear - N1 N2; lia)). rewrite (MU3 x ltac:(cbn [outside]; clear - Hlt; lia)).
    rewrite (PRES2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; lia])).
    apply MU1. cbn [outside]. clear - Hlt. lia. }
  assert (WM04 : wmono asegs m m4) by exact (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 (wmono_trans asegs _ _ _ WM3 WM4))).
  assert (ENV4 : err_env m4 od e k MK SA NODES E LV pad tw ne).
  { pose proof ENV as (_ & _ & (_ & _ & HK & _)).
    apply (err_env_agree m m4 _ _ _ _ _ _ _ _ _ _ _ ENV); [| exact WM04]. intros a n H x Hx. cbv beta in Hx. apply A04.
    - destruct H as [H|[H|[H|[H|[H|H]]]]].
      1-3: right; left; apply client_static_intro; unfold ERRNO_A in H; lia.
      + apply (acl_live _ _ _ MK 72); [exact INM | lia].
      + apply (acl_live _ _ _ SA 32); [exact INS | lia].
      + apply (acl_live _ _ _ NODES 128); [exact INN | lia].
    - left. unfold ERRNO_A, STACK_WIN, RT_STACK in *. clear - H Hx HK NUM R1 R2 R3 LOW HSTK. lia. }
  assert (ES4 : es_rep m4 E top bot fl mk buf fs ls fn).
  { apply (es_rep_agree m m4 _ _ _ _ _ _ _ _ _ ES); [| exact WM04]. intros x Hx. cbv beta in Hx. apply A04.
    - apply (acl_live _ _ _ E 904); [exact INE | lia].
    - left. unfold STACK_WIN, RT_STACK in *. clear - Hx NUM R4 LOW HSTK. lia. }
  (* [comment removed for export] *)
  apply (C_VSE Σ1 PMc (Z_to_bv 64 SITE_se_vset) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 (Z_to_bv 64 (usp + -48)) (Z_to_bv 64 usp1) a0 a1 (Z_to_bv 64 0)
           (Z_to_bv 64 (usp + -40)) b4 b5 b6 b7 (Z_to_bv 64 0) a1 a0 (Z_to_bv 64 f) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m4 lo
           od e k MK SA NODES E LV pad tw ne top bot fl mk buf fs ls fn FDO MST eq_refl eq_refl ART4 MI4).
  { fold usp in SPA. unfold call_ok. rewrite EU1, SP1. split; [exact ST4|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|].
    clear - SPA HP HPM. Z.div_mod_to_equations. lia. }
  { rewrite EU1. unfold usp1. clear - HSTK HP. lia. }
  { rewrite FRS1. cbn [length]. exact Hfr. } { rewrite CR1. clear - Hcr. lia. }
  { exact ENV4. } { rewrite LV1. exact BLK. } { exact ES4. }
  { exact Hc4'. }
  clear Hc4'. intros c5 (Σ2 & e2 & v & buf' & Hc5 & LV2 & FRS2 & SP2 & CR2 & CG2).
  destruct (ASTA_unpack RT Σ2 _ _ c5 Hc5) as (ms5 & (m5 & RS5 & (ART5 & MI5 & WM5 & ST5) & PRES5 & ENV5 & ES5) & Hc5'). clear Hc5.
  destruct RS5 as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F5 & fc5 & ->).
  rewrite EU1 in ST5, PRES5. rewrite (ret_pc_even SITE_se_vset) in Hc5' by (unfold SITE_se_vset; lia).
  assert (INF2 : In (f, 0%nat) (rt_frames RT Σ2)) by (rewrite FRS2; exact INF).
  assert (AG5 : forall a n, (usp1 <= a /\ a + n <= USTACK_TOP) \/ (f <= a /\ a + n <= f + 56) \/ (f / 8 + 2147450880 <= a /\ a + n <= f / 8 + 2147450880 + 8) ->
            agree_on (fun x => a <= x < a + n) m4 m5).
  { intros a n H x Hx. cbv beta in Hx. pose proof (div8_facts f) as Q1. destruct H as [H|[H|H]]; (apply PRES5; [| unfold VSE_W, ERRNO_A; cbn [outside]]).
    - left. lia.
    - unfold USTACK_TOP, RT_STACK, STACK_WIN, usp1 in *. clear - H Hx R4 NUM HP LOW HSTK. lia.
    - apply (acl_frame _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; lia].
    - clear - H Hx PFE FIMG. lia.
    - apply (acl_fshadow _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; rewrite SHF; unfold shad, SHB; lia].
    - clear - H Hx SLE Q1 F0. lia. }
  assert (HDR5 : rw_cells asegs m5 f [C8 (Z_to_bv 64 SE_MAGIC)]).
  { apply (rw_cells_agree asegs m4 m5 _ _ (rw_cells_head m4 f _ _ HDR4)); [| exact WM5]. apply AG5. cbn [cells_size csize Nat.add]. lia. }
  assert (SB5 : rw_cells asegs m5 (f / 8 + 2147450880) se_shadow).
  { apply (rw_cells_agree asegs m4 m5 _ _ SB4); [| exact WM5]. apply AG5. cbn [se_shadow cells_size csize Nat.add]. lia. }
  assert (AG5s : forall a n, usp1 <= a -> a + n <= USTACK_TOP -> agree_on (fun x => a <= x < a + n) m4 m5) by (intros a n H1 H2; apply AG5; left; lia).
  cl_keep FR4 AG5s WM5 FR5.
  assert (GAP5 : stk asegs m5 usp1 (usp + -128)).
  { apply (stk_agree_nw asegs m4 m5 _ _ GAP4). intros x Hx. cbv beta in Hx. apply PRES5; [left; unfold USTACK_TOP in *; lia|].
    unfold VSE_W, ERRNO_A; cbn [outside]. unfold USTACK_TOP, RT_STACK, STACK_WIN, usp1 in *. clear - Hx R4 NUM LOW HSTK HP. lia. }
  (* [comment removed for export] *)
  pose proof (se_s2_walk (Z_to_bv 64 SITE_se_vset) sp gp (Z_to_bv 64 0xba3ef0) v0 v1 v2 v d1 d2 d3 d4 d5 d6 d7 (Z_to_bv 64 0) a1 a0 s8 s9 s10 s11 v3 v4 v5 v6
                ra s0 s1 s2 s3 s4 s5 s6 s7 a3 a4 a5 a6 a7 F5 fc5 m5 f lo pd j0 j
                HP F0 FIMG ltac:(lia) ltac:(destruct FSH; [left | right]; lia) ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia)
                FR5 GAP5 ST5 HDR5 SB5 MI5) as W3.
  fold usp usp1 in W3.
  cl_lift W3 Hc5' c6 Hc6.
  destruct (ASTA_unpack RT Σ2 _ _ c6 Hc6) as (ms6 & (ra1 & w0 & w1 & w2 & g0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & m6 & -> & MU6 & WM6 & MI6 & FR6 & GAP6 & ST6) & Hc6'). clear Hc6.
  fold usp in MU6, FR6, GAP6, Hc6'. fold usp1 in GAP6, ST6, Hc6'.
  assert (ART6 : ART RT Σ2 m6).
  { apply (af_frame RT AF Σ2 m5 m6 usp1 ART5 ltac:(rewrite SP2, SP1; unfold usp1; lia)); [| exact WM6].
    intros a Ha. apply MU6. cbn [outside]. split; [| split; [| exact I]]; intros Hin; apply Ha.
    - apply (acl_frame _ _ _ f 0%nat); [exact INF2 | change (fs_size 0) with 64; lia].
    - apply (acl_fshadow _ _ _ f 0%nat); [exact INF2 | change (fs_size 0) with 64; rewrite SHF; unfold shad, SHB; lia]. }
  (* [comment removed for export] *)
  destruct (af_frame_release RT AF Σ2 m6 f 0%nat (rt_frames RT Σ) ART6 ltac:(rewrite FRS2; exact FRS1)) as (Σ3 & flg & FLC & NAC & FL0 & FLW & FW & REL).
  change (fs_size 0) with 64 in FW. replace (f + 64 - 8) with (f + 56) in FW by lia. rewrite SP2, SP1 in FLW.
  (* [comment removed for export] *)
  pose proof (se_s3_walk ra1 ra sp gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 g0 g1 g2 g3 g4 g5 g6 g7 (Z_to_bv 64 0) a1 a0 s8 s9 s10 s11 w3 w4 w5 w6
                s0 s1 s2 s3 s4 s5 s6 s7 a3 a4 a5 a6 a7 F5 fc5 m6 f flg lo pd j0 j
                HP ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia)
                F0 ltac:(lia) FL0 ltac:(clear - FLW LOW; lia) ST6 GAP6 FR6 FW FLC MI6) as W4.
  fold usp usp1 in W4.
  cl_lift W4 Hc6' c7 Hc7.
  destruct (ASTA_unpack RT Σ2 _ _ c7 Hc7) as (ms7 & (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & m7 & -> & MU7 & WM7 & MI7 & ST7 & FLC7) & Hc7'). clear Hc7.
  fold usp in ST7.
  destruct (REL m7 MU7 WM7 FLC7) as (ART7 & FRS3 & LV3 & SP3 & CR3 & AL3 & AM3 & CG3).
  (* [comment removed for export] *)
  assert (NFL : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) usp x -> x <> flg).
  { intros x Hx Ex. subst x. destruct Hx as [H|H]; [unfold USTACK_TOP, RT_STACK, STACK_WIN in *; clear - H FLW NUM; lia|].
    apply NAC. right. rewrite LV2, LV1, FRS2, FRS1.
    destruct H as [H|[H|[H|H]]]; [left; exact H | right; left; exact H
      | right; right; left; destruct H as (f' & k' & Hin & R); exists f', k'; split; [right; exact Hin | exact R]
      | right; right; right; destruct H as (f' & k' & Hin & R); exists f', k'; split; [right; exact Hin | exact R]]. }
  apply Hk. exists Σ3, e2, (Z_to_bv 64 flg), buf'.
  split; [| split; [rewrite LV3, LV2; exact LV1 | split; [exact FRS3 | split; [rewrite SP3, SP2; exact SP1 | split; [rewrite CR3, CR2, CR1; lia | rewrite CG3, CG2; exact CG1]]]]].
  eapply ASTA_conseq; [exact (ASTA_switch RT Σ2 Σ3 PMc _ c7 Hc7' AL3 AM3)|]. intros ms <-. exists m7.
  split; [exists y0, y1, y2, h1, h2, h3, h4, h5, h6, h7, y3, y4, y5, y6, F5, fc5; reflexivity|].
  split; [split; [exact ART7 | split; [exact MI7 | split; [exact (wmono_trans asegs _ _ _ WM04 (wmono_trans asegs _ _ _ WM5 (wmono_trans asegs _ _ _ WM6 WM7))) | exact ST7]]]|].
  (* [comment removed for export] *)
  assert (A47 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> m7 x = m5 x).
  { intros x Hx.
    destruct (newframe_apart RT AF Σ Σ1 m2 f 0%nat usp _ ART2 FRS1 LV1 SP1 ltac:(lia) Hx) as (N1 & N2).
    change (fs_size 0) with 64 in N1, N2. rewrite SHF in N2. unfold shad, SHB in N2.
    rewrite (MU7 x ltac:(cbn [outside]; split; [pose proof (NFL _ Hx); lia | exact I])).
    apply MU6. cbn [outside]. clear - N1 N2. lia. }
  split.
  { intros x Hx Ho. rewrite (A47 x Hx).
    rewrite (PRES5 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [rewrite LV1; auto | rewrite FRS1; intros e' He'; right; exact He' | unfold usp1; lia]) Ho).
    apply A04; [exact Hx|]. destruct (cl_split RT AF Σ m usp 144 _ ART0 ltac:(lia) ltac:(lia) Hx) as [Hi|Lo]; [right; exact Hi | left; exact Lo]. }
  split.
  { apply (err_env_agree m5 m7 _ _ _ _ _ _ _ _ _ _ _ ENV5); [| exact (wmono_trans asegs _ _ _ WM6 WM7)].
    pose proof ENV5 as (_ & _ & (_ & _ & HK & _)).
    intros a n H x Hx. cbv beta in Hx. apply A47.
    destruct H as [H|[H|[H|[H|[H|H]]]]].
    1-3: right; left; apply client_static_intro; unfold ERRNO_A in H; lia.
    - apply (acl_live _ _ _ MK 72); [exact INM | lia].
    - apply (acl_live _ _ _ SA 32); [exact INS | lia].
    - apply (acl_live _ _ _ NODES 128); [exact INN | lia]. }
  apply (es_rep_agree m5 m7 _ _ _ _ _ _ _ _ _ ES5); [| exact (wmono_trans asegs _ _ _ WM6 WM7)].
  intros x Hx. cbv beta in Hx. apply A47. apply (acl_live _ _ _ E 904); [exact INE | lia].
Qed.
End CSe.
