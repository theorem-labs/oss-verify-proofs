(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Malloc Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import LhPure LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_T_once Th_mutex Fz_T_lock Fz_I1_img Fz_I1_hash Fz_I1_defs Fz_I1_getrn Fz_I1_retrieve Fz_I1_insert Fz_I1_loadw Fz_I1_errload Fz_I1_getitem Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation z64 := (Z_to_bv 64 0) (only parsing).

Definition e_reason : Z := 0x1fef74.
Definition SITE_ers_smalloc : Z := 0x1fefd4.     (* [comment removed for export] *)
Definition SITE_ers_once : Z := 0x1ff070.        (* [comment removed for export] *)
Definition SITE_ers_igi1 : Z := 0x1ff0ac.        (* [comment removed for export] *)
Definition SITE_ers_igi2 : Z := 0x1ff0c4.        (* [comment removed for export] *)
Definition ERS_FOUND : Z := 0x1ff0c8.            (* [comment removed for export] *)
Definition ERS_EXIT : Z := 0x1ff0e0.             (* [comment removed for export] *)
Definition ERS_RELEASE : Z := 0x1ff120.          (* [comment removed for export] *)
Definition ERS_MAGIC : Z := 0x41b58ab3.
Definition ERS_RETIRED : Z := 0x45e0360e.

(* [comment removed for export] *)
Definition ers_w0_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (e : Z) (F : bvmap 5 word) (fc : bv 32)
    (lo pad : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a1' a2' : word) (j16 : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_ers_smalloc) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
                 (Z_to_bv 64 64) a1' a2' a3 a4 a5 a6 a7 s2 (Z_to_bv 64 e) s4 s5 s6 (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (e_stack_malloc 0)) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -96) [C8 (Z_to_bv 64 0); CB 16 j16; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk asegs m' (bv_unsigned sp + -96 - pad) (bv_unsigned sp + -96)
    /\ stk asegs m' lo (bv_unsigned sp + -96 - pad).

Lemma ers_w0 : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo pad e : Z),
  (pad = 0 \/ pad = 16) -> bv_unsigned sp mod 32 = pad -> 0 <= e < 2^64 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 112 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  ro_cells asegs m g_detect_stack_use_after_return [C4 (Z_to_bv 64 1)] -> mem_inv asegs m ->
  evt asegs (ers_w0_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 e F fc lo pad m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_reason) fc None m (seg_rom asegs)).
Proof.
  intros until e. intros HP HPM HE ST HLO HLOS SPH UT SHC UAR MI. unfold e_reason, g_shadow_memory_dynamic_address, g_detect_stack_use_after_return in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 96, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 96, SP)]) by ut_fp_lia.
  carve_frame 96%nat ST.
  zstep. zstep; lfix. do 10 zstep. zstep.
  rewrite (land_m32_pad (SP + -96) pad) by (first [lia | replace (SP + -96) with (SP + (-3) * 32) by lia; rewrite Z.mod_add by lia; exact HPM]).
  zstep. zstep.
  do 2 zstep. zstep. zstep. zstep. zstep. zstep. if_false. do 2 zstep.
  destruct (stk_split asegs _ lo (SP + -96 - pad) (SP + -96) ST ltac:(lia)) as [ST1 GAP].
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold ers_w0_post, SITE_ers_smalloc, e_stack_malloc. apply evt_done. do 4 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [eassumption|]. split; [exact GAP| exact ST1].
Qed.

(* [comment removed for export] *)
Definition ers_w1_post (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s4 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' : word) (f e lo pad : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (j24 fr : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_ers_once) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
                 (Z_to_bv 64 G_ERR_ONCE) (Z_to_bv 64 e_do_esi) (Z_to_bv 64 e_reason) a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 e) s4 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000)
                 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_T_run_once) fc None m' (seg_rom asegs)
    /\ munch [(f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (bv_unsigned sp - 96, bv_unsigned sp - 72)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -96) [CB 24 j24; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0]
    /\ rw_cells asegs m' f [C8 (Z_to_bv 64 ERS_MAGIC); C8 (Z_to_bv 64 0x17ece); C8 (Z_to_bv 64 e_reason); CB 32 fr]
    /\ rw_cells asegs m' (f / 8 + 2147450880) [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))]
    /\ stk asegs m' (bv_unsigned sp + -96 - pad) (bv_unsigned sp + -96)
    /\ stk asegs m' lo (bv_unsigned sp + -96 - pad).

Lemma ers_w1 : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' : word) (F : bvmap 5 word) fc (m : mem) (f e lo pad : Z) (fj sj j16 : list byte),
  (pad = 0 \/ pad = 16) -> 0 < f -> f mod 64 = 0 -> 0xbc6000 <= f -> f + 64 <= lo -> (f + 64 <= 0x7fff8000 \/ 0x10007fff8000 <= f) -> 0 <= e < 2^64 ->
  lo <= bv_unsigned sp - 128 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m (bv_unsigned sp + -96) [C8 (Z_to_bv 64 0); CB 16 j16; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0] ->
  stk asegs m (bv_unsigned sp + -96 - pad) (bv_unsigned sp + -96) -> stk asegs m lo (bv_unsigned sp + -96 - pad) ->
  rw_cells asegs m f [CB 56 fj] -> rw_cells asegs m (f / 8 + 2147450880) [CB 8 sj] ->
  mem_inv asegs m ->
  evt asegs (ers_w1_post sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s4 s8 s9 s10 s11 t3 t4 t5 t6 F fc ra0 s0' s1' s2' s3' s4' s5' s6' s7' f e lo pad m)
    (MS (mkR (Z_to_bv 64 SITE_ers_smalloc) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
             (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 e) s4 s5 s6 (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_ers_smalloc) fc None m (seg_rom asegs)).
Proof.
  intros until j16. intros HP F0 F64 FIMG FLO FSH HE HLO HLOS SPH UT SHC FR GAP ST FB SB MI.
  unfold SITE_ers_smalloc, g_shadow_memory_dynamic_address in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (SP - 96, SP - 72)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 8 <= 0x10007fff8000).
  { pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)). assert (f / 8 + 8 <= 2^44) by (Z.div_mod_to_equations; lia). lia. }
  assert (HWU : ut_fp [(f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (SP - 96, SP - 72)]) by (clear - F0 FIMG SHR HLO HLOS SPH FLO; ut_fp_lia).
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  pose proof (div8_facts f) as Q1.
  zstep. zstep. zstep. zstep. if_true.
  (* [comment removed for export] *)
  destruct HP as [-> | ->].
  1: replace (SP + -96 - 0) with (SP + -96) in * by lia.
  2: replace (SP + -96 - 16) with (SP + -112) in * by lia.
  all: zstep.
  all: do 3 zstep; zstep; rewrite (shr3_div f) by lia; do 3 zstep.
  all: (zstep; lfix); (zstep; lfix); (zstep; lfix).
  all: zstep; zstep; (zstep; lfix); (zstep; lfix); (zstep; lfix); (zstep; lfix).
  all: zstep; (zstep; lfix); (zstep; lfix); (zstep; lfix); (zstep; lfix).
  all: do 4 zstep; zstep.
  1: pose proof (rw_cells_blur _ _ [_; _; _] _ FR) as FRB. 2: pose proof (rw_cells_blur _ _ [_; _] _ FR) as FRB.
  all: cbn [cells_size csize Nat.add app cells_bytes cbytes] in FRB.
  all: subst SP; rewrite ?Z_to_bv_bv_unsigned.
  all: unfold ers_w1_post, SITE_ers_once, e_T_run_once, G_ERR_ONCE, e_do_esi, ERS_MAGIC, e_reason.
  all: try replace (bv_unsigned sp + -96 - 0) with (bv_unsigned sp + -96) by lia.
  all: try replace (bv_unsigned sp + -96 - 16) with (bv_unsigned sp + -112) by lia.
  all: apply evt_done; do 3 eexists; split; [reflexivity|].
  all: split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [exact FRB|]; split; [eassumption|]; split; [eassumption|]; split; assumption.
Qed.

(* [comment removed for export] *)
Lemma ers_w2a : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (f e lo pad : Z),
  0 <= e < 2^64 -> Z.land e 2147483648 <> 0 ->
  stk asegs m lo (bv_unsigned sp + -96 - pad) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 128 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR (Z_to_bv 64 SITE_ers_once) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
                                   (Z_to_bv 64 0) (Z_to_bv 64 2147483647) (Z_to_bv 64 (Z.land e 2147483648)) a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 e) s4 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000)
                                   s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 ERS_EXIT) fc None m (seg_rom asegs))
    (MS (mkR (Z_to_bv 64 SITE_ers_once) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 e) s4 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000)
             s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_ers_once) fc None m (seg_rom asegs)).
Proof.
  intros until pad. intros HE HB ST LO0 LO HTOP MI. unfold SITE_ers_once in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  zstep. th_if_lit.
  do 5 zstep. zstep. if_cases K; zify_cond K.
  - apply evt_done. unfold ERS_EXIT. cbv delta [mkR]. reflexivity.
  - exfalso. apply HB. exact K.
Qed.

(* [comment removed for export] *)
Definition ers_w2b_post (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (f e pad : Z) (fr : list byte) (m : mem) : machine_state -> Prop :=
  fun ms => exists m' : mem,
    ms = MS (mkR (Z_to_bv 64 SITE_ers_igi1) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
                 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 2147483647) (Z_to_bv 64 1) a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 e) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000)
                 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_get_item) fc None m' (seg_rom asegs)
    /\ munch [(f + 32, f + 40)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' f [C8 (Z_to_bv 64 ERS_MAGIC); C8 (Z_to_bv 64 0x17ece); C8 (Z_to_bv 64 e_reason); CB 8 (firstn 8 fr); C8 (Z_to_bv 64 (Z.land e 2147483647)); CB 16 (skipn 16 fr)].

Lemma ers_w2b : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (f e lo pad : Z) (fr : list byte),
  0 <= e < 2^64 -> Z.land e 2147483648 = 0 -> 0 < f -> 0xbc6000 <= f -> f + 64 <= lo -> (f + 64 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  rw_cells asegs m f [C8 (Z_to_bv 64 ERS_MAGIC); C8 (Z_to_bv 64 0x17ece); C8 (Z_to_bv 64 e_reason); CB 32 fr] ->
  rw_cells asegs m G_ERR_FLAG [C4 (Z_to_bv 64 1)] -> img_untouched m ->
  stk asegs m lo (bv_unsigned sp + -96 - pad) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 128 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (ers_w2b_post sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 F fc f e pad fr m)
    (MS (mkR (Z_to_bv 64 SITE_ers_once) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 e) s4 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000)
             s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_ers_once) fc None m (seg_rom asegs)).
Proof.
  intros until fr. intros HE HB F0 FIMG FLO FSH FB FLC UT ST LO0 LO HTOP MI. unfold SITE_ers_once, ERS_MAGIC, e_reason in *. unfold G_ERR_FLAG in FLC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  pose proof (munch_refl [(f + 32, f + 40)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(f + 32, f + 40)]) by (clear - F0 FIMG FLO LO0; ut_fp_lia).
  assert (HWS : sh_fp [(f + 32, f + 40)]) by (clear - F0 FIMG FSH FLO LO0; sh_fp_lia).
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  zstep. th_if_lit.
  do 5 zstep. zstep. if_cases K; zify_cond K.
  - exfalso. apply K. exact HB.
  - zstep. zstep. zstep. th_if_lit.
    zstep. zstep. zstep. zstep. zstep.
    apply evt_done. unfold ers_w2b_post, SITE_ers_igi1, e_get_item, ERS_MAGIC, e_reason. eexists. split; [cbv delta [mkR]; reflexivity|].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. eassumption.
Qed.

(* [comment removed for export] *)
Lemma ers_w3a : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (f e lo pad v1 : Z),
  0 < v1 < 2^64 ->
  stk asegs m lo (bv_unsigned sp + -96 - pad) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 128 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR (Z_to_bv 64 SITE_ers_igi1) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
                                   (Z_to_bv 64 v1) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 e) s4 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000)
                                   s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 ERS_FOUND) fc None m (seg_rom asegs))
    (MS (mkR (Z_to_bv 64 SITE_ers_igi1) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
             (Z_to_bv 64 v1) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 e) s4 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000)
             s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_ers_igi1) fc None m (seg_rom asegs)).
Proof.
  intros until v1. intros HV ST LO0 LO HTOP MI. unfold SITE_ers_igi1 in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  zstep. if_cases K; zify_cond K.
  - apply evt_done. unfold ERS_FOUND. cbv delta [mkR]. reflexivity.
  - exfalso. rewrite ?unsigned_lit in K by lia. lia.
Qed.

(* [comment removed for export] *)
Definition ers_w3b_post (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (f e pad : Z) (j8 j16 : list byte) (m : mem) : machine_state -> Prop :=
  fun ms => exists m' : mem,
    ms = MS (mkR (Z_to_bv 64 SITE_ers_igi2) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
                 (Z_to_bv 64 (f + 32)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 (Z.shiftl e 41)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000)
                 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_get_item) fc None m' (seg_rom asegs)
    /\ munch [(f + 32, f + 40)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' f [C8 (Z_to_bv 64 ERS_MAGIC); C8 (Z_to_bv 64 0x17ece); C8 (Z_to_bv 64 e_reason); CB 8 j8; C8 (Z_to_bv 64 (Z.land e 8388607)); CB 16 j16].

Lemma ers_w3b : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (f e lo pad : Z) (j8 j16 : list byte) (d0 : word),
  0 <= e < 2^64 -> 0 < f -> 0xbc6000 <= f -> f + 64 <= lo -> (f + 64 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  rw_cells asegs m f [C8 (Z_to_bv 64 ERS_MAGIC); C8 (Z_to_bv 64 0x17ece); C8 (Z_to_bv 64 e_reason); CB 8 j8; C8 d0; CB 16 j16] -> img_untouched m ->
  stk asegs m lo (bv_unsigned sp + -96 - pad) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 128 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (ers_w3b_post sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 F fc f e pad j8 j16 m)
    (MS (mkR (Z_to_bv 64 SITE_ers_igi1) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
             (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 e) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000)
             s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_ers_igi1) fc None m (seg_rom asegs)).
Proof.
  intros until d0. intros HE F0 FIMG FLO FSH FB UT ST LO0 LO HTOP MI. unfold SITE_ers_igi1, ERS_MAGIC, e_reason in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  pose proof (munch_refl [(f + 32, f + 40)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(f + 32, f + 40)]) by (clear - F0 FIMG FLO LO0; ut_fp_lia).
  assert (HWS : sh_fp [(f + 32, f + 40)]) by (clear - F0 FIMG FSH FLO LO0; sh_fp_lia).
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  zstep. th_if_lit.
  zstep. zstep. zstep. zstep. zstep.
  apply evt_done. unfold ers_w3b_post, SITE_ers_igi2, e_get_item, ERS_MAGIC, e_reason. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. eassumption.
Qed.

(* [comment removed for export] *)
Lemma ers_w4 : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (f lo pad v2 : Z),
  0 <= v2 < 2^64 ->
  stk asegs m lo (bv_unsigned sp + -96 - pad) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 128 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR (Z_to_bv 64 SITE_ers_igi2) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
                                   (Z_to_bv 64 v2) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) s3 s4 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000)
                                   s8 s9 s10 s11 t3 t4 t5 t6)
                              F (if v2 =? 0 then Z_to_bv 64 ERS_EXIT else Z_to_bv 64 ERS_FOUND) fc None m (seg_rom asegs))
    (MS (mkR (Z_to_bv 64 SITE_ers_igi2) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
             (Z_to_bv 64 v2) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) s3 s4 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000)
             s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_ers_igi2) fc None m (seg_rom asegs)).
Proof.
  intros until v2. intros HV ST LO0 LO HTOP MI. unfold SITE_ers_igi2 in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  zstep. if_cases K; zify_cond K.
  - apply evt_done. unfold ERS_EXIT. rewrite ?unsigned_lit in K by lia. rewrite (proj2 (Z.eqb_eq v2 0) K). cbv delta [mkR]. reflexivity.
  - apply evt_done. unfold ERS_FOUND. rewrite ?unsigned_lit in K by lia. rewrite (proj2 (Z.eqb_neq v2 0) K). cbv delta [mkR]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ers_wf : forall rax sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (f lo pad v : Z) (sw : word),
  0 < v -> v mod 8 = 0 -> v + 16 <= SEGTOP_A -> acc asegs m v 16 -> ro_cells asegs m (v + 8) [C8 sw] ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  stk asegs m lo (bv_unsigned sp + -96 - pad) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 128 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists a1' : word, ms = MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
                                   sw a1' a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) s3 s4 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000)
                                   s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 ERS_EXIT) fc None m (seg_rom asegs))
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
             (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) s3 s4 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000)
             s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ERS_FOUND) fc None m (seg_rom asegs)).
Proof.
  intros until sw. intros HV VAL VHI ACC SC UT SHC ST LO0 LO HTOP MI. unfold ERS_FOUND, g_shadow_memory_dynamic_address, SEGTOP_A in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep. zstep. th_if_lit. zstep.
  apply evt_done. unfold ERS_EXIT. eexists. cbv delta [mkR]. reflexivity.
Qed.

(* [comment removed for export] *)
Definition ers_wxa_post (rax sp gp tp t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s3 s4 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (f pad : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists m' : mem,
    ms = MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
                 a0 (Z_to_bv 64 (-11)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) s3 s4 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000)
                 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ERS_RELEASE) fc None m' (seg_rom asegs)
    /\ munch [(f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'.

Lemma ers_wxa : forall sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (rax : word) (f lo pad : Z) (x0 : word)
    (b0 b1 b2 b3 b4 b5 b6 b7 : byte),
  0 < f -> f mod 64 = 0 -> 0xbc6000 <= f -> f + 64 <= lo -> (f + 64 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  rw_cells asegs m f [C8 x0] -> rw_cells asegs m (f / 8 + 2147450880) [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7] -> img_untouched m ->
  stk asegs m lo (bv_unsigned sp + -96 - pad) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 128 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (ers_wxa_post rax sp gp tp t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s3 s4 s8 s9 s10 s11 t3 t4 t5 t6 F fc f pad m)
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) s3 s4 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000)
             s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ERS_EXIT) fc None m (seg_rom asegs)).
Proof.
  intros until b7. intros F0 F64 FIMG FLO FSH FB SB UT ST LO0 LO HTOP MI. unfold ERS_EXIT in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  pose proof (munch_refl [(f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 8 <= 0x10007fff8000).
  { pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)). assert (f / 8 + 8 <= 2^44) by (Z.div_mod_to_equations; lia). lia. }
  assert (HWU : ut_fp [(f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 8)]) by (clear - F0 FIMG SHR FLO LO0; ut_fp_lia).
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  pose proof (div8_facts f) as Q1.
  zstep. (zstep; lfix). (zstep; lfix). zstep. zstep. (zstep; lfix).
  zstep. ifF. zstep. do 8 (zstep; lfix).
  apply evt_done. unfold ers_wxa_post, ERS_RELEASE. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [assumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
Definition ers_wxb_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 a0 a2 a3 a4 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32)
    (fl lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' a0 (Z_to_bv 64 fl) a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(fl, fl + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' fl [C1 (Z_to_bv 8 0)].

Lemma ers_wxb : forall sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s8 s9 s10 s11 t3 t4 t5 t6
    (rax ra0 s0' s1' s2' s3' s4' s5' s6' s7' : word) (F : bvmap 5 word) fc (m : mem) (f fl lo pad : Z) (j24 : list byte),
  (pad = 0 \/ pad = 16) -> lo <= bv_unsigned sp - 128 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  0 < f -> f + 64 <= lo -> 0 < fl -> fl + 1 <= lo ->
  stk asegs m lo (bv_unsigned sp + -96 - pad) -> stk asegs m (bv_unsigned sp + -96 - pad) (bv_unsigned sp + -96) ->
  rw_cells asegs m (bv_unsigned sp + -96) [CB 24 j24; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0] ->
  ro_cells asegs m (f + 56) [C8 (Z_to_bv 64 fl)] -> rw_cells asegs m fl [C1 (Z_to_bv 8 1)] -> mem_inv asegs m ->
  evt asegs (ers_wxb_post ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 a0 a2 a3 a4 a5 a6 a7 F fc fl lo m)
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) s3 s4 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000)
             s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ERS_RELEASE) fc None m (seg_rom asegs)).
Proof.
  intros until j24. intros HP HLO HLOS SPH F0 FLO FL0 FLLO ST1 GAP FR FLG FLB MI. unfold ERS_RELEASE in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EUfl : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply unsigned_lit; lia).
  zstep. clear FLG.
  zstep; lfix.
  zstep. zstep.
  do 9 zstep.
  pose proof (stk_merge asegs _ lo (SP + -96 - pad) (SP + -96) ST1 GAP ltac:(lia)) as ST2.
  zstep. release_frame FR ST2 SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold ers_wxb_post. apply evt_done. do 8 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption| assumption].
Qed.

Section Reason.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis SM0 : stack_malloc_contract RT 0.
Hypothesis C_IGI : igi_stmt RT GOBJ.

(* [comment removed for export] *)
Definition ers_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (L REST : list (Z * Z)) (lh B : Z) (g : lh_geo) (bks : list (list (bptr * Z))) (LK e : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 e -> tp = Z_to_bv 64 0xba3ef0 -> 0 <= e < 2^64 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 288 <= bv_unsigned sp ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  err_statics m LK lh -> In (LK, 40) REST -> LK mod 4 = 0 -> rw_cells asegs m LK (mutex_cells z64 z64) ->
  lh_repE GOBJ m L lh B g bks -> Permutation (rt_live RT Σ) (L ++ REST) -> Forall (fun x => 0 < snd x) REST ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_reason m)))
    (fun c => exists (Σ' : rts RT) (v : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
           /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp REST (rt_frames RT Σ) (bv_unsigned sp) [(LK + 4, LK + 8)] m m'
           /\ lh_repE GOBJ m' L lh B g bks /\ rw_cells asegs m' LK (mutex_cells z64 z64) /\ err_statics m' LK lh) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - 1 /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem ers_cps : ers_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo L REST lh B g bks LK e
    FDO MST -> -> HE ART0 MI0 CALL HSTK Hfr Hcr (ONC & FLC & LKC & LHC) INLK AL4 MC REPE PERM RPOS.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  set (pad := usp mod 32).
  assert (HP : pad = 0 \/ pad = 16) by (unfold pad; clear - SPA; Z.div_mod_to_equations; lia).
  assert (HPM : usp mod 32 = pad) by reflexivity. clearbody pad.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 288 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP /\ SEGTOP_A <= lo) by (unfold RT_STACK, STACK_WIN, USTACK_TOP, SEGTOP_A in *; lia).
  set (usp1 := usp + -96 - pad).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & UAR & UT).
  unfold G_ERR_ONCE in ONC. unfold G_ERR_FLAG in FLC. unfold G_ERR_LOCK in LKC. unfold G_ERR_HASH in LHC.
  assert (INR : forall x, In x REST -> In x (rt_live RT Σ)) by (intros x Hx; eapply Permutation_in; [apply Permutation_sym; exact PERM| apply in_or_app; right; exact Hx]).
  assert (INL : forall x, In x L -> In x (rt_live RT Σ)) by (intros x Hx; eapply Permutation_in; [apply Permutation_sym; exact PERM| apply in_or_app; left; exact Hx]).
  pose proof (af_live_range RT AF Σ m LK 40 ART0 (INR _ INLK)) as (LK0 & LKLO & _). pose proof (afp_live_hi RT GOBJ AFP Σ m LK 40 ART0 (INR _ INLK) ltac:(lia)) as LKHI.
  destruct REPE as (REP & PERML & ALN). pose proof (lh_geo_bounds g (proj1 REP)) as GB.
  assert (INLH : In (lh, 104) (rt_live RT Σ)) by (apply INL; eapply Permutation_in; [apply Permutation_sym; exact PERML| left; reflexivity]).
  assert (INB : In (B, 8 * g_na g) (rt_live RT Σ)) by (apply INL; eapply Permutation_in; [apply Permutation_sym; exact PERML| right; left; reflexivity]).
  pose proof (af_live_range RT AF Σ m lh 104 ART0 INLH) as (L0 & LLO & _). pose proof (afp_live_hi RT GOBJ AFP Σ m lh 104 ART0 INLH ltac:(lia)) as LHI.
  pose proof (af_live_range RT AF Σ m B (8 * g_na g) ART0 INB) as (B0 & BLO & _). pose proof (afp_live_hi RT GOBJ AFP Σ m B (8 * g_na g) ART0 INB ltac:(lia)) as BHI.
  assert (NODESF : forall q A, In (q, A) (concat bks) -> In (A, 24) L /\ A + 24 <= rt_sp0 RT Σ - STACK_WIN /\ 0x10007fff8000 <= A /\ (A + 24 <= LK \/ LK + 40 <= A)).
  { intros q A Hq. destruct (lh_rep_owned asegs LH_CEIL _ _ _ _ _ _ _ _ _ _ _ REP q A Hq) as [O _].
    pose proof (af_live_range RT AF Σ m A 24 ART0 (INL _ O)) as (_ & R1 & _). pose proof (afp_live_hi RT GOBJ AFP Σ m A 24 ART0 (INL _ O) ltac:(lia)) as R2.
    split; [exact O|]. split; [lia|]. split; [exact R2|]. exact (lrest_apart RT AF Σ m L REST A 24 LK 40 ART0 PERM O INLK ltac:(lia) ltac:(lia)). }
  pose proof (lrest_apart RT AF Σ m L REST lh 104 LK 40 ART0 PERM ltac:(eapply Permutation_in; [apply Permutation_sym; exact PERML| left; reflexivity]) INLK ltac:(lia) ltac:(lia)) as APLH.
  pose proof (lrest_apart RT AF Σ m L REST B (8 * g_na g) LK 40 ART0 PERM ltac:(eapply Permutation_in; [apply Permutation_sym; exact PERML| right; left; reflexivity]) INLK ltac:(lia) ltac:(lia)) as APB.
  (* [comment removed for export] *)
  assert (REPK : forall (ma mb : mem) W, lh_rep asegs LH_CEIL (DVerr GOBJ) ma (ownL L) ERR_FNS_A lh (bp lh) (bp B) B (8 * g_na g) g bks -> munch W ma mb -> wmono asegs ma mb ->
            (forall x, lh <= x < lh + 104 -> outside W x) -> (forall x, B <= x < B + 8 * g_na g -> outside W x) ->
            (forall q A x, In (q, A) (concat bks) -> A <= x < A + 24 -> outside W x) ->
            lh_rep asegs LH_CEIL (DVerr GOBJ) mb (ownL L) ERR_FNS_A lh (bp lh) (bp B) B (8 * g_na g) g bks).
  { intros ma mb W R MUx WMx O1 O2 O3. eapply lh_rep_agree; [exact R| | intros ? ? ? ? _ X; exact X].
    eapply LhRep.agree_on_mono; [exact (LhRep.agree_on_of_munch asegs _ _ _ MUx WMx)|].
    intros a [Ha|[Ha|(q & A & Hq & Ha)]]; [exact (O1 _ Ha)| exact (O2 _ Ha)| exact (O3 q A a Hq Ha)]. }
  (* [comment removed for export] *)
  pose proof (ers_w0 ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pad e
                HP HPM HE ST ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia) UT SHC UAR MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (a1' & a2' & j16 & m1 & -> & MU1 & WM1 & MI1 & FR1 & GAP1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, GAP1, ST1, Hc1'. fold usp1 in GAP1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 96 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 96 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  (* [comment removed for export] *)
  apply (SM0 Σ PMc (Z_to_bv 64 SITE_ers_smalloc) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 64) a1' a2' a3 a4 a5 a6 a7
           s2 (Z_to_bv 64 e) s4 s5 s6 (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo FDO MST ltac:(left; reflexivity) eq_refl Hfr Hcr ART1 MI1).
  { unfold call_ok. rewrite EU1. split; [exact ST1|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|].
    fold usp in SPA. clear - SPA HP HPM. Z.div_mod_to_equations. lia. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & f & Hc2 & FRS1 & LV1 & SP1 & CR1 & F0 & F64 & FU & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WF2 & WS2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_ers_smalloc) in Hc2' by (unfold SITE_ers_smalloc; lia).
  assert (INF : In (f, 0%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  pose proof (af_frames_range RT AF Σ1 m2 f 0%nat ART2 INF) as (_ & FLO & _ & FAP).
  pose proof (af_frames_align RT AF Σ1 m2 f 0%nat ART2 INF) as (_ & FIMG).
  pose proof (af_frames_hi RT AF Σ1 m2 f 0%nat ART2 INF) as FSH.
  rewrite SP1 in FLO. change (fs_size 0) with 64 in FLO, FSH, FU, WF2, WS2, FAP. change (64 - 8) with 56 in WF2. change (64 / 8) with 8 in WS2.
  unfold shad, SHB in WS2. unfold SEGTOP_A in FIMG. rewrite LV1 in FAP.
  assert (AG2 : forall a k, usp1 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m1 m2).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES2. left. lia. }
  cl_keep FR1 AG2 WM2 FR2.
  assert (GAP2 : stk asegs m2 usp1 (usp + -96)).
  { apply (stk_agree_nw asegs m1 m2 _ _ GAP1). intros x Hx. cbv beta in Hx. apply PRES2. left. unfold USTACK_TOP in *. lia. }
  destruct (wr_at_rw_CB m2 f 56 WF2 ltac:(lia)) as (fj & FB2). destruct (wr_at_rw_CB m2 (f / 8 + 2147450880) 8 WS2 ltac:(lia)) as (sj & SB2).
  change (Z.to_nat 56) with 56%nat in FB2. change (Z.to_nat 8) with 8%nat in SB2.
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & SHC2 & _ & _ & UT2).
  assert (WM02 : wmono asegs m m2) by exact (wmono_trans asegs _ _ _ WM1 WM2).
  (* [comment removed for export] *)
  assert (PR2 : rt_pres_fp REST (rt_frames RT Σ) usp [(LK + 4, LK + 8)] m m2).
  { intros a Ha Ho. rewrite (PRES2 a ltac:(apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact INR| intros ? X; exact X| unfold usp1; lia])). exact (PR1 a ltac:(apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact INR| intros ? X; exact X| lia]) I). }
  assert (STAT2 : forall a cs, rw_cells asegs m a cs -> 0xb9f7e0 <= a -> a + Z.of_nat (cells_size cs) <= 0xb9f860 -> rw_cells asegs m2 a cs).
  { intros a cs H H1 H2. apply (rw_cells_agree asegs m m2 _ _ H); [| exact WM02]. intros x Hx. cbv beta in Hx.
    rewrite (PRES2 x ltac:(right; left; apply client_static_intro; lia)). apply PR1; [right; left; apply client_static_intro; lia| exact I]. }
  pose proof (STAT2 _ _ ONC ltac:(lia) ltac:(cbn; lia)) as ONC2. pose proof (STAT2 _ _ FLC ltac:(lia) ltac:(cbn; lia)) as FLC2.
  pose proof (STAT2 _ _ LKC ltac:(lia) ltac:(cbn; lia)) as LKC2. pose proof (STAT2 _ _ LHC ltac:(lia) ltac:(cbn; lia)) as LHC2.
  assert (MC2 : rw_cells asegs m2 LK (mutex_cells z64 z64)).
  { apply (rw_cells_agree asegs m m2 _ _ MC); [| exact WM02]. intros x Hx. cbn [cells_size csize Nat.add mutex_cells] in Hx.
    assert (Hx' : aclient REST (rt_frames RT Σ) usp (bv_unsigned x)) by (right; right; left; exists LK, 40; split; [exact INLK| lia]).
    rewrite (PRES2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx'); [exact INR| intros ? X; exact X| unfold usp1, STACK_WIN in *; lia])).
    exact (PR1 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx'); [exact INR| intros ? X; exact X| lia]) I). }
  assert (REP2 : lh_rep asegs LH_CEIL (DVerr GOBJ) m2 (ownL L) ERR_FNS_A lh (bp lh) (bp B) B (8 * g_na g) g bks).
  { eapply lh_rep_agree; [exact REP| | intros ? ? ? ? _ X; exact X]. intros a Ra Ha.
    assert (Ha' : aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
    { destruct Ha as [X|[X|(q & A & Hq & X)]]; right; right; left; [exists lh, 104| exists B, (8 * g_na g)| exists A, 24];
        (split; [| lia]); [exact INLH| exact INB| exact (INL _ (proj1 (NODESF q A Hq)))]. }
    assert (E : m2 (wa a) = m (wa a)); [| split; [exact E| intros Hw; apply WM02; exact Hw]].
    rewrite (PRES2 (wa a) ltac:(unfold wa; rewrite unsigned_lit by lia; apply (aclient_mono _ _ _ _ _ _ _ Ha'); [intros ? X; exact X| intros ? X; exact X| lia])).
    exact (PR1 (wa a) ltac:(unfold wa; rewrite unsigned_lit by lia; exact Ha') I). }
  (* [comment removed for export] *)
  pose proof (ers_w1 sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s2 s4 s5 s6 s8 s9 s10 s11 u3 u4 u5 u6
                ra s0 s1 s2 s3 s4 s5 s6 s7 F2 fc2 m2 f e lo pad fj sj j16 HP F0 F64 FIMG ltac:(lia) ltac:(destruct FSH; [left | right]; lia) HE
                ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia)
                UT2 SHC2 FR2 GAP2 ST2 FB2 SB2 MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (j24 & fr & m3 & -> & MU3 & WM3 & MI3 & FR3 & FB3 & SB3 & GAP3 & ST3) & Hc3'). clear Hc3.
  fold usp in MU3, FR3, GAP3, Hc3'. fold usp1 in GAP3, ST3, Hc3'.
  assert (SHF : shad (f + 64) = shad f + 8) by (replace (f + 64) with (f + 64 * 1) by lia; rewrite (shad_add64 f 1 F64); lia).
  pose proof (div8_facts f) as Q1.
  (* [comment removed for export] *)
  assert (FKEEP : forall (ma mb : mem) W, ART RT Σ1 ma -> munch W ma mb -> wmono asegs ma mb ->
            (forall x, ~ outside W x -> (f <= x < f + 56) \/ (shad f <= x < shad f + 8) \/ (usp - 128 <= x < usp - 72)) ->
            ART RT Σ1 mb /\ (forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> mb a = ma a)).
  { intros ma mb W HAx MUx WMx HW. split.
    - apply (af_frame RT AF Σ1 ma mb (usp - 128) HAx ltac:(rewrite SP1; lia)); [| exact WMx].
      intros a Ha. apply MUx. destruct (outside_dec W (bv_unsigned a)) as [O|O]; [exact O|]. exfalso. apply Ha.
      destruct (HW _ O) as [X|[X|X]].
      + apply (acl_frame _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; lia].
      + apply (acl_fshadow _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; rewrite SHF; lia].
      + apply acl_stack. unfold USTACK_TOP in *. lia.
    - intros a Ha. apply MUx. destruct (outside_dec W (bv_unsigned a)) as [O|O]; [exact O|]. exfalso.
      destruct (newframe_apart RT AF Σ Σ1 m2 f 0%nat usp _ ART2 FRS1 LV1 SP1 ltac:(lia) Ha) as (N1 & N2). change (fs_size 0) with 64 in N1, N2. rewrite SHF in N2.
      pose proof (cl_split RT AF Σ m usp 128 _ ART0 ltac:(lia) ltac:(lia) Ha) as N4.
      destruct (HW _ O) as [X|[X|X]]; lia. }
  destruct (FKEEP m2 m3 _ ART2 MU3 WM3 ltac:(intros x Hx; cbn [outside] in Hx; unfold shad, SHB; lia)) as [ART3 PR3].
  (* [comment removed for export] *)
  assert (CARRY : forall mX : mem, (forall a : word, aclient REST (rt_frames RT Σ) usp (bv_unsigned a) -> ~ (LK + 4 <= bv_unsigned a < LK + 8) -> mX a = m2 a) ->
            rt_pres_fp REST (rt_frames RT Σ) usp [(LK + 4, LK + 8)] m mX
            /\ rw_cells asegs mX G_ERR_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs mX G_ERR_FLAG [C4 (Z_to_bv 64 1)]
            /\ rw_cells asegs mX G_ERR_LOCK [C8 (Z_to_bv 64 LK)] /\ rw_cells asegs mX G_ERR_HASH [C8 (Z_to_bv 64 lh)]).
  { intros mX AGX.
    assert (STATX : forall a cs, rw_cells asegs m2 a cs -> 0xb9f7e0 <= a -> a + Z.of_nat (cells_size cs) <= 0xb9f860 -> rw_cells asegs mX a cs).
    { intros a cs H H1 H2. apply (rw_cells_agree_nw asegs m2 mX _ _ H). intros x Hx. cbv beta in Hx. apply AGX; [right; left; apply client_static_intro; lia| lia]. }
    split. { intros a Ha Ho. cbn [outside] in Ho. rewrite (AGX a Ha ltac:(lia)). exact (PR2 a Ha ltac:(cbn [outside]; exact Ho)). }
    split; [exact (STATX _ _ ONC2 ltac:(lia) ltac:(cbn; lia))|]. split; [exact (STATX _ _ FLC2 ltac:(lia) ltac:(cbn; lia))|].
    split; [exact (STATX _ _ LKC2 ltac:(lia) ltac:(cbn; lia))| exact (STATX _ _ LHC2 ltac:(lia) ltac:(cbn; lia))]. }
  (* [comment removed for export] *)
  assert (LOFF : forall x, (lh <= x < lh + 104 \/ B <= x < B + 8 * g_na g \/ exists q A, In (q, A) (concat bks) /\ A <= x < A + 24) ->
            0x10007fff8000 <= x /\ x < rt_sp0 RT Σ - STACK_WIN /\ ~ (f <= x < f + 64) /\ aclient (rt_live RT Σ) (rt_frames RT Σ) usp x).
  { intros x Hx. destruct Hx as [X|[X|(q & A & Hq & X)]].
    - destruct (FAP lh 104 INLH). all: split; [lia|]; split; [lia|]; split; [lia|]; right; right; left; exists lh, 104; split; [exact INLH| lia].
    - destruct (FAP B (8 * g_na g) INB). all: split; [lia|]; split; [lia|]; split; [lia|]; right; right; left; exists B, (8 * g_na g); split; [exact INB| lia].
    - destruct (NODESF q A Hq) as (O & R1 & R2 & _). destruct (FAP A 24 (INL _ O)). all: split; [lia|]; split; [lia|]; split; [lia|]; right; right; left; exists A, 24; split; [exact (INL _ O)| lia]. }
  assert (REPF : forall (ma mb : mem) W, lh_rep asegs LH_CEIL (DVerr GOBJ) ma (ownL L) ERR_FNS_A lh (bp lh) (bp B) B (8 * g_na g) g bks -> munch W ma mb -> wmono asegs ma mb ->
            (forall x, ~ outside W x -> (f <= x < f + 56) \/ (shad f <= x < shad f + 8) \/ (usp - 288 <= x < usp)) ->
            lh_rep asegs LH_CEIL (DVerr GOBJ) mb (ownL L) ERR_FNS_A lh (bp lh) (bp B) B (8 * g_na g) g bks).
  { intros ma mb W R MUx WMx HW. apply (REPK ma mb W R MUx WMx); intros; (destruct (outside_dec W x) as [O|O]; [exact O| exfalso]);
      [destruct (LOFF x ltac:(left; assumption)) as (Y1 & Y2 & Y3 & _)| destruct (LOFF x ltac:(right; left; assumption)) as (Y1 & Y2 & Y3 & _)
      | destruct (LOFF x ltac:(right; right; exists q, A; split; assumption)) as (Y1 & Y2 & Y3 & _)];
      destruct (HW _ O) as [Z1|[Z1|Z1]]; unfold shad, SHB, USTACK_TOP in *; lia. }
  assert (AG3 : forall a : word, aclient REST (rt_frames RT Σ) usp (bv_unsigned a) -> ~ (LK + 4 <= bv_unsigned a < LK + 8) -> m3 a = m2 a) by (intros a Ha _; exact (PR3 a ltac:(apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact INR| intros ? X; exact X| lia]))).
  destruct (CARRY m3 AG3) as (PRK3 & ONC3 & FLC3 & LKC3 & LHC3).
  pose proof (REPF m2 m3 _ REP2 MU3 WM3 ltac:(intros x Hx; cbn [outside] in Hx; unfold shad, SHB; lia)) as REP3.
  assert (MC3 : rw_cells asegs m3 LK (mutex_cells z64 z64)).
  { apply (rw_cells_agree asegs m2 m3 _ _ MC2); [| exact WM3]. intros x Hx. cbn [cells_size csize Nat.add mutex_cells] in Hx. apply PR3. right; right; left. exists LK, 40. split; [exact (INR _ INLK)| lia]. }
  (* [comment removed for export] *)
  pose proof (T_run_once_done_proof (Z_to_bv 64 SITE_ers_once) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 G_ERR_ONCE) (Z_to_bv 64 e_do_esi) (Z_to_bv 64 e_reason) b3 b4 b5 b6 b7
                (Z_to_bv 64 f) (Z_to_bv 64 e) s4 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m3 lo) as WR.
  rewrite (unsigned_lit G_ERR_ONCE), EU1 in WR by (unfold G_ERR_ONCE; lia). unfold G_ERR_ONCE in WR.
  specialize (WR (proj1 ONC3) ST3 ltac:(lia) ltac:(unfold usp1, RT_STACK in *; lia) ltac:(left; unfold usp1; lia) MI3).
  cl_lift WR Hc3' c4 Hc4.
  destruct (ASTA_unpack RT Σ1 _ _ c4 Hc4) as (ms4 & (a2x & a3x & m4 & -> & MU4 & WM4 & MI4 & ST4 & _) & Hc4'). clear Hc4.
  rewrite (ret_pc_even SITE_ers_once) in Hc4' by (unfold SITE_ers_once; lia).
  destruct (FKEEP m3 m4 _ ART3 MU4 WM4 ltac:(intros x Hx; cbn [outside] in Hx; unfold usp1 in Hx; lia)) as [ART4 PR34].
  assert (WM24 : wmono asegs m2 m4) by exact (wmono_trans asegs _ _ _ WM3 WM4).
  assert (AG4 : forall a : word, aclient REST (rt_frames RT Σ) usp (bv_unsigned a) -> ~ (LK + 4 <= bv_unsigned a < LK + 8) -> m4 a = m2 a) by (intros a Ha Hn; rewrite (PR34 a ltac:(apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact INR| intros ? X; exact X| lia])); exact (AG3 a Ha Hn)).
  destruct (CARRY m4 AG4) as (PRK4 & ONC4 & FLC4 & LKC4 & LHC4).
  pose proof (REPF m3 m4 _ REP3 MU4 WM4 ltac:(intros x Hx; cbn [outside] in Hx; unfold usp1 in Hx; lia)) as REP4.
  assert (OFF34 : forall P : Z -> Prop, (forall x, P x -> ~ (usp1 - 16 <= x < usp1)) -> agree_on P m3 m4) by (intros P HPx a Ha; apply MU4; cbn [outside]; pose proof (HPx _ Ha); split; [lia| exact I]).
  assert (MC4 : rw_cells asegs m4 LK (mutex_cells z64 z64)) by (apply (rw_cells_agree asegs m3 m4 _ _ MC3); [apply OFF34; cbn [cells_size csize Nat.add mutex_cells]; unfold usp1, STACK_WIN in *; intros; lia| exact WM4]).
  eassert (FR4 : rw_cells asegs m4 (usp + -96) _) by (apply (rw_cells_agree asegs m3 m4 _ _ FR3); [apply OFF34; cbn [cells_size csize Nat.add]; unfold usp1; intros; lia| exact WM4]).
  eassert (FB4 : rw_cells asegs m4 f _) by (apply (rw_cells_agree asegs m3 m4 _ _ FB3); [apply OFF34; cbn [cells_size csize Nat.add]; unfold usp1, RT_STACK in *; intros; lia| exact WM4]).
  eassert (SB4 : rw_cells asegs m4 (f / 8 + 2147450880) _) by (apply (rw_cells_agree asegs m3 m4 _ _ SB3); [apply OFF34; cbn [cells_size csize Nat.add]; unfold usp1, RT_STACK in *; intros; lia| exact WM4]).
  assert (GAP4 : stk asegs m4 usp1 (usp + -96)) by (apply (stk_agree_nw asegs m3 m4 _ _ GAP3); apply OFF34; cbv beta; intros; lia).
  destruct (af_client_consts RT AF Σ1 m4 ART4) as (_ & SHC4 & _ & _ & UT4).
  (* [comment removed for export] *)
  assert (EXITK : forall (mX : mem) (rax z0 z1 z2 r y1 y2 y3 y4 y5 y6 y7 q3 q4 z3 z4 z5 z6 : word) (Fx : bvmap 5 word) (fcx : bv 32) (cX : config) (x0 : word)
      (sb0 sb1 sb2 sb3 sb4 sb5 sb6 sb7 : byte),
    ART RT Σ1 mX -> mem_inv asegs mX -> stk asegs mX lo usp1 -> stk asegs mX usp1 (usp + -96) ->
    rw_cells asegs mX (usp + -96) [CB 24 j24; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs mX f [C8 x0] -> rw_cells asegs mX (f / 8 + 2147450880) [C1 sb0; C1 sb1; C1 sb2; C1 sb3; C1 sb4; C1 sb5; C1 sb6; C1 sb7] ->
    (forall a : word, aclient REST (rt_frames RT Σ) usp (bv_unsigned a) -> ~ (LK + 4 <= bv_unsigned a < LK + 8) -> mX a = m2 a) ->
    rw_cells asegs mX LK (mutex_cells z64 z64) -> lh_rep asegs LH_CEIL (DVerr GOBJ) mX (ownL L) ERR_FNS_A lh (bp lh) (bp B) B (8 * g_na g) g bks ->
    ASTA RT Σ1 PMc (eq (MS (mkR rax (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) z0 z1 z2 sp (Z_to_bv 64 usp1) r y1 y2 y3 y4 y5 y6 y7
                                 (Z_to_bv 64 f) q3 q4 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 z3 z4 z5 z6)
                            Fx (Z_to_bv 64 ERS_EXIT) fcx None mX (seg_rom asegs))) cX ->
    realizes asegs cX T).
  { intros mX rax z0 z1 z2 r y1 y2 y3 y4 y5 y6 y7 q3 q4 z3 z4 z5 z6 Fx fcx cX x0 sb0 sb1 sb2 sb3 sb4 sb5 sb6 sb7 ARTX MIX STX GAPX FRX FBX SBX AGX MCX REPX HcX.
    destruct (af_client_consts RT AF Σ1 mX ARTX) as (_ & SHCX & _ & _ & UTX).
    pose proof (ers_wxa sp gp (Z_to_bv 64 0xba3ef0) z0 z1 z2 r y1 y2 y3 y4 y5 y6 y7 q3 q4 s8 s9 s10 s11 z3 z4 z5 z6 Fx fcx mX rax f lo pad x0 sb0 sb1 sb2 sb3 sb4 sb5 sb6 sb7
                  F0 F64 FIMG ltac:(lia) ltac:(destruct FSH; [left | right]; lia) FBX SBX UTX ltac:(fold usp usp1; exact STX) ltac:(lia) ltac:(fold usp; unfold RT_STACK in *; lia)
                  ltac:(fold usp; unfold USTACK_TOP in *; lia) MIX) as WA.
    fold usp usp1 in WA.
    cl_lift WA HcX c5 Hc5.
    destruct (ASTA_unpack RT Σ1 _ _ c5 Hc5) as (ms5 & (m5 & -> & MU5 & WM5 & MI5) & Hc5'). clear Hc5.
    destruct (FKEEP mX m5 _ ARTX MU5 WM5 ltac:(intros x Hx; cbn [outside] in Hx; unfold shad, SHB; lia)) as [ART5 PR5].
    assert (OFF5 : forall P : Z -> Prop, (forall x, P x -> ~ (f <= x < f + 8) /\ ~ (f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 8)) -> agree_on P mX m5).
    { intros P HPx a Ha. apply MU5. cbn [outside]. destruct (HPx _ Ha) as [X1 X2]. repeat split; try exact I; lia. }
    assert (ST5 : stk asegs m5 lo usp1) by (apply (stk_agree_nw asegs mX m5 _ _ STX); apply OFF5; unfold usp1, RT_STACK in *; intros; lia).
    assert (GAP5 : stk asegs m5 usp1 (usp + -96)) by (apply (stk_agree_nw asegs mX m5 _ _ GAPX); apply OFF5; unfold usp1, RT_STACK in *; intros; lia).
    eassert (FR5 : rw_cells asegs m5 (usp + -96) _) by (apply (rw_cells_agree asegs mX m5 _ _ FRX); [apply OFF5; cbn [cells_size csize Nat.add]; unfold RT_STACK in *; intros; lia| exact WM5]).
    assert (MC5 : rw_cells asegs m5 LK (mutex_cells z64 z64)).
    { apply (rw_cells_agree asegs mX m5 _ _ MCX); [| exact WM5]. apply OFF5. cbn [cells_size csize Nat.add mutex_cells]. intros x Hx.
      destruct (FAP LK 40 (INR _ INLK)); unfold shad, SHB, USTACK_TOP in *; split; lia. }
    (* [comment removed for export] *)
    destruct (af_frame_release RT AF Σ1 m5 f 0%nat (rt_frames RT Σ) ART5 FRS1) as (Σ3 & fl & FLG & NAC & FL0 & FLW & FW & REL).
    change (fs_size 0) with 64 in FW. replace (f + 64 - 8) with (f + 56) in FW by lia. rewrite SP1 in FLW.
    pose proof (ers_wxb sp gp (Z_to_bv 64 0xba3ef0) z0 z1 z2 r (Z_to_bv 64 (-11)) y2 y3 y4 y5 y6 y7 q3 q4 s8 s9 s10 s11 z3 z4 z5 z6 rax ra s0 s1 s2 s3 s4 s5 s6 s7 Fx fcx m5 f fl lo pad j24
                  HP ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia) F0 ltac:(lia) FL0 ltac:(lia)
                  ltac:(fold usp usp1; exact ST5) ltac:(fold usp usp1; exact GAP5) FR5 FW FLG MI5) as WB.
    fold usp usp1 in WB.
    cl_lift WB Hc5' c6 Hc6.
    destruct (ASTA_unpack RT Σ1 _ _ c6 Hc6) as (ms6 & (x1 & x2 & x3 & x4 & x5 & x6 & x7 & m6 & -> & MU6 & WM6 & MI6 & ST6 & FLG6) & Hc6'). clear Hc6.
    fold usp in ST6.
    destruct (REL m6 MU6 WM6 FLG6) as (ART6 & FRS3 & LV3 & SP3 & CR3 & AL3 & AM3 & CG3).
    assert (NFL : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) usp x -> x <> fl).
    { intros x Hx E. subst x. destruct Hx as [H|H]; [unfold USTACK_TOP, RT_STACK, STACK_WIN in *; lia|]. apply NAC. right. rewrite LV1, FRS1.
      destruct H as [H|[H|[H|H]]]; [left; exact H | right; left; exact H
        | right; right; left; destruct H as (f' & k' & Hin & R); exists f', k'; split; [right; exact Hin | exact R]
        | right; right; right; destruct H as (f' & k' & Hin & R); exists f', k'; split; [right; exact Hin | exact R]]. }
    assert (AG6 : forall a : word, aclient REST (rt_frames RT Σ) usp (bv_unsigned a) -> ~ (LK + 4 <= bv_unsigned a < LK + 8) -> m6 a = m2 a).
    { intros a Ha Hn. assert (Ha' : aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact INR| intros ? X; exact X| lia]).
      rewrite (MU6 a ltac:(cbn [outside]; pose proof (NFL _ Ha'); split; [lia| exact I])). rewrite (PR5 a Ha'). exact (AGX a Ha Hn). }
    destruct (CARRY m6 AG6) as (PRK6 & ONC6 & FLC6 & LKC6 & LHC6).
    pose proof (REPF mX m5 _ REPX MU5 WM5 ltac:(intros x Hx; cbn [outside] in Hx; unfold shad, SHB; lia)) as REP5.
    assert (REP6 : lh_rep asegs LH_CEIL (DVerr GOBJ) m6 (ownL L) ERR_FNS_A lh (bp lh) (bp B) B (8 * g_na g) g bks).
    { apply (REPK m5 m6 _ REP5 MU6 WM6); intros; cbn [outside]; (split; [| exact I]);
        [pose proof (NFL x (proj2 (proj2 (proj2 (LOFF x ltac:(left; assumption))))))| pose proof (NFL x (proj2 (proj2 (proj2 (LOFF x ltac:(right; left; assumption))))))
        | pose proof (NFL x (proj2 (proj2 (proj2 (LOFF x ltac:(right; right; exists q, A; split; assumption))))))]; lia. }
    assert (MC6 : rw_cells asegs m6 LK (mutex_cells z64 z64)).
    { apply (rw_cells_agree asegs m5 m6 _ _ MC5); [| exact WM6]. intros x Hx. cbn [cells_size csize Nat.add mutex_cells] in Hx. apply MU6. cbn [outside]. split; [| exact I].
      pose proof (NFL (bv_unsigned x) ltac:(right; right; left; exists LK, 40; split; [exact (INR _ INLK)| lia])). lia. }
    apply Hk. exists Σ3, r.
    split; [| split; [rewrite LV3; exact LV1 | split; [exact FRS3 | split; [rewrite SP3; exact SP1 | split; [rewrite CR3; exact CR1 | rewrite CG3; exact CG1]]]]].
    eapply ASTA_conseq; [exact (ASTA_switch RT Σ1 Σ3 PMc _ c6 Hc6' AL3 AM3)|]. intros ms <-. exists m6.
    split; [exists x1, x2, x3, (Z_to_bv 64 fl), y2, y3, y4, y5, y6, y7, x4, x5, x6, x7, Fx, fcx; reflexivity|].
    split; [exact (conj ART6 (conj MI6 ST6))|].
    split; [exact PRK6|]. split; [exact (conj REP6 (conj PERML ALN))|]. split; [exact MC6|]. exact (conj ONC6 (conj FLC6 (conj LKC6 LHC6))). }
  (* [comment removed for export] *)
  assert (AFTERIGI : forall (ma mb : mem), ART RT Σ1 mb -> rt_pres_fp REST (rt_frames RT Σ1) usp1 [(LK + 4, LK + 8)] ma mb ->
            (forall a : word, aclient REST (rt_frames RT Σ) usp (bv_unsigned a) -> ~ (LK + 4 <= bv_unsigned a < LK + 8) -> ma a = m2 a) ->
            rw_cells asegs ma (usp + -96) [CB 24 j24; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
            (forall cs, rw_cells asegs ma f cs -> Z.of_nat (cells_size cs) = 56 -> rw_cells asegs mb f cs)
            /\ (forall cs, rw_cells asegs ma (f / 8 + 2147450880) cs -> Z.of_nat (cells_size cs) = 8 -> rw_cells asegs mb (f / 8 + 2147450880) cs)
            /\ (stk asegs ma usp1 (usp + -96) -> stk asegs mb usp1 (usp + -96))
            /\ rw_cells asegs mb (usp + -96) [CB 24 j24; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
            /\ (forall a : word, aclient REST (rt_frames RT Σ) usp (bv_unsigned a) -> ~ (LK + 4 <= bv_unsigned a < LK + 8) -> mb a = m2 a)).
  { intros ma mb ARTb PRESb AGa FRa.
    assert (AGF : forall P : Z -> Prop, (forall x, P x -> aclient REST (rt_frames RT Σ1) usp1 x /\ ~ (LK + 4 <= x < LK + 8)) -> agree_on P ma mb).
    { intros P HPx a Ha. destruct (HPx _ Ha) as [X1 X2]. apply PRESb; [exact X1| cbn [outside]; split; [lia| exact I]]. }
    pose proof (FAP LK 40 (INR _ INLK)) as KLK.
    split. { intros cs H Hs. apply (rw_cells_agree_nw asegs ma mb _ _ H). apply AGF. intros x Hx. rewrite Hs in Hx. split; [apply (acl_frame _ _ _ f 0%nat); [exact INF| change (fs_size 0) with 64; lia]| lia]. }
    split. { intros cs H Hs. apply (rw_cells_agree_nw asegs ma mb _ _ H). apply AGF. intros x Hx. rewrite Hs in Hx.
             split; [apply (acl_fshadow _ _ _ f 0%nat); [exact INF| change (fs_size 0) with 64; rewrite SHF; unfold shad, SHB; lia]| unfold USTACK_TOP in *; lia]. }
    split. { intros G. apply (stk_agree_nw asegs ma mb _ _ G). apply AGF. intros x Hx. split; [left; unfold USTACK_TOP in *; lia| unfold usp1, STACK_WIN in *; lia]. }
    split. { apply (rw_cells_agree_nw asegs ma mb _ _ FRa). apply AGF. cbn [cells_size csize Nat.add]. intros x Hx. split; [left; unfold usp1, USTACK_TOP in *; lia| unfold STACK_WIN in *; lia]. }
    intros a Ha Hn. rewrite <- (AGa a Ha Hn). apply PRESb; [| cbn [outside]; split; [lia| exact I]].
    apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros ? X; exact X| intros e' He; rewrite FRS1; right; exact He| unfold usp1; lia]. }
  (* [comment removed for export] *)
  assert (KEY : forall (mb : mem) (j8 j16' : list byte) (w : word),
            rw_cells asegs mb f [C8 (Z_to_bv 64 ERS_MAGIC); C8 (Z_to_bv 64 0x17ece); C8 (Z_to_bv 64 e_reason); CB 8 j8; C8 w; CB 16 j16'] ->
            rw_cells asegs mb (f / 8 + 2147450880) [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))] ->
            rw_cells asegs mb (f + 32) [C8 w] /\ acc asegs mb (f + 32) 8 /\ (f + 32) mod 8 = 0).
  { intros mb j8 j16' w FBb SBb.
    lazymatch type of FBb with rw_cells _ _ _ [?c1; ?c2; ?c3; ?c4; ?c5; ?c6] => pose proof (rw_cells_skip mb f [c1; c2; c3; c4] [c5; c6] FBb) as X end.
    cbn [cells_size csize Nat.add app] in X. replace (f + Z.of_nat 32) with (f + 32) in X by lia.
    assert (SBb4 : rw_cells asegs mb (f / 8 + 2147450880 + 4) [C1 (Z_to_bv 8 0)])
      by exact (rw_cells_head mb _ _ _ (rw_cells_skip mb (f / 8 + 2147450880) [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15))] _ SBb)).
    split; [exact (rw_cells_head mb _ _ _ X)|]. split; [| clear - F64; Z.div_mod_to_equations; lia].
    apply (acc_of_shadow0 mb (f + 32)); [replace (shad (f + 32)) with (f / 8 + 2147450880 + 4) by (unfold shad, SHB; Z.div_mod_to_equations; lia); exact (rw_C1_bytes mb _ _ SBb4)
                                      | clear - F64; Z.div_mod_to_equations; lia | lia]. }
  (* [comment removed for export] *)
  assert (DSTORE : forall (ma mb : mem), ART RT Σ1 ma -> munch [(f + 32, f + 40)] ma mb -> wmono asegs ma mb ->
            (forall a : word, aclient REST (rt_frames RT Σ) usp (bv_unsigned a) -> ~ (LK + 4 <= bv_unsigned a < LK + 8) -> ma a = m2 a) ->
            lh_rep asegs LH_CEIL (DVerr GOBJ) ma (ownL L) ERR_FNS_A lh (bp lh) (bp B) B (8 * g_na g) g bks ->
            ART RT Σ1 mb
            /\ (forall a : word, aclient REST (rt_frames RT Σ) usp (bv_unsigned a) -> ~ (LK + 4 <= bv_unsigned a < LK + 8) -> mb a = m2 a)
            /\ lh_rep asegs LH_CEIL (DVerr GOBJ) mb (ownL L) ERR_FNS_A lh (bp lh) (bp B) B (8 * g_na g) g bks
            /\ (forall P : Z -> Prop, (forall x, P x -> ~ (f + 32 <= x < f + 40)) -> agree_on P ma mb)).
  { intros ma mb ARTa MUx WMx AGa REPa.
    destruct (FKEEP ma mb _ ARTa MUx WMx ltac:(intros x Hx; cbn [outside] in Hx; lia)) as [ARTb PRab].
    split; [exact ARTb|]. split. { intros a Ha Hn. rewrite (PRab a ltac:(apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact INR| intros ? X; exact X| lia])). exact (AGa a Ha Hn). }
    split; [exact (REPF ma mb _ REPa MUx WMx ltac:(intros x Hx; cbn [outside] in Hx; lia))|].
    intros P HPx a Ha. apply MUx. cbn [outside]. pose proof (HPx _ Ha). split; [lia| exact I]. }
  pose proof (FAP LK 40 (INR _ INLK)) as KLK.
  (* [comment removed for export] *)
  destruct (Z.eq_dec (Z.land e 2147483648) 0) as [EB|EB]; cycle 1.
  { pose proof (ers_w2a sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 (Z_to_bv 64 e_do_esi) a2x a3x b4 b5 b6 b7 s4 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m4 f e lo pad
                  HE EB ltac:(fold usp usp1; exact ST4) ltac:(lia) ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(fold usp; unfold USTACK_TOP in *; lia) MI4) as W2.
    fold usp usp1 in W2. cl_lift W2 Hc4' c5 Hc5. destruct (ASTA_unpack RT Σ1 _ _ c5 Hc5) as (ms5 & -> & Hc5'). clear Hc5.
    exact (EXITK m4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 c5 _ _ _ _ _ _ _ _ _ ART4 MI4 ST4 GAP4 FR4 (rw_cells_head m4 _ _ _ FB4) SB4 AG4 MC4 REP4 Hc5'). }
  (* [comment removed for export] *)
  pose proof (ers_w2b sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 (Z_to_bv 64 e_do_esi) a2x a3x b4 b5 b6 b7 s4 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m4 f e lo pad fr
                HE EB F0 FIMG ltac:(lia) ltac:(destruct FSH; [left | right]; lia) FB4 FLC4 UT4 ltac:(fold usp usp1; exact ST4) ltac:(lia)
                ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(fold usp; unfold USTACK_TOP in *; lia) MI4) as W2.
  fold usp usp1 in W2. cl_lift W2 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ1 _ _ c5 Hc5) as (ms5 & (m5 & -> & MU5 & WM5 & MI5 & FB5) & Hc5'). clear Hc5.
  destruct (DSTORE m4 m5 ART4 MU5 WM5 AG4 REP4) as (ART5 & AG5 & REP5 & OFF45).
  destruct (CARRY m5 AG5) as (PRK5 & ONC5 & FLC5 & LKC5 & LHC5).
  assert (MC5 : rw_cells asegs m5 LK (mutex_cells z64 z64)) by (apply (rw_cells_agree asegs m4 m5 _ _ MC4); [apply OFF45; cbn [cells_size csize Nat.add mutex_cells]; intros; lia| exact WM5]).
  eassert (FR5 : rw_cells asegs m5 (usp + -96) _) by (apply (rw_cells_agree asegs m4 m5 _ _ FR4); [apply OFF45; cbn [cells_size csize Nat.add]; unfold RT_STACK in *; intros; lia| exact WM5]).
  eassert (SB5 : rw_cells asegs m5 (f / 8 + 2147450880) _) by (apply (rw_cells_agree asegs m4 m5 _ _ SB4); [apply OFF45; cbn [cells_size csize Nat.add]; unfold USTACK_TOP in *; intros; lia| exact WM5]).
  assert (GAP5 : stk asegs m5 usp1 (usp + -96)) by (apply (stk_agree_nw asegs m4 m5 _ _ GAP4); apply OFF45; unfold usp1, RT_STACK in *; intros; lia).
  assert (ST5 : stk asegs m5 lo usp1) by (apply (stk_agree_nw asegs m4 m5 _ _ ST4); apply OFF45; unfold usp1, RT_STACK in *; intros; lia).
  destruct (KEY m5 _ _ _ FB5 SB5) as (KC5 & KA5 & KAL).
  (* [comment removed for export] *)
  apply (C_IGI Σ1 PMc (Z_to_bv 64 SITE_ers_igi1) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 2147483647) (Z_to_bv 64 1) a3x b4 b5 b6 b7
           (Z_to_bv 64 f) (Z_to_bv 64 e) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 u3 u4 u5 u6
           F2 fc2 m5 lo L REST lh B g bks LK (f + 32) f 0%nat (Z_to_bv 64 (Z.land e 2147483647)) FDO MST eq_refl eq_refl ART5 MI5).
  { unfold call_ok. rewrite EU1. split; [exact ST5|]. split; [rewrite SP1; exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|].
    fold usp in SPA. clear - SPA HP HPM. Z.div_mod_to_equations. lia. }
  { rewrite EU1. unfold usp1, RT_STACK in *. lia. }
  { exact LKC5. } { exact LHC5. } { exact INLK. } { exact AL4. } { exact MC5. }
  { exact (conj REP5 (conj PERML ALN)). } { rewrite LV1. exact PERM. } { exact RPOS. }
  { exact INF. } { lia. } { change (fs_size 0) with 64. lia. } { exact KC5. } { exact KA5. } { exact KAL. }
  { exact Hc5'. }
  clear Hc5'. intros c6 (v1 & Hc6 & VOK1).
  destruct (ASTA_unpack RT Σ1 _ _ c6 Hc6) as (ms6 & (m6 & RS6 & (ART6 & MI6 & ST6) & PRES6 & REPE6 & MC6 & KC6) & Hc6'). clear Hc6.
  destruct RS6 as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F6 & fc6 & ->).
  rewrite EU1 in ST6, PRES6. rewrite (ret_pc_even SITE_ers_igi1) in Hc6' by (unfold SITE_ers_igi1; lia).
  destruct REPE6 as (REP6 & _ & _).
  destruct (AFTERIGI m5 m6 ART6 PRES6 AG5 FR5) as (FBT6 & SBT6 & GAPT6 & FR6 & AG6). pose proof (GAPT6 GAP5) as GAP6. pose proof (SBT6 _ SB5 eq_refl) as SB6.
  pose proof (FBT6 _ FB5 eq_refl) as FB6.
  destruct (CARRY m6 AG6) as (PRK6 & ONC6 & FLC6 & LKC6 & LHC6).
  assert (VR1 : 0 <= v1 < 2^64) by (destruct VOK1 as [->|(_ & V1 & V2 & _)]; [lia| unfold IMG_UT_LO, IMG_UT_HI in *; lia]).
  (* [comment removed for export] *)
  assert (FOUNDK : forall (mX : mem) (rax z0 z1 z2 y1 y2 y3 y4 y5 y6 y7 q3 z3 z4 z5 z6 : word) (Fx : bvmap 5 word) (fcx : bv 32) (cX : config) (v : Z) (w : word) (j8 j16' : list byte),
    DVerr GOBJ v -> ART RT Σ1 mX -> mem_inv asegs mX -> stk asegs mX lo usp1 -> stk asegs mX usp1 (usp + -96) ->
    rw_cells asegs mX (usp + -96) [CB 24 j24; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs mX f [C8 (Z_to_bv 64 ERS_MAGIC); C8 (Z_to_bv 64 0x17ece); C8 (Z_to_bv 64 e_reason); CB 8 j8; C8 w; CB 16 j16'] ->
    rw_cells asegs mX (f / 8 + 2147450880) [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))] ->
    (forall a : word, aclient REST (rt_frames RT Σ) usp (bv_unsigned a) -> ~ (LK + 4 <= bv_unsigned a < LK + 8) -> mX a = m2 a) ->
    rw_cells asegs mX LK (mutex_cells z64 z64) -> lh_rep asegs LH_CEIL (DVerr GOBJ) mX (ownL L) ERR_FNS_A lh (bp lh) (bp B) B (8 * g_na g) g bks ->
    ASTA RT Σ1 PMc (eq (MS (mkR rax (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) z0 z1 z2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 v) y1 y2 y3 y4 y5 y6 y7
                                 (Z_to_bv 64 f) q3 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 z3 z4 z5 z6)
                            Fx (Z_to_bv 64 ERS_FOUND) fcx None mX (seg_rom asegs))) cX ->
    realizes asegs cX T).
  { intros mX rax z0 z1 z2 y1 y2 y3 y4 y5 y6 y7 q3 z3 z4 z5 z6 Fx fcx cX v w j8 j16' DV ARTX MIX STX GAPX FRX FBX SBX AGX MCX REPX HcX.
    destruct (dverr_cells RT GOBJ AF AFP Σ1 mX v ARTX DV) as (_ & _ & ACC16). destruct (af_client_consts RT AF Σ1 mX ARTX) as (_ & SHCX & _ & _ & UTX).
    pose proof DV as (VAL & VLO & VHI & _). unfold IMG_UT_LO, IMG_UT_HI in VLO, VHI.
    destruct (ut_ro_C8_any mX (v + 8) UTX ltac:(unfold IMG_UT_LO; lia) ltac:(unfold IMG_UT_HI; lia)) as (sw & SW).
    pose proof (ers_wf rax sp gp (Z_to_bv 64 0xba3ef0) z0 z1 z2 y1 y2 y3 y4 y5 y6 y7 q3 (Z_to_bv 64 (f + 32)) s8 s9 s10 s11 z3 z4 z5 z6 Fx fcx mX f lo pad v sw
                  ltac:(lia) VAL ltac:(unfold SEGTOP_A; lia) ACC16 SW UTX SHCX ltac:(fold usp usp1; exact STX) ltac:(lia) ltac:(fold usp; unfold RT_STACK in *; lia)
                  ltac:(fold usp; unfold USTACK_TOP in *; lia) MIX) as WF.
    fold usp usp1 in WF. cl_lift WF HcX c7 Hc7. destruct (ASTA_unpack RT Σ1 _ _ c7 Hc7) as (ms7 & (y1' & ->) & Hc7'). clear Hc7.
    exact (EXITK mX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fx fcx c7 _ _ _ _ _ _ _ _ _ ARTX MIX STX GAPX FRX (rw_cells_head mX _ _ _ FBX) SBX AGX MCX REPX Hc7'). }
  destruct (Z.eq_dec v1 0) as [V1|V1]; cycle 1.
  { (* [comment removed for export] *)
    destruct VOK1 as [X|DV1]; [lia|].
    pose proof (ers_w3a sp gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 (Z_to_bv 64 (f + 32)) s8 s9 s10 s11 w3 w4 w5 w6 F6 fc6 m6 f e lo pad v1
                  ltac:(lia) ltac:(fold usp usp1; exact ST6) ltac:(lia) ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(fold usp; unfold USTACK_TOP in *; lia) MI6) as W3.
    fold usp usp1 in W3. cl_lift W3 Hc6' c7 Hc7. destruct (ASTA_unpack RT Σ1 _ _ c7 Hc7) as (ms7 & -> & Hc7'). clear Hc7.
    exact (FOUNDK m6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F6 fc6 c7 v1 _ _ _ DV1 ART6 MI6 ST6 GAP6 FR6 FB6 SB6 AG6 MC6 REP6 Hc7'). }
  (* [comment removed for export] *)
  subst v1. destruct (af_client_consts RT AF Σ1 m6 ART6) as (_ & _ & _ & _ & UT6).
  pose proof (ers_w3b sp gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 s8 s9 s10 s11 w3 w4 w5 w6 F6 fc6 m6 f e lo pad (firstn 8 fr) (skipn 16 fr) (Z_to_bv 64 (Z.land e 2147483647))
                HE F0 FIMG ltac:(lia) ltac:(destruct FSH; [left | right]; lia) FB6 UT6 ltac:(fold usp usp1; exact ST6) ltac:(lia)
                ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(fold usp; unfold USTACK_TOP in *; lia) MI6) as W3.
  fold usp usp1 in W3. cl_lift W3 Hc6' c7 Hc7.
  destruct (ASTA_unpack RT Σ1 _ _ c7 Hc7) as (ms7 & (m7 & -> & MU7 & WM7 & MI7 & FB7) & Hc7'). clear Hc7.
  destruct (DSTORE m6 m7 ART6 MU7 WM7 AG6 REP6) as (ART7 & AG7 & REP7 & OFF67).
  destruct (CARRY m7 AG7) as (PRK7 & ONC7 & FLC7 & LKC7 & LHC7).
  assert (MC7 : rw_cells asegs m7 LK (mutex_cells z64 z64)) by (apply (rw_cells_agree asegs m6 m7 _ _ MC6); [apply OFF67; cbn [cells_size csize Nat.add mutex_cells]; intros; lia| exact WM7]).
  eassert (FR7 : rw_cells asegs m7 (usp + -96) _) by (apply (rw_cells_agree asegs m6 m7 _ _ FR6); [apply OFF67; cbn [cells_size csize Nat.add]; unfold RT_STACK in *; intros; lia| exact WM7]).
  eassert (SB7 : rw_cells asegs m7 (f / 8 + 2147450880) _) by (apply (rw_cells_agree asegs m6 m7 _ _ SB6); [apply OFF67; cbn [cells_size csize Nat.add]; unfold USTACK_TOP in *; intros; lia| exact WM7]).
  assert (GAP7 : stk asegs m7 usp1 (usp + -96)) by (apply (stk_agree_nw asegs m6 m7 _ _ GAP6); apply OFF67; unfold usp1, RT_STACK in *; intros; lia).
  assert (ST7 : stk asegs m7 lo usp1) by (apply (stk_agree_nw asegs m6 m7 _ _ ST6); apply OFF67; unfold usp1, RT_STACK in *; intros; lia).
  destruct (KEY m7 _ _ _ FB7 SB7) as (KC7 & KA7 & _).
  (* [comment removed for export] *)
  apply (C_IGI Σ1 PMc (Z_to_bv 64 SITE_ers_igi2) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 (f + 32)) e1 e2 e3 e4 e5 e6 e7
           (Z_to_bv 64 f) (Z_to_bv 64 (Z.shiftl e 41)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 w3 w4 w5 w6
           F6 fc6 m7 lo L REST lh B g bks LK (f + 32) f 0%nat (Z_to_bv 64 (Z.land e 8388607)) FDO MST eq_refl eq_refl ART7 MI7).
  { unfold call_ok. rewrite EU1. split; [exact ST7|]. split; [rewrite SP1; exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|].
    fold usp in SPA. clear - SPA HP HPM. Z.div_mod_to_equations. lia. }
  { rewrite EU1. unfold usp1, RT_STACK in *. lia. }
  { exact LKC7. } { exact LHC7. } { exact INLK. } { exact AL4. } { exact MC7. }
  { exact (conj REP7 (conj PERML ALN)). } { rewrite LV1. exact PERM. } { exact RPOS. }
  { exact INF. } { lia. } { change (fs_size 0) with 64. lia. } { exact KC7. } { exact KA7. } { exact KAL. }
  { exact Hc7'. }
  clear Hc7'. intros c8 (v2 & Hc8 & VOK2).
  destruct (ASTA_unpack RT Σ1 _ _ c8 Hc8) as (ms8 & (m8 & RS8 & (ART8 & MI8 & ST8) & PRES8 & REPE8 & MC8 & KC8) & Hc8'). clear Hc8.
  destruct RS8 as (x0 & x1 & x2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & x3 & x4 & x5 & x6 & F8 & fc8 & ->).
  rewrite EU1 in ST8, PRES8. rewrite (ret_pc_even SITE_ers_igi2) in Hc8' by (unfold SITE_ers_igi2; lia).
  destruct REPE8 as (REP8 & _ & _).
  destruct (AFTERIGI m7 m8 ART8 PRES8 AG7 FR7) as (FBT8 & SBT8 & GAPT8 & FR8 & AG8). pose proof (GAPT8 GAP7) as GAP8. pose proof (SBT8 _ SB7 eq_refl) as SB8.
  pose proof (FBT8 _ FB7 eq_refl) as FB8.
  assert (VR2 : 0 <= v2 < 2^64) by (destruct VOK2 as [->|(_ & V1' & V2' & _)]; [lia| unfold IMG_UT_LO, IMG_UT_HI in *; lia]).
  (* [comment removed for export] *)
  pose proof (ers_w4 sp gp (Z_to_bv 64 0xba3ef0) x0 x1 x2 d1 d2 d3 d4 d5 d6 d7 (Z_to_bv 64 (Z.shiftl e 41)) (Z_to_bv 64 (f + 32)) s8 s9 s10 s11 x3 x4 x5 x6 F8 fc8 m8 f lo pad v2
                VR2 ltac:(fold usp usp1; exact ST8) ltac:(lia) ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(fold usp; unfold USTACK_TOP in *; lia) MI8) as W4.
  fold usp usp1 in W4. cl_lift W4 Hc8' c9 Hc9. destruct (ASTA_unpack RT Σ1 _ _ c9 Hc9) as (ms9 & -> & Hc9'). clear Hc9.
  destruct (Z.eq_dec v2 0) as [V2|V2].
  - rewrite (proj2 (Z.eqb_eq v2 0) V2) in Hc9'.
    exact (EXITK m8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F8 fc8 c9 _ _ _ _ _ _ _ _ _ ART8 MI8 ST8 GAP8 FR8 (rw_cells_head m8 _ _ _ FB8) SB8 AG8 MC8 REP8 Hc9').
  - rewrite (proj2 (Z.eqb_neq v2 0) V2) in Hc9'. destruct VOK2 as [X|DV2]; [lia|].
    exact (FOUNDK m8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F8 fc8 c9 v2 _ _ _ DV2 ART8 MI8 ST8 GAP8 FR8 FB8 SB8 AG8 MC8 REP8 Hc9').
Qed.
End Reason.

