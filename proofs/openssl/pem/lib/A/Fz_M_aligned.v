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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_ut RT_iface_pem I_lkit Fz_kit Fz_chk Fz_fkit Fz_M_malloc Fz_env Fz_mkit Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition e_CRYPTO_aligned_alloc : Z := 0x1fc040.
Definition SITE_aa_smalloc : Z := 0x1fc0c0.
Definition SITE_aa_memalign : Z := 0x1fc1f8.
Definition SITE_aa_release : Z := 0x1fc288.

(* [comment removed for export] *)
Definition aa_s0_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (n fp lo pad : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a1' a2' : word) (j : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_aa_smalloc) (Z_to_bv 64 (bv_unsigned sp + -128 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -128 - pad))
                 (Z_to_bv 64 64) a1' a2' a3 a4 a5 a6 a7 s2 a4 a3 (Z_to_bv 64 fp) (Z_to_bv 64 64) (Z_to_bv 64 n) s8 s9 s10 (Z_to_bv 64 0x7fff8000) t3 t4 t5 t6)
            F (Z_to_bv 64 (e_stack_malloc 0)) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 128, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -128) [CB 24 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk asegs m' (bv_unsigned sp + -128 - pad) (bv_unsigned sp + -128)
    /\ stk asegs m' lo (bv_unsigned sp + -128 - pad).

Lemma aa_s0_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (n fp lo pad : Z),
  (pad = 0 \/ pad = 16) -> bv_unsigned sp mod 32 = pad ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 144 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  ro_cells asegs m g_detect_stack_use_after_return [C4 (Z_to_bv 64 1)] -> mem_inv asegs m ->
  evt asegs (aa_s0_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc n fp lo pad m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) (Z_to_bv 64 64) (Z_to_bv 64 fp) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_CRYPTO_aligned_alloc) fc None m (seg_rom asegs)).
Proof.
  intros until pad. intros HP HPM ST HLO HLOS SPH UT SHC UAR MI. unfold e_CRYPTO_aligned_alloc, g_shadow_memory_dynamic_address, g_detect_stack_use_after_return in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 128, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 128, SP)]) by ut_fp_lia.
  carve_frame 128%nat ST.
  zstep. zstep; lfix. do 14 zstep. zstep.
  rewrite (land_m32_pad (SP + -128) pad) by (first [lia | replace (SP + -128) with (SP + (-4) * 32) by lia; rewrite Z.mod_add by lia; exact HPM]).
  do 5 zstep. do 2 zstep. zstep. zstep. zstep. zstep. zstep. zstep. if_false. do 2 zstep.
  destruct (stk_split asegs _ lo (SP + -128 - pad) (SP + -128) ST ltac:(lia)) as [ST1 GAP].
  lazymatch goal with FRH : rw_cells asegs ?mm (SP + -128) (?c1 :: ?c2 :: ?rest) |- _ =>
    pose proof (rw_cells_blur mm (SP + -128) [c1; c2] rest FRH) as FRB end.
  cbn [cells_size csize Nat.add] in FRB.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold aa_s0_post, SITE_aa_smalloc, e_stack_malloc. apply evt_done. do 4 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact FRB|]. split; [exact GAP| exact ST1].
Qed.
(* [comment removed for export] *)
Definition AA_MAGIC : Z := 0x41b58ab3.
Definition AA_DESCR : Z := 0x32407.   (* [comment removed for export] *)
Definition aa_shadow : list cell :=
  [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))].

Definition aa_s1_post (sp gp tp t0 t1 t2 s3 s4 a5 a6 a7 t3 t4 t5 t6 : word)
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word) (F : bvmap 5 word) (fc : bv 32)
    (n fp f lo pad : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a3' a4' : word) (j fr : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_aa_memalign) (Z_to_bv 64 (bv_unsigned sp + -128 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -128 - pad))
                 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 64) (Z_to_bv 64 n) a3' a4' a5 a6 a7 (Z_to_bv 64 f) s3 s4 (Z_to_bv 64 fp) (Z_to_bv 64 64) (Z_to_bv 64 n)
                 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 f) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 (fp / 8 + 2147450880)) t3 t4 t5 t6)
            F (Z_to_bv 64 e_posix_memalign) fc None m' (seg_rom asegs)
    /\ munch [(f, f + 56); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (fp, fp + 8); (bv_unsigned sp - 128, bv_unsigned sp)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -128) [CB 24 j; C8 s11'; C8 s10'; C8 s9'; C8 s8'; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0]
    /\ rw_cells asegs m' f [C8 (Z_to_bv 64 AA_MAGIC); C8 (Z_to_bv 64 AA_DESCR); C8 (Z_to_bv 64 e_CRYPTO_aligned_alloc); CB 32 fr]
    /\ rw_cells asegs m' (f / 8 + 2147450880) aa_shadow
    /\ rw_cells asegs m' fp [C8 (Z_to_bv 64 0)].

Lemma aa_s1_walk : forall ra0 sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s8 s9 s10 t3 t4 t5 t6
    (s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word) (F : bvmap 5 word) fc (m : mem) (n fp f lo pad : Z) (j fj sj pj : list byte),
  (pad = 0 \/ pad = 16) -> 0xbc6000 <= f -> f + 64 <= lo -> (f + 64 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 144 -> bv_unsigned sp <= 2^47 ->
  0x10007fff8000 <= fp -> fp + 8 <= lo -> fp mod 8 = 0 -> (fp + 8 <= f \/ f + 64 <= fp) ->
  img_untouched m -> ro_cells asegs m G_MALLOC_IMPL [C8 (Z_to_bv 64 e_CRYPTO_malloc)] ->
  rw_cells asegs m (bv_unsigned sp + -128) [CB 24 j; C8 s11'; C8 s10'; C8 s9'; C8 s8'; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0] ->
  rw_cells asegs m f [CB 56 fj] -> rw_cells asegs m (f / 8 + 2147450880) [CB 8 sj] ->
  rw_cells asegs m fp [CB 8 pj] -> ro_cells asegs m (fp / 8 + 2147450880) [C1 (Z_to_bv 8 0)] -> mem_inv asegs m ->
  evt asegs (aa_s1_post sp gp tp t0 t1 t2 s3 s4 a5 a6 a7 t3 t4 t5 t6 ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' F fc n fp f lo pad m)
    (MS (mkR (Z_to_bv 64 SITE_aa_smalloc) (Z_to_bv 64 (bv_unsigned sp + -128 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -128 - pad))
             (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 fp) (Z_to_bv 64 64) (Z_to_bv 64 n) s8 s9 s10 (Z_to_bv 64 0x7fff8000) t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_aa_smalloc) fc None m (seg_rom asegs)).
Proof.
  intros until pj. intros HP FIMG FLO FSH HLOS HLO SPH PHI PLO P8 PF UT MIMP FR FB SB PC PSH MI.
  unfold SITE_aa_smalloc, G_MALLOC_IMPL, e_CRYPTO_malloc in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(f, f + 56); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (fp, fp + 8); (SP - 128, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (div8_facts f) as Q1. pose proof (div8_facts fp) as Q2.
  assert (HWU : ut_fp [(f, f + 56); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (fp, fp + 8); (SP - 128, SP)]) by ut_fp_lia.
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  do 3 zstep. zstep. if_true.
  destruct HP as [-> | ->].
  1: replace (SP + -128 - 0) with (SP + -128) by lia.
  2: replace (SP + -128 - 16) with (SP + -144) by lia.
  all: do 4 zstep; rewrite (shr3_div f) by lia; do 4 zstep.
  all: zstep; lfix. all: zstep; lfix. all: zstep; lfix.
  all: do 2 zstep.
  all: zstep; lfix. all: zstep; lfix. all: zstep; lfix. all: zstep; lfix.
  all: zstep.
  all: zstep; lfix. all: zstep; lfix. all: zstep; lfix. all: zstep; lfix.
  all: zstep; rewrite (shr3_div fp) by lia. all: zstep.
  all: zstep.
  all: do 2 zstep.
  all: if_false.
  all: zstep.
  all: zstep; lfix.
  all: zstep.
  all: if_false.
  all: do 21 zstep.
  all: zstep.
  all: if_false.
  all: do 4 zstep.
  all: zstep.
  all: if_false.
  all: do 2 zstep.
  all: zstep; lfix.
  all: zstep.
  all: if_true.
  all: do 4 zstep.
  1: replace (SP + -128) with (SP + -128 - 0) by lia.
  2: replace (SP + -144) with (SP + -128 - 16) by lia.
  all: pose proof (rw_cells_blur _ _ [_; _] _ FR) as FRB.
  all: cbn [cells_size csize Nat.add] in FRB.
  all: subst; rewrite ?Z_to_bv_bv_unsigned.
  all: unfold aa_s1_post, SITE_aa_memalign, e_posix_memalign, aa_shadow, AA_MAGIC, AA_DESCR, e_CRYPTO_aligned_alloc; apply evt_done; do 5 eexists; (split; [reflexivity|]).
  all: (split; [assumption|]); (split; [assumption|]); (split; [assumption|]); (split; [exact FRB|]); (split; [eassumption|]); (split; [eassumption | eassumption]).
Qed.
(* [comment removed for export] *)
Definition AA_RETIRED : Z := 0x45e0360e.
Definition aa_shadow_f5 : list cell :=
  [C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11))].

Definition aa_s2_post (sp gp tp t0 t1 t2 s0' s1' s3 s4 s6 s7 s8 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (fp f q : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (ra1 a1' : word) (m' : mem),
    ms = MS (mkR ra1 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 q) a1' a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) s3 s4 (Z_to_bv 64 fp) s6 s7 s8
                 (Z_to_bv 64 f) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 (fp / 8 + 2147450880)) t3 t4 t5 t6)
            F (Z_to_bv 64 SITE_aa_release) fc None m' (seg_rom asegs)
    /\ munch [(f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (fp, fp + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' fp [C8 (Z_to_bv 64 q)]
    /\ rw_cells asegs m' (f / 8 + 2147450880) aa_shadow_f5.

Lemma aa_s2_walk : forall ra0 sp gp tp t0 t1 t2 s0' s1' a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (fp f q : Z) (pw : word),
  0xbc6000 <= f -> f + 64 <= 2^47 -> (f + 64 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  0x10007fff8000 <= fp -> fp + 8 <= 2^47 -> fp mod 8 = 0 -> (fp + 8 <= f \/ f + 64 <= fp) ->
  rw_cells asegs m f [C8 (Z_to_bv 64 AA_MAGIC)] -> rw_cells asegs m (f + 32) [C8 (Z_to_bv 64 q)] ->
  rw_cells asegs m (f / 8 + 2147450880) aa_shadow ->
  rw_cells asegs m fp [C8 pw] -> ro_cells asegs m (fp / 8 + 2147450880) [C1 (Z_to_bv 8 0)] -> mem_inv asegs m ->
  evt asegs (aa_s2_post sp gp tp t0 t1 t2 s0' s1' s3 s4 s6 s7 (Z_to_bv 64 (f + 32)) a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc fp f q m)
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) s3 s4 (Z_to_bv 64 fp) s6 s7 (Z_to_bv 64 (f + 32))
             (Z_to_bv 64 f) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 (fp / 8 + 2147450880)) t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_aa_memalign) fc None m (seg_rom asegs)).
Proof.
  intros until pw. intros FIMG FH FSH PHI PH P8 PF HDR RET SB PC PSH MI.
  unfold SITE_aa_memalign, aa_shadow, AA_MAGIC in *.
  pose proof (munch_refl [(f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (fp, fp + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (div8_facts f) as Q1. pose proof (div8_facts fp) as Q2.
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  zstep. if_true.
  zstep. zstep. if_false.
  zstep. zstep.
  zstep. zstep; lfix. zstep.
  do 2 zstep. zstep; lfix.
  zstep. if_false.
  zstep.
  zstep; lfix. zstep; lfix. zstep; lfix. zstep; lfix. zstep; lfix. zstep; lfix. zstep; lfix. zstep; lfix.
  unfold aa_s2_post, SITE_aa_release, aa_shadow_f5. apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [eassumption | eassumption].
Qed.
(* [comment removed for export] *)
Definition aa_s3_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word) (F : bvmap 5 word) (fc : bv 32)
    (q fl lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3 t4 t5 t6)
            F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(fl, fl + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' fl [C1 (Z_to_bv 8 0)].

Lemma aa_s3_walk : forall ra1 ra0 sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word) (F : bvmap 5 word) fc (m : mem) (q f fl lo pad : Z) (j : list byte),
  (pad = 0 \/ pad = 16) -> lo <= bv_unsigned sp - 144 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  0 < f -> f + 64 <= lo -> 0 < fl -> fl + 1 <= lo ->
  stk asegs m lo (bv_unsigned sp + -128 - pad) -> stk asegs m (bv_unsigned sp + -128 - pad) (bv_unsigned sp + -128) ->
  rw_cells asegs m (bv_unsigned sp + -128) [CB 24 j; C8 s11'; C8 s10'; C8 s9'; C8 s8'; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0] ->
  ro_cells asegs m (f + 56) [C8 (Z_to_bv 64 fl)] -> rw_cells asegs m fl [C1 (Z_to_bv 8 1)] -> mem_inv asegs m ->
  evt asegs (aa_s3_post ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' F fc q fl lo m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -128 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -128 - pad))
             (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_aa_release) fc None m (seg_rom asegs)).
Proof.
  intros until j. intros HP HLO HLOS SPH F0 FLO FL0 FLLO ST1 GAP FR FLG FLB MI. unfold SITE_aa_release in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EUfl : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply unsigned_lit; lia).
  zstep. clear FLG.
  zstep; lfix.
  do 2 zstep.
  do 13 zstep.
  pose proof (stk_merge asegs _ lo (SP + -128 - pad) (SP + -128) ST1 GAP ltac:(lia)) as ST2.
  zstep.
  release_frame FR ST2 SP.
  zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold aa_s3_post. apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption| assumption].
Qed.
Section CAlignedAlloc.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis SM0 : stack_malloc_contract RT 0.
Hypothesis MAL : memalign_contract RT.

(* [comment removed for export] *)
Definition crypto_aligned_alloc_env_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (n fp pb nb lo : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 n -> a1 = Z_to_bv 64 64 -> a2 = Z_to_bv 64 fp -> tp = Z_to_bv 64 0xba3ef0 ->
  memalign_plain 64 n ->
  In (pb, nb) (rt_live RT Σ) -> nb <= 64512 -> pb <= fp -> fp + 8 <= pb + nb -> fp mod 8 = 0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x200 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_CRYPTO_aligned_alloc (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) [(SITE_aa_memalign, e_CRYPTO_aligned_alloc)] [(SITE_aa_memalign, e_posix_memalign)] ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 1 + mcost n <= rt_credit RT Σ ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_CRYPTO_aligned_alloc m)))
    (fun c => exists (Σ' : rts RT) (q : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 q) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) fp 8 m m'
           /\ cl_env m' lb canary /\ rw_cells asegs m' fp [C8 (Z_to_bv 64 q)] /\ wr_at asegs m' q n /\ acc asegs m' q n) c
       /\ rt_live RT Σ' = (q, n) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - 1 - mcost n /\ 0 < q /\ q mod 64 = 0 /\ q + n < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem crypto_aligned_alloc_cps : crypto_aligned_alloc_env_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n fp pb nb lo outer lb canary
    FDO MST -> -> -> -> HPL Hinb Hnb Hfp1 Hfp2 Hfp8 ART0 MI0 CALL HSTK CTX UWC CGH Hfr Hlen Hcr ENV.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  set (pad := usp mod 32).
  assert (HP : pad = 0 \/ pad = 16) by (unfold pad; clear - SPA; Z.div_mod_to_equations; lia).
  assert (HPM : usp mod 32 = pad) by reflexivity. clearbody pad.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 208 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLOI : SEGTOP_A <= lo) by (unfold SEGTOP_A, STACK_WIN in *; lia).
  set (usp1 := usp + -128 - pad).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & UAR & UT).
  pose proof (afp_live_hi RT GOBJ AFP Σ m pb nb ART0 Hinb Hnb) as PBHI.
  pose proof (af_live_range RT AF Σ m pb nb ART0 Hinb) as (_ & PBLO & _).
  assert (MC0 : 0 <= mcost n) by (destruct HPL as (_ & Hn1 & _); unfold mcost; destruct (n <=? 64512); lia).
  (* [comment removed for export] *)
  pose proof (aa_s0_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n fp lo pad
                HP HPM ST ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia) UT SHC UAR MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (a1' & a2' & j & m1 & -> & MU1 & WM1 & MI1 & FR1 & GAP1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, GAP1, ST1, Hc1'. fold usp1 in GAP1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 128 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 128 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  pose proof (cl_env_seg _ m m1 lb canary ENV MU1 ltac:(cl_fp_lia)) as ENV1.
  (* [comment removed for export] *)
  apply (SM0 Σ PMc (Z_to_bv 64 SITE_aa_smalloc) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 64) a1' a2' a3 a4 a5 a6 a7
           s2 a4 a3 (Z_to_bv 64 fp) (Z_to_bv 64 64) (Z_to_bv 64 n) s8 s9 s10 (Z_to_bv 64 0x7fff8000) t3 t4 t5 t6 F fc m1 lo FDO MST ltac:(left; reflexivity) eq_refl Hfr ltac:(lia) ART1 MI1).
  { unfold call_ok. rewrite EU1. split; [exact ST1|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|].
    fold usp in SPA. clear - SPA HP HPM. Z.div_mod_to_equations. lia. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & f & Hc2 & FRS1 & LV1 & SP1 & CR1 & F0 & F64 & FU & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WF2 & WS2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_aa_smalloc) in Hc2' by (unfold SITE_aa_smalloc; lia).
  assert (INF : In (f, 0%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  assert (INB1 : In (pb, nb) (rt_live RT Σ1)) by (rewrite LV1; exact Hinb).
  pose proof (af_frames_range RT AF Σ1 m2 f 0%nat ART2 INF) as (_ & FLO & _ & FPB).
  pose proof (af_frames_align RT AF Σ1 m2 f 0%nat ART2 INF) as (_ & FIMG).
  pose proof (af_frames_hi RT AF Σ1 m2 f 0%nat ART2 INF) as FSH.
  specialize (FPB pb nb INB1).
  rewrite SP1 in FLO. change (fs_size 0) with 64 in FLO, FSH, FU, WF2, WS2, FPB. change (64 - 8) with 56 in WF2. change (64 / 8) with 8 in WS2.
  unfold shad, SHB in WS2. unfold SEGTOP_A in FIMG.
  assert (SHF : shad (f + 64) = shad f + 8) by (replace (f + 64) with (f + 64 * 1) by lia; rewrite (shad_add64 f 1 F64); lia).
  assert (AG2 : forall a k, usp1 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m1 m2).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES2. left. lia. }
  cl_keep FR1 AG2 WM2 FR2.
  destruct (I_lkit.wr_at_rw_CB m2 f 56 WF2 ltac:(lia)) as (fj & FB2). destruct (I_lkit.wr_at_rw_CB m2 (f / 8 + 2147450880) 8 WS2 ltac:(lia)) as (sj & SB2).
  change (Z.to_nat 56) with 56%nat in FB2. change (Z.to_nat 8) with 8%nat in SB2.
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & _ & _ & _ & UT2).
  pose proof (af_acc_live RT AF Σ1 m2 pb nb ART2 INB1) as (WRB2 & ACCB2).
  destruct (I_lkit.wr_at_rw_CB m2 fp 8 (wr_at_sub m2 pb nb fp 8 WRB2 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (pj & PC2).
  change (Z.to_nat 8) with 8%nat in PC2.
  pose proof (acc_granule0_ro m2 pb nb fp ACCB2 ltac:(lia) ltac:(lia) Hfp8 ltac:(lia)) as PSH2. unfold shad, SHB in PSH2.
  pose proof (cl_env_pres _ _ _ m1 m2 lb canary ENV1 PRES2) as ENV2.
  (* [comment removed for export] *)
  pose proof (aa_s1_walk ra sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s2 a4 a3 s8 s9 s10 u3 u4 u5 u6
                s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F2 fc2 m2 n fp f lo pad j fj sj pj HP FIMG ltac:(lia) ltac:(destruct FSH; [left | right]; lia)
                ltac:(lia) ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(fold usp; unfold USTACK_TOP in *; lia)
                ltac:(lia) ltac:(lia) Hfp8 ltac:(destruct FPB; [right | left]; lia) UT2 (cl_env_mimp m2 lb canary ENV2) FR2 FB2 SB2 PC2 PSH2 MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (a3' & a4' & j3 & fr & m3 & -> & MU3 & WM3 & MI3 & FR3 & HDR3 & SB3 & PC3) & Hc3'). clear Hc3.
  fold usp in MU3, FR3, Hc3'. fold usp1 in Hc3'.
  assert (Q1 := div8_facts f). assert (Q2 := div8_facts fp).
  assert (ART3 : ART RT Σ1 m3).
  { apply (af_frame RT AF Σ1 m2 m3 (usp - 128) ART2 ltac:(rewrite SP1; lia)); [| exact WM3].
    intros a Ha. apply MU3. cbn [outside]. split; [| split; [| split; [| split; [| exact I]]]]; intros Hin; apply Ha.
    - apply (acl_frame _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; lia].
    - apply (acl_fshadow _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; rewrite SHF; unfold shad, SHB; lia].
    - apply (acl_live _ _ _ pb nb); [exact INB1 | lia].
    - apply acl_stack. unfold USTACK_TOP in *. lia. }
  assert (ST3 : stk asegs m3 lo usp1).
  { apply (stk_munch _ m2 m3 lo usp1 ST2 MU3 WM3). intros x Hx. cbn [outside]. unfold usp1 in Hx. lia. }
  pose proof (cl_env_seg _ m2 m3 lb canary ENV2 MU3 ltac:(cl_fp_lia)) as ENV3.
  assert (AG3 : forall a k, (usp <= a /\ a + k <= USTACK_TOP) -> agree_on (fun x => a <= x < a + k) m2 m3).
  { intros a k H. apply (agree_of_munch _ m2 m3 _ MU3). intros x Hx. cbv beta in Hx. cbn [outside]. unfold USTACK_TOP, RT_STACK in *. lia. }
  assert (AG03 : agree_on (fun x => usp <= x < USTACK_TOP) m m3).
  { intros a Ha. cbv beta in Ha. rewrite (AG3 usp (USTACK_TOP - usp) ltac:(lia) a ltac:(cbv beta; lia)).
    rewrite (PRES2 a ltac:(left; unfold usp1; lia)). exact (AG1 a Ha). }
  (* [comment removed for export] *)
  assert (SH32 : shad (f + 32) = f / 8 + 2147450880 + 4).
  { unfold shad, SHB. clear - F64. Z.div_mod_to_equations. lia. }
  assert (RETB : bytes_at asegs m3 (shad (f + 32)) [z8]).
  { rewrite SH32. apply rw_C1_bytes.
    pose proof (rw_cells_skip m3 (f / 8 + 2147450880) [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15))]
                  [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))] SB3) as X.
    cbn [cells_size csize Nat.add] in X. exact (rw_cells_head m3 _ _ _ X). }
  assert (CKD : checked_dst RT Σ1 m3 (Z_to_bv 64 usp1) (f + 32) 8).
  { split; [intros _; split; [apply (acc_of_shadow0 m3 (f + 32) RETB); [clear - F64; Z.div_mod_to_equations; lia | lia]|]|].
    - right; left. exists f, 0%nat. split; [exact INF | change (fs_size 0) with 64; lia].
    - split; [intros i Hi; apply (acl_frame _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; lia]|].
      exact (wr_at_wm m2 m3 _ _ (wr_at_sub m2 f 56 (f + 32) 8 WF2 ltac:(lia) ltac:(lia) ltac:(lia)) WM3). }
  assert (FRR3 : rw_cells asegs m3 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp + -128 + Z.of_nat (cells_size [CB 24 j3; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia).
    exact (rw_cells_skip m3 (usp + -128) [CB 24 j3; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR3). }
  rewrite <- CG1 in CTX, CGH.
  apply (MAL Σ1 PMc (Z_to_bv 64 SITE_aa_memalign) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 64) (Z_to_bv 64 n)
           a3' a4' b5 b6 b7 (Z_to_bv 64 f) a4 a3 (Z_to_bv 64 fp) (Z_to_bv 64 64) (Z_to_bv 64 n) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 f) (Z_to_bv 64 (f / 8 + 2147450880))
           (Z_to_bv 64 (fp / 8 + 2147450880)) u3 u4 u5 u6 F2 fc2 m3 (f + 32) 64 n lo FDO MST eq_refl eq_refl eq_refl eq_refl HPL ltac:(unfold USTACK_TOP in *; lia) CKD
           ltac:(rewrite LV1; exact Hlen) ltac:(rewrite CR1; lia) ART3 MI3).
  { unfold call_ok. rewrite EU1, SP1. split; [exact ST3|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|].
    fold usp in SPA. clear - SPA HP HPM. Z.div_mod_to_equations. lia. }
  { apply (cl_unwind_call (rt_cg RT Σ1) e_CRYPTO_aligned_alloc e_posix_memalign SITE_aa_memalign m m3 ra s0 sp (Z_to_bv 64 usp1) outer CTX
             (proj1 CGH _ ltac:(left; reflexivity)) (proj2 CGH _ ltac:(left; reflexivity)) ltac:(unfold SITE_aa_memalign; lia) UWC AG03 FRR3).
    - rewrite EU1. fold usp. unfold usp1. lia.
    - exact SPT. }
  { exact Hc3'. }
  clear Hc3'. intros c4 (Σ2 & q & Hc4 & LV2 & FRS2 & SP2 & CR2 & Q0 & Q64 & QU & CG2).
  destruct (ASTA_unpack RT Σ2 _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & RET4 & WR4 & ACC4) & Hc4'). clear Hc4.
  destruct RS4 as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F4 & fc4 & ->).
  rewrite EU1 in ST4, PRES4. rewrite (ret_pc_even SITE_aa_memalign) in Hc4' by (unfold SITE_aa_memalign; lia).
  assert (INF2 : In (f, 0%nat) (rt_frames RT Σ2)) by (rewrite FRS2; exact INF).
  assert (INB2 : In (pb, nb) (rt_live RT Σ2)) by (rewrite LV2; right; exact INB1).
  assert (INQ2 : In (q, n) (rt_live RT Σ2)) by (rewrite LV2; left; reflexivity).
  (* [comment removed for export] *)
  assert (AG4 : forall a k, ((usp1 <= a /\ a + k <= USTACK_TOP) \/ (f <= a /\ a + k <= f + 32) \/ (f / 8 + 2147450880 <= a /\ a + k <= f / 8 + 2147450880 + 8)
                            \/ (fp <= a /\ a + k <= fp + 8)) -> agree_on (fun x => a <= x < a + k) m3 m4).
  { intros a k H x Hx. cbv beta in Hx. apply PRES4.
    - destruct H as [H|[H|[H|H]]].
      + left. lia.
      + apply (acl_frame _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; lia].
      + apply (acl_fshadow _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; rewrite SHF; unfold shad, SHB; lia].
      + apply (acl_live _ _ _ pb nb); [exact INB1 | lia].
    - unfold USTACK_TOP, RT_STACK, usp1 in *. lia. }
  assert (HDR4 : rw_cells asegs m4 f [C8 (Z_to_bv 64 AA_MAGIC)]).
  { apply (rw_cells_agree asegs m3 m4 _ _ (rw_cells_head m3 f _ _ HDR3)); [| exact WM4]. apply AG4. cbn [cells_size csize Nat.add]. lia. }
  assert (SB4 : rw_cells asegs m4 (f / 8 + 2147450880) aa_shadow).
  { apply (rw_cells_agree asegs m3 m4 _ _ SB3); [| exact WM4]. apply AG4. cbn [aa_shadow cells_size csize Nat.add]. lia. }
  assert (PC4 : rw_cells asegs m4 fp [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_agree asegs m3 m4 _ _ PC3); [| exact WM4]. apply AG4. cbn [cells_size csize Nat.add]. lia. }
  pose proof (af_acc_live RT AF Σ2 m4 pb nb ART4 INB2) as (_ & ACCB4).
  pose proof (acc_granule0_ro m4 pb nb fp ACCB4 ltac:(lia) ltac:(lia) Hfp8 ltac:(lia)) as PSH4. unfold shad, SHB in PSH4.
  (* [comment removed for export] *)
  pose proof (aa_s2_walk (Z_to_bv 64 SITE_aa_memalign) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) v0 v1 v2 sp (Z_to_bv 64 usp1) d1 d2 d3 d4 d5 d6 d7 a4 a3
                (Z_to_bv 64 64) (Z_to_bv 64 n) v3 v4 v5 v6 F4 fc4 m4 fp f q (Z_to_bv 64 0) FIMG ltac:(unfold USTACK_TOP in *; lia)
                ltac:(destruct FSH; [left | right]; lia) ltac:(lia) ltac:(unfold USTACK_TOP, STACK_WIN in *; lia) Hfp8
                ltac:(destruct FPB; [right | left]; lia) HDR4 RET4 SB4 PC4 PSH4 MI4) as W2.
  cl_lift W2 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ2 _ _ c5 Hc5) as (ms5 & (ra5 & a1'' & m5 & -> & MU5 & WM5 & MI5 & PC5 & SH5) & Hc5'). clear Hc5.
  assert (ART5 : ART RT Σ2 m5).
  { apply (af_frame RT AF Σ2 m4 m5 usp1 ART4 ltac:(rewrite SP2, SP1; unfold usp1; lia)); [| exact WM5].
    intros a Ha. apply MU5. cbn [outside]. split; [| split; [| split; [| exact I]]]; intros Hin; apply Ha.
    - apply (acl_frame _ _ _ f 0%nat); [exact INF2 | change (fs_size 0) with 64; lia].
    - apply (acl_fshadow _ _ _ f 0%nat); [exact INF2 | change (fs_size 0) with 64; rewrite SHF; unfold shad, SHB; lia].
    - apply (acl_live _ _ _ pb nb); [exact INB2 | lia]. }
  (* [comment removed for export] *)
  destruct (af_frame_release RT AF Σ2 m5 f 0%nat (rt_frames RT Σ) ART5 ltac:(rewrite FRS2; exact FRS1)) as (Σ3 & fl & FLC & NAC & FL0 & FLW & FW & REL).
  change (fs_size 0) with 64 in FW. replace (f + 64 - 8) with (f + 56) in FW by lia. rewrite SP2, SP1 in FLW.
  assert (AG5 : forall a k, (usp1 <= a /\ a + k <= USTACK_TOP) -> agree_on (fun x => a <= x < a + k) m4 m5).
  { intros a k H. apply (agree_of_munch _ m4 m5 _ MU5). intros x Hx. cbv beta in Hx. cbn [outside]. unfold USTACK_TOP, RT_STACK, usp1 in *. lia. }
  assert (ST5 : stk asegs m5 lo usp1).
  { apply (stk_munch _ m4 m5 lo usp1 ST4 MU5 WM5). intros x Hx. cbn [outside]. unfold usp1 in Hx. lia. }
  assert (GAP5 : stk asegs m5 usp1 (usp + -128)).
  { apply (stk_agree_nw asegs m4 m5); [apply (stk_agree_nw asegs m3 m4); [apply (stk_agree_nw asegs m2 m3); [apply (stk_agree_nw asegs m1 m2 _ _ GAP1)|]|]|].
    - intros x Hx. cbv beta in Hx. apply PRES2. left. unfold USTACK_TOP in *. lia.
    - apply (agree_of_munch _ m2 m3 _ MU3). intros x Hx. cbv beta in Hx. cbn [outside]. unfold USTACK_TOP, RT_STACK, usp1 in *. lia.
    - replace (usp + -128) with (usp1 + (usp + -128 - usp1)) by lia. apply AG4. left. unfold USTACK_TOP, usp1 in *. lia.
    - replace (usp + -128) with (usp1 + (usp + -128 - usp1)) by lia. apply AG5. unfold USTACK_TOP, usp1 in *. lia. }
  assert (FR5 : rw_cells asegs m5 (usp + -128) [CB 24 j3; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m4 m5); [apply (rw_cells_agree asegs m3 m4 _ _ FR3); [| exact WM4] | | exact WM5].
    - apply AG4. left. cbn [cells_size csize Nat.add]. unfold USTACK_TOP, usp1 in *. lia.
    - apply AG5. cbn [cells_size csize Nat.add]. unfold USTACK_TOP, usp1 in *. lia. }
  (* [comment removed for export] *)
  pose proof (aa_s3_walk ra5 ra sp gp (Z_to_bv 64 0xba3ef0) v0 v1 v2 a1'' d2 d3 d4 d5 d6 d7 a4 a3 (Z_to_bv 64 fp) (Z_to_bv 64 64) (Z_to_bv 64 n) (Z_to_bv 64 (f + 32))
                (Z_to_bv 64 f) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 (fp / 8 + 2147450880)) v3 v4 v5 v6
                s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F4 fc4 m5 q f fl lo pad j3 HP ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia)
                ltac:(fold usp; unfold USTACK_TOP in *; lia) F0 ltac:(lia) FL0 ltac:(lia) ST5 GAP5 FR5 FW FLC MI5) as W3.
  fold usp usp1 in W3.
  cl_lift W3 Hc5' c6 Hc6.
  destruct (ASTA_unpack RT Σ2 _ _ c6 Hc6) as (ms6 & (y0 & y1 & y2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & y3 & y4 & y5 & y6 & m6 & -> & MU6 & WM6 & MI6 & ST6 & FLC6) & Hc6'). clear Hc6.
  fold usp in ST6.
  destruct (REL m6 MU6 WM6 FLC6) as (ART6 & FRS3 & LV3 & SP3 & CR3 & AL3 & AM3 & CG3).
  assert (LV3' : rt_live RT Σ3 = (q, n) :: rt_live RT Σ) by (rewrite LV3, LV2, LV1; reflexivity).
  assert (INQ3 : In (q, n) (rt_live RT Σ3)) by (rewrite LV3'; left; reflexivity).
  assert (NFL : forall x, aclient (rt_live RT Σ2) (rt_frames RT Σ2) usp1 x -> x <> fl).
  { intros x Hx E. subst x. apply NAC. destruct Hx as [H|H]; [exfalso; unfold usp1, RT_STACK in *; lia | right; exact H]. }
  assert (AG6 : forall a k, (forall x, a <= x < a + k -> x <> fl) -> agree_on (fun x => a <= x < a + k) m5 m6).
  { intros a k H. apply (agree_of_munch _ m5 m6 _ MU6). intros x Hx. cbv beta in Hx. specialize (H x Hx). cbn [outside]. lia. }
  apply Hk. exists Σ3, q.
  split; [| split; [exact LV3' | split; [rewrite FRS3; reflexivity | split; [rewrite SP3, SP2; exact SP1 | split; [rewrite CR3, CR2, CR1; lia |
            split; [exact Q0 | split; [exact Q64 | split; [exact QU | rewrite CG3, CG2; exact CG1]]]]]]]].
  eapply ASTA_conseq; [exact (ASTA_switch RT Σ2 Σ3 PMc _ c6 Hc6' AL3 AM3)|]. intros ms <-. exists m6.
  split; [exists y0, y1, y2, g1, g2, g3, g4, g5, g6, g7, y3, y4, y5, y6, F4, fc4; reflexivity|].
  split; [split; [exact ART6 | split; [exact MI6 | split; [exact (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 (wmono_trans asegs _ _ _ WM3
            (wmono_trans asegs _ _ _ WM4 (wmono_trans asegs _ _ _ WM5 WM6))))) | exact ST6]]]|].
  split.
  { intros a Ha Hnf.
    assert (A1 : aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp1 (bv_unsigned a))
      by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LV1; auto | rewrite FRS1; intros e He; right; exact He | unfold usp1; lia]).
    assert (A2 : aclient (rt_live RT Σ2) (rt_frames RT Σ2) usp1 (bv_unsigned a))
      by (apply (aclient_mono _ _ _ _ _ _ _ A1); [rewrite LV2; intros e He; right; exact He | rewrite FRS2; auto | lia]).
    destruct (newframe_apart RT AF Σ Σ1 m2 f 0%nat usp _ ART2 FRS1 LV1 SP1 ltac:(lia) Ha) as (N1 & N2).
    change (fs_size 0) with 64 in N1, N2. rewrite SHF in N2. unfold shad, SHB in N2.
    pose proof (cl_split RT AF Σ m usp 208 _ ART0 ltac:(lia) ltac:(lia) Ha) as N4.
    pose proof (NFL _ A2) as N5.
    rewrite (MU6 a ltac:(cbn [outside]; split; [lia | exact I])).
    rewrite (MU5 a ltac:(cbn [outside]; clear - N1 N2 Hnf; lia)).
    rewrite (PRES4 a A1 ltac:(clear - N1; lia)).
    rewrite (MU3 a ltac:(cbn [outside]; clear - N1 N2 N4 Hnf HP; lia)).
    rewrite (PRES2 a ltac:(apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto | auto | unfold usp1; lia])).
    exact (PR1 a Ha I). }
  split.
  { assert (ENV4 : cl_env m4 lb canary).
    { apply (cl_env_pres_ex _ _ _ (f + 32) 8 m3 m4 lb canary ENV3 PRES4).
      intros x Hx. pose proof (client_static_range x (cl_cell_static x Hx)). unfold SEGTOP_A in *. lia. }
    pose proof (cl_env_seg _ m4 m5 lb canary ENV4 MU5 ltac:(cl_fp_lia)) as ENV5.
    apply (cl_env_agree m5 m6 lb canary ENV5).
    intros a Ha. apply MU6. cbn [outside]. split; [| exact I]. intros Hin. apply NAC. right; left.
      replace fl with (bv_unsigned a) by lia. exact (cl_cell_static _ Ha). }
  split.
  { apply (rw_cells_agree asegs m5 m6 _ _ PC5); [| exact WM6]. apply AG6. intros x Hx. cbn [cells_size csize Nat.add] in Hx.
    apply NFL. apply (acl_live _ _ _ pb nb); [exact INB2 | lia]. }
  exact (af_acc_live RT AF Σ3 m6 q n ART6 INQ3).
Qed.

End CAlignedAlloc.
