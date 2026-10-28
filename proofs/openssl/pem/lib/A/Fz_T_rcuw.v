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
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_G_pkit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout Th_mutex Th_mutex_init Th_cond I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_G_kit Fz_ckit Fz_M_malloc Fz_M_zalloc Fz_env Fz_G_CRYPTO_calloc Fz_G_ossl_lib_ctx_get_concrete Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac tslia ::= wp_tslia.
Local Ltac zstore := zstep; fix_lit_store.
Local Ltac wg_T := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => ifT | |- _ => idtac end.
Local Ltac wg_F := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => ifF | |- _ => idtac end.
Notation TP_A := (0xba3ef0)%Z (only parsing).

Definition e_rcu_lock_new : Z := 0x1f5920.
Definition SITE_rcu_smalloc : Z := 0x1f5994.   (* [comment removed for export] *)
Definition SITE_rcu_memset : Z := 0x1f5a44.    (* [comment removed for export] *)
Definition SITE_rcu_getc : Z := 0x1f5a68.      (* [comment removed for export] *)
Definition SITE_rcu_zalloc : Z := 0x1f5a84.    (* [comment removed for export] *)
Definition SITE_rcu_calloc : Z := 0x1f5cfc.    (* [comment removed for export] *)
Definition SITE_rcu_release : Z := 0x1f5c64.   (* [comment removed for export] *)
Definition RCU_MAGIC : Z := 0x41b58ab3.
Definition RCU_RETIRED : Z := 0x45e0360e.
Definition RCU_DESCR : Z := 0x2b9d0.

(* [comment removed for export] *)
Local Ltac zgo p := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 p) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep; lfix
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [ifF | ifT | ubs_if] end).
(* [comment removed for export] *)
Local Ltac tleaf LF := tcall LF; [..| try th_ret_lit]; try first [eassumption | reflexivity | lia | split; eassumption]; cbv beta delta [mkR]; unfold mutex_cells, cond_cells in *.

Lemma rw_cells_blur_all : forall (m : mem) A cs, rw_cells asegs m A cs -> rw_cells asegs m A [CB (cells_size cs) (cells_bytes cs)].
Proof. intros m A cs H. apply (rw_cells_blur m A cs []). rewrite app_nil_r. exact H. Qed.

(* [comment removed for export] *)
Definition rcu_w0_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo pad : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a1' a2' : word) (j : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_rcu_smalloc) (Z_to_bv 64 (bv_unsigned sp + -160 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pad))
                 (Z_to_bv 64 96) a1' a2' a3 a4 a5 a6 a7 s2 a1 a0 s5 s6 s7 s8 s9 (Z_to_bv 64 0x7fff8000) s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (e_stack_malloc 1)) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 160, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -160) [CB 56 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk asegs m' (bv_unsigned sp + -160 - pad) (bv_unsigned sp + -160)
    /\ stk asegs m' lo (bv_unsigned sp + -160 - pad).

Lemma rcu_w0 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo pad : Z),
  (pad = 0 \/ pad = 16) -> bv_unsigned sp mod 32 = pad ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 176 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  ro_cells asegs m g_detect_stack_use_after_return [C4 (Z_to_bv 64 1)] -> mem_inv asegs m ->
  evt asegs (rcu_w0_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo pad m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_rcu_lock_new) fc None m (seg_rom asegs)).
Proof.
  intros until pad. intros HP HPM ST HLO HLOS SPH UT SHC UAR MI. unfold e_rcu_lock_new, g_shadow_memory_dynamic_address, g_detect_stack_use_after_return in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 160, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 160, SP)]) by ut_fp_lia.
  carve_frame 160%nat ST.
  zstep. zstep; lfix. do 14 zstep. zstep.
  rewrite (land_m32_pad (SP + -160) pad) by (first [lia | replace (SP + -160) with (SP + (-5) * 32) by lia; rewrite Z.mod_add by lia; exact HPM]).
  zgo 0x1f5988. zstep. if_false. zgo 0x1a6530.
  destruct (stk_split asegs _ lo (SP + -160 - pad) (SP + -160) ST ltac:(lia)) as [ST1 GAP].
  lazymatch goal with FRH : rw_cells asegs ?mm (SP + -160) (?c1 :: ?c2 :: ?rest) |- _ =>
    pose proof (rw_cells_blur mm (SP + -160) [c1; c2] rest FRH) as FRB end.
  cbn [cells_size csize Nat.add] in FRB.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold rcu_w0_post, SITE_rcu_smalloc, e_stack_malloc. apply evt_done. do 4 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact FRB|]. split; [exact GAP| exact ST1].
Qed.

(* [comment removed for export] *)
Definition rcu_w1_post (sp gp tp t0 t1 t2 s3 s4 s5 s6 s7 s11 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word) (F : bvmap 5 word) (fc : bv 32)
    (f lo pad : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a3' : word) (j fj sj : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_rcu_memset) (Z_to_bv 64 (bv_unsigned sp + -160 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pad))
                 (Z_to_bv 64 (bv_unsigned sp + -160 - pad + 40)) (Z_to_bv 64 0) (Z_to_bv 64 16) a3' a4 a5 a6 a7 (Z_to_bv 64 f) s3 s4 s5 s6 s7
                 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_asan_memset) fc None m' (seg_rom asegs)
    /\ munch [(f, f + 120); (f / 8 + 2147450880, f / 8 + 2147450880 + 16); (bv_unsigned sp - 160, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -160) [CB 56 j; C8 s11'; C8 s10'; C8 s9'; C8 s8'; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0]
    /\ rw_cells asegs m' f [CB 120 fj]
    /\ rw_cells asegs m' (f / 8 + 2147450880) [CB 16 sj].

Lemma rcu_w1 : forall ra0 sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6
    (s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word) (F : bvmap 5 word) fc (m : mem) (f lo pad : Z) (j fj sj : list byte),
  (pad = 0 \/ pad = 16) -> 0 < f -> f + 128 <= 2^47 ->
  (f + 120 <= 0x10000 \/ 0xbc6000 <= f) -> (f + 128 <= 0x7fff8000 \/ 0x10007fff8000 <= f) -> 0x10007fff8000 <= bv_unsigned sp - 176 -> bv_unsigned sp <= 2^47 ->
  (f + 128 <= bv_unsigned sp - 176 \/ bv_unsigned sp <= f) ->
  img_untouched m ->
  rw_cells asegs m (bv_unsigned sp + -160) [CB 56 j; C8 s11'; C8 s10'; C8 s9'; C8 s8'; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0] ->
  rw_cells asegs m f [CB 120 fj] -> rw_cells asegs m (f / 8 + 2147450880) [CB 16 sj] -> mem_inv asegs m ->
  evt asegs (rcu_w1_post sp gp tp t0 t1 t2 s3 s4 s5 s6 s7 s11 a4 a5 a6 a7 t3 t4 t5 t6 ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' F fc f lo pad m)
    (MS (mkR (Z_to_bv 64 SITE_rcu_smalloc) (Z_to_bv 64 (bv_unsigned sp + -160 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pad))
             (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 0x7fff8000) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_rcu_smalloc) fc None m (seg_rom asegs)).
Proof.
  intros until sj. intros HP F0 FH FIMG FSH SPL SPH FSEP UT FR FB SB MI. unfold SITE_rcu_smalloc in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(f, f + 120); (f / 8 + 2147450880, f / 8 + 2147450880 + 16); (SP - 160, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 16 <= 0x10007fff8000).
  { pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)). assert (f / 8 + 16 <= 2^44) by (Z.div_mod_to_equations; lia). lia. }
  assert (HWU : ut_fp [(f, f + 120); (f / 8 + 2147450880, f / 8 + 2147450880 + 16); (SP - 160, SP)]) by ut_fp_lia.
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  pose proof (div8_facts f) as Q1.
  zgo 0x1f59a4. zstep. if_true.
  destruct HP as [-> | ->].
  1: replace (SP + -160 - 0) with (SP + -160) by lia.
  2: replace (SP + -160 - 16) with (SP + -176) by lia.
  all: zgo 0x1f59d8.
  all: rewrite (shr3_div f) by lia.
  all: zgo 0x1c1dbc.
  1: replace (SP + -160) with (SP + -160 - 0) by lia; replace (SP + -120) with (SP + -160 - 0 + 40) by lia.
  2: replace (SP + -176) with (SP + -160 - 16) by lia; replace (SP + -136) with (SP + -160 - 16 + 40) by lia.
  all: pose proof (rw_cells_blur _ _ [_; _; _] _ FR) as FRB; cbn [cells_size csize Nat.add app] in FRB.
  all: pose proof (rw_cells_blur_all _ _ _ FB) as FBB; cbn [cells_size csize Nat.add app] in FBB.
  all: pose proof (rw_cells_blur_all _ _ _ SB) as SBB; cbn [cells_size csize Nat.add app] in SBB.
  all: subst; rewrite ?Z_to_bv_bv_unsigned.
  all: unfold rcu_w1_post, SITE_rcu_memset, e_asan_memset; apply evt_done; do 5 eexists; (split; [reflexivity|]).
  all: (split; [assumption|]); (split; [assumption|]); (split; [assumption|]); (split; [exact FRB|]); (split; [exact FBB| exact SBB]).
Qed.

(* [comment removed for export] *)
Definition rcu_w2_post (sp gp tp s3 s5 s6 s7 s11 : word) (F : bvmap 5 word) (fc : bv 32) (f lo pad : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fj sj : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_rcu_zalloc) (Z_to_bv 64 (bv_unsigned sp + -160 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pad))
                 (Z_to_bv 64 264) (Z_to_bv 64 0x491e0) (Z_to_bv 64 575) a3 a4 a5 a6 a7 (Z_to_bv 64 f) s3 (Z_to_bv 64 2) s3 s6 s7
                 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_CRYPTO_zalloc) fc None m' (seg_rom asegs)
    /\ munch [(f, f + 120); (f / 8 + 2147450880, f / 8 + 2147450880 + 16); (bv_unsigned sp - 160 - pad - 16, bv_unsigned sp - 160 - pad)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + -160 - pad)
    /\ rw_cells asegs m' f [CB 120 fj]
    /\ rw_cells asegs m' (f / 8 + 2147450880) [CB 16 sj].

Lemma rcu_w2 : forall sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (f lo pad : Z) (fj sj : list byte),
  (pad = 0 \/ pad = 16) -> lo <= bv_unsigned sp - 176 - 64 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  0 < f -> f + 128 <= lo -> (f + 128 <= 0x7fff8000 \/ 0x10007fff8000 <= f) -> bv_unsigned s3 <> 0 ->
  stk asegs m lo (bv_unsigned sp + -160 - pad) ->
  rw_cells asegs m f [CB 120 fj] -> rw_cells asegs m (f / 8 + 2147450880) [CB 16 sj] -> mem_inv asegs m ->
  evt asegs (rcu_w2_post sp gp tp s3 s5 s6 s7 s11 F fc f lo pad m)
    (MS (mkR (Z_to_bv 64 SITE_rcu_memset) (Z_to_bv 64 (bv_unsigned sp + -160 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pad))
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) s3 (Z_to_bv 64 1) s5 s6 s7 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_rcu_memset) fc None m (seg_rom asegs)).
Proof.
  intros until sj. intros HP HLO HLOS SPH F0 FLO FSH CTX0 ST1 FB SB MI. unfold SITE_rcu_memset in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl [(f, f + 120); (f / 8 + 2147450880, f / 8 + 2147450880 + 16); (SP - 160 - pad - 16, SP - 160 - pad)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (div8_facts f) as Q1.
  assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 16 <= 0x10007fff8000).
  { pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)). assert (f / 8 + 16 <= 2^44) by (Z.div_mod_to_equations; lia). lia. }
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 (SP + -160 - pad)) = SP + -160 - pad) by (apply unsigned_lit; lia).
  zgo 0x1f6b18.
  pose proof ossl_lib_ctx_get_concrete_s0_walk as LF. unfold SEGTOP_A in LF.
  tcall LF. all: try first [eassumption | reflexivity | lia].
  { rewrite bv_eqb_Z, (unsigned_lit 0) by lia. apply Z.eqb_neq. exact CTX0. }
  assert (BR0 : bv_eqb s3 (Z_to_bv 64 0) = false) by (rewrite bv_eqb_Z, (unsigned_lit 0) by lia; apply Z.eqb_neq; exact CTX0).
  zstep. rewrite BR0. cbv iota.
  zgo 0x1fbfec.
  pose proof (rw_cells_blur_all _ _ _ FB) as FBB; cbn [cells_size csize Nat.add app] in FBB.
  pose proof (rw_cells_blur_all _ _ _ SB) as SBB; cbn [cells_size csize Nat.add app] in SBB.
  subst SP.
  unfold rcu_w2_post, SITE_rcu_zalloc, e_CRYPTO_zalloc. apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact FBB| exact SBB].
Qed.

(* [comment removed for export] *)
Definition rcu_head_a (ctx : word) : list cell :=
  [CB 8 (repeat (Z_to_bv 8 0) 8); C8 ctx; CB 8 (repeat (Z_to_bv 8 0) 8); CB 4 (repeat (Z_to_bv 8 0) 4); CB 4 (repeat (Z_to_bv 8 0) 4); CB 16 (repeat (Z_to_bv 8 0) 16)].

Definition rcu_w3_post (sp gp tp s3 s11 : word) (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word) (F : bvmap 5 word) (fc : bv 32)
    (p f lo pad : Z) (canary : word) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j fj : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_rcu_calloc) (Z_to_bv 64 (bv_unsigned sp + -160 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pad))
                 (Z_to_bv 64 2) (Z_to_bv 64 8) (Z_to_bv 64 0x491e0) (Z_to_bv 64 460) a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 p) (Z_to_bv 64 2) (Z_to_bv 64 (p + 16))
                 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (p + 128)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (f + 64)) t3 t4 t5 t6)
            F (Z_to_bv 64 e_CRYPTO_calloc) fc None m' (seg_rom asegs)
    /\ munch [(p, p + 264); (f, f + 120); (bv_unsigned sp - 160 - pad - 64, bv_unsigned sp - 160 - pad); (bv_unsigned sp - 160, bv_unsigned sp)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + -160 - pad) /\ ssp_cells m' canary
    /\ rw_cells asegs m' (bv_unsigned sp + -160) [CB 56 j; C8 s11'; C8 s10'; C8 s9'; C8 s8'; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0]
    /\ rw_cells asegs m' f [CB 120 fj]
    /\ rw_cells asegs m' p (rcu_head_a s3)
    /\ rw_cells asegs m' (p + 48) (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) /\ rw_cells asegs m' (p + 88) (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
    /\ rw_cells asegs m' (p + 128) cond_cells
    /\ rw_cells asegs m' (p + 176) (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) /\ rw_cells asegs m' (p + 216) cond_cells.

Lemma rcu_w3 : forall ra0 sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 s11 t3 t4 t5 t6
    (s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word) (F : bvmap 5 word) fc (m : mem) (p f lo pad : Z) (j fj : list byte) (canary : word),
  (pad = 0 \/ pad = 16) -> lo <= bv_unsigned sp - 176 - 64 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  0x10007fff8000 <= p -> p + 264 <= lo -> p mod 8 = 0 ->
  0 < f -> 0xbc6000 <= f -> f + 128 <= lo -> (f + 128 <= 0x7fff8000 \/ 0x10007fff8000 <= f) -> (p + 264 <= f \/ f + 128 <= p) ->
  stk asegs m lo (bv_unsigned sp + -160 - pad) ->
  rw_cells asegs m (bv_unsigned sp + -160) [CB 56 j; C8 s11'; C8 s10'; C8 s9'; C8 s8'; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0] ->
  rw_cells asegs m f [CB 120 fj] ->
  rw_cells asegs m p [CB 264 (repeat (Z_to_bv 8 0) 264)] -> acc asegs m p 264 ->
  ssp_cells m canary -> mem_inv asegs m ->
  evt asegs (rcu_w3_post sp gp tp s3 s11 ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' F fc p f lo pad canary m)
    (MS (mkR (Z_to_bv 64 SITE_rcu_zalloc) (Z_to_bv 64 (bv_unsigned sp + -160 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pad))
             (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) s3 (Z_to_bv 64 2) s3 s6 s7 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_rcu_zalloc) fc None m (seg_rom asegs)).
Proof.
  intros until canary. intros HP HLO HLOS SPH PHI PLO PAL F0 FIMG FLO FSH PF ST1 FR FB HB ACC SSP MI. unfold SITE_rcu_zalloc in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl [(p, p + 264); (f, f + 120); (SP - 160 - pad - 64, SP - 160 - pad); (SP - 160, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  pose proof (div8_facts f) as Q1.
  pose proof SSP as SSP2. destruct SSP2 as [SSG SSC]. unfold got_ssp, ssp_guard in SSG, SSC.
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EUp : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 (SP + -160 - pad)) = SP + -160 - pad) by (apply unsigned_lit; lia).
  apply (rw_cells_split_CB asegs _ _ [] 264 _ [] [8; 8; 8; 4; 4; 16; 40; 40; 48; 40; 48]%nat) in HB; [| reflexivity]. cbn [mk_CB_cells app firstn skipn repeat] in HB.
  destruct (proj1 (rw_cells_app m p [_; _; _; _; _; _] _) HB) as [HB0 HB1]. clear HB. cbn [cells_size csize Nat.add] in HB1.
  destruct (proj1 (rw_cells_app m _ [_] _) HB1) as [HM1 HB2]. clear HB1. cbn [cells_size csize Nat.add] in HB2.
  destruct (proj1 (rw_cells_app m _ [_] _) HB2) as [HM2 HB3]. clear HB2. cbn [cells_size csize Nat.add] in HB3.
  destruct (proj1 (rw_cells_app m _ [_] _) HB3) as [HC1 HB4]. clear HB3. cbn [cells_size csize Nat.add] in HB4.
  destruct (proj1 (rw_cells_app m _ [_] _) HB4) as [HM3 HC2]. clear HB4. cbn [cells_size csize Nat.add] in HC2.
  replace (p + 48 + 40) with (p + 88) in HM2 by lia. replace (p + 48 + 40 + 40) with (p + 128) in HC1 by lia.
  replace (p + 48 + 40 + 40 + 48) with (p + 176) in HM3 by lia. replace (p + 48 + 40 + 40 + 48 + 40) with (p + 216) in HC2 by lia.
  change (p + Z.of_nat 48) with (p + 48) in HM1.
  pose proof mutex_init_null_proof as LM. unfold mutex_init_null_stmt, got_ssp, ssp_guard in LM.
  pose proof cond_init_null_proof as LC. unfold cond_init_null_stmt, got_ssp, ssp_guard in LC.
  zgo 0x1f5a9c. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0.
  zgo 0x529888. tleaf LM. rename POST into PM1. try clear SSP.
  destruct HP as [-> | ->].
  1: replace (SP + -160 - 0) with (SP + -160) in * by lia.
  2: replace (SP + -160 - 16) with (SP + -176) in * by lia.
  all: zgo 0x529888; tleaf LM; rename POST into PM2.
  all: zgo 0x529888; tleaf LM; rename POST into PM3.
  all: zgo 0x527a64; tleaf LC; rename POST into QC1.
  all: zgo 0x527a64; tleaf LC; rename POST into QC2.
  all: zgo 0x201580.
  1: pose proof (rw_cells_blur _ _ [_; _; _; _] _ FR) as FRB.
  2: pose proof (rw_cells_blur _ _ [_; _; _; _; _] _ FR) as FRB.
  all: cbn [cells_size csize Nat.add app] in FRB.
  all: pose proof (rw_cells_blur_all _ _ _ FB) as FBB; cbn [cells_size csize Nat.add app] in FBB.
  1: replace (SP + -160) with (SP + -160 - 0) by lia.
  2: replace (SP + -176) with (SP + -160 - 16) by lia.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (SSP' : ssp_cells mm canary) by (split; assumption) end.
  all: subst SP; unfold rcu_w3_post, SITE_rcu_calloc, e_CRYPTO_calloc, rcu_head_a; apply evt_done; do 14 eexists; (split; [reflexivity|]).
  all: (split; [eapply munch_weaken; [| exact MU]; intros xw Hxw; cbn [outside] in *; lia|]); (split; [assumption|]); (split; [assumption|]).
  1: rewrite Z.sub_0_r. 2: replace (bv_unsigned sp + -160 - 16) with (bv_unsigned sp + -176) by lia.
  all: (split; [assumption|]); (split; [exact SSP'|]); (split; [exact FRB|]); (split; [exact FBB|]); (split; [exact HB0|]).
  all: repeat (split; [assumption|]); assumption.
Qed.

(* [comment removed for export] *)
Definition rcu_head (ctx : word) (q : Z) : list cell :=
  [CB 8 (repeat (Z_to_bv 8 0) 8); C8 ctx; C8 (Z_to_bv 64 q); CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 2); CB 16 (repeat (Z_to_bv 8 0) 16)].
Definition SITE_rcu_retire : Z := 0x1f5c04.

Definition rcu_w4_post (sp gp tp s3 t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (p q f lo pad : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a1 a2 : word) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_rcu_calloc) (Z_to_bv 64 (bv_unsigned sp + -160 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pad))
                 (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 p) (Z_to_bv 64 2) (Z_to_bv 64 (p + 16))
                 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (p + 128)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (f + 64)) t3 t4 t5 t6)
            F (Z_to_bv 64 SITE_rcu_retire) fc None m' (seg_rom asegs)
    /\ munch [(p, p + 48)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + -160 - pad)
    /\ rw_cells asegs m' p (rcu_head s3 q).

Lemma rcu_w4 : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p q f lo pad : Z),
  lo <= bv_unsigned sp - 176 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  0x10007fff8000 <= p -> p + 264 <= lo -> p mod 8 = 0 -> 0 < q -> q + 16 <= lo -> 0 < f -> f + 128 <= lo ->
  stk asegs m lo (bv_unsigned sp + -160 - pad) ->
  rw_cells asegs m p (rcu_head_a s3) -> acc asegs m p 264 -> mem_inv asegs m ->
  evt asegs (rcu_w4_post sp gp tp s3 t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc p q f lo pad m)
    (MS (mkR (Z_to_bv 64 SITE_rcu_calloc) (Z_to_bv 64 (bv_unsigned sp + -160 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pad))
             (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 p) (Z_to_bv 64 2) (Z_to_bv 64 (p + 16))
             (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (p + 128)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (f + 64)) t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_rcu_calloc) fc None m (seg_rom asegs)).
Proof.
  intros until pad. intros HLO HLOS SPH PHI PLO PAL Q0 QLO F0 FLO ST1 HB0 ACC MI. unfold SITE_rcu_calloc in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl [(p, p + 48)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EUp : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  unfold rcu_head_a in HB0.
  zgo 0x1f5d0c.
  change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0).
  zgo 0x1f5d20. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0.
  zgo 0x1f5c04.
  subst SP. unfold rcu_w4_post, SITE_rcu_retire, rcu_head. apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [assumption|]. split; [assumption|]. split; [assumption| exact HB0].
Qed.
(* [comment removed for export] *)
Definition rcu_w5_post (sp gp tp a0 a1 a2 a3 a4 a5 a6 a7 s3 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (p f lo pad : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a0' : word) (fj sj : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_rcu_calloc) (Z_to_bv 64 (bv_unsigned sp + -160 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pad))
                 a0' a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 p) (Z_to_bv 64 2) (Z_to_bv 64 (p + 16))
                 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (p + 128)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (f + 64)) t3 t4 t5 t6)
            F (Z_to_bv 64 SITE_rcu_release) fc None m' (seg_rom asegs)
    /\ munch [(f, f + 120); (f / 8 + 2147450880, f / 8 + 2147450880 + 16)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + -160 - pad)
    /\ rw_cells asegs m' f [CB 120 fj]
    /\ rw_cells asegs m' (f / 8 + 2147450880) [CB 16 sj].

Lemma rcu_w5 : forall sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p f lo pad : Z) (fj sj : list byte),
  lo <= bv_unsigned sp - 176 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  0 < f -> 0xbc6000 <= f -> f + 128 <= lo -> (f + 128 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  stk asegs m lo (bv_unsigned sp + -160 - pad) ->
  rw_cells asegs m f [CB 120 fj] -> rw_cells asegs m (f / 8 + 2147450880) [CB 16 sj] -> mem_inv asegs m ->
  evt asegs (rcu_w5_post sp gp tp a0 a1 a2 a3 a4 a5 a6 a7 s3 t0 t1 t2 t3 t4 t5 t6 F fc p f lo pad m)
    (MS (mkR (Z_to_bv 64 SITE_rcu_calloc) (Z_to_bv 64 (bv_unsigned sp + -160 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pad))
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 p) (Z_to_bv 64 2) (Z_to_bv 64 (p + 16))
             (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (p + 128)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (f + 64)) t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_rcu_retire) fc None m (seg_rom asegs)).
Proof.
  intros until sj. intros HLO HLOS SPH F0 FIMG FLO FSH ST1 FB SB MI. unfold SITE_rcu_retire in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl [(f, f + 120); (f / 8 + 2147450880, f / 8 + 2147450880 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (div8_facts f) as Q1.
  assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 16 <= 0x10007fff8000).
  { pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)). assert (f / 8 + 16 <= 2^44) by (Z.div_mod_to_equations; lia). lia. }
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  zgo 0x1f5c64.
  pose proof (rw_cells_blur_all _ _ _ FB) as FBB; cbn [cells_size csize Nat.add app] in FBB.
  pose proof (rw_cells_blur_all _ _ _ SB) as SBB; cbn [cells_size csize Nat.add app] in SBB.
  subst SP. unfold rcu_w5_post, SITE_rcu_release. apply evt_done. do 4 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact FBB| exact SBB].
Qed.
(* [comment removed for export] *)
Definition rcu_w6_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (p fl lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3 t4 t5 t6)
            F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(fl, fl + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' fl [C1 (Z_to_bv 8 0)].

Lemma rcu_w6 : forall ra0 sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word) (F : bvmap 5 word) fc (m : mem) (p f fl lo pad : Z) (j : list byte),
  (pad = 0 \/ pad = 16) -> lo <= bv_unsigned sp - 176 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  0 < f -> f + 128 <= lo -> 0 < fl -> fl + 1 <= lo ->
  stk asegs m lo (bv_unsigned sp + -160 - pad) -> stk asegs m (bv_unsigned sp + -160 - pad) (bv_unsigned sp + -160) ->
  rw_cells asegs m (bv_unsigned sp + -160) [CB 56 j; C8 s11'; C8 s10'; C8 s9'; C8 s8'; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0] ->
  ro_cells asegs m (f + 120) [C8 (Z_to_bv 64 fl)] -> rw_cells asegs m fl [C1 (Z_to_bv 8 1)] -> mem_inv asegs m ->
  evt asegs (rcu_w6_post ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc p fl lo m)
    (MS (mkR (Z_to_bv 64 SITE_rcu_calloc) (Z_to_bv 64 (bv_unsigned sp + -160 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pad))
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 p) (Z_to_bv 64 2) (Z_to_bv 64 (p + 16))
             (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (p + 128)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (f + 64)) t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_rcu_release) fc None m (seg_rom asegs)).
Proof.
  intros until j. intros HP HLO HLOS SPH F0 FLO FL0 FLLO ST1 GAP FR FLG FLB MI. unfold SITE_rcu_release in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EUfl : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply unsigned_lit; lia).
  zstep. clear FLG.
  zstep; lfix.
  zgo 0x1f5ca8.
  pose proof (stk_merge asegs _ lo (SP + -160 - pad) (SP + -160) ST1 GAP ltac:(lia)) as ST2.
  zgo 0x1f5ce0.
  release_frame FR ST2 SP.
  zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold rcu_w6_post. apply evt_done. eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption| assumption].
Qed.
