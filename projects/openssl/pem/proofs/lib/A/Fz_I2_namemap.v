(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Fz_G_pkit Fz_T_kit.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout Th_mutex Th_mutex_init Th_cond I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_G_kit Fz_ckit Fz_M_malloc Fz_M_zalloc Fz_env Fz_M_locknew Fz_M_aligned Fz_M_aligned_array Fz_G_CRYPTO_calloc Fz_G_ossl_lib_ctx_get_concrete Fz_T_rcuw Fz_T_rcu Fz_I2_anl Fz_I2_htw Fz_I2_htnew Fz_G_OPENSSL_sk_new_null Fz_G_OPENSSL_sk_set_cmp_thunks Fz_G_OPENSSL_sk_set_copy_thunks Fz_G_OPENSSL_sk_set_thunks Fz_I2_nmw Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Notation TP_A := (0xba3ef0)%Z (only parsing).

(* [comment removed for export] *)
Lemma ubs_raw8 : forall p, p mod 8 = 0 -> negb (bv_eqb (Z_to_bv 64 (Z.land p 7)) (Z_to_bv 64 0)) = false.
Proof. intros p H. rewrite (ubs_land7 p H). reflexivity. Qed.

Section NamemapNew.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis SM1 : stack_malloc_contract RT 1.
Hypothesis MSET : memset_icontract RT e_asan_memset.
Hypothesis C_CZ : crypto_zalloc_env_stmt RT.
Hypothesis C_LN : crypto_lock_new_env_stmt RT.
Hypothesis C_HT : ht_new_stmt RT.
Hypothesis C_SKN : OPENSSL_sk_new_null_stmt RT.
Hypothesis C_SKCMP : OPENSSL_sk_set_cmp_thunks_stmt RT.
Hypothesis C_SKCPY : OPENSSL_sk_set_copy_thunks_stmt RT.
Hypothesis C_SKSET : OPENSSL_sk_set_thunks_stmt RT.

Definition NM_SITES : list (Z * Z) :=
  [(SITE_nm_zalloc, e_namemap_new); (SITE_nm_locknew, e_namemap_new); (SITE_nm_htnew, e_namemap_new); (SITE_nm_sknew, e_namemap_new);
   (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc); (SITE_ln_zalloc, e_lock_new); (SITE_OPENSSL_sk_new_null_1, e_OPENSSL_sk_new_null)] ++ HT_SITES.
Definition NM_CALLS : list (Z * Z) :=
  [(SITE_nm_zalloc, e_CRYPTO_zalloc); (SITE_nm_locknew, e_lock_new); (SITE_nm_htnew, e_ht_new); (SITE_nm_sknew, e_OPENSSL_sk_new_null);
   (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc); (SITE_ln_zalloc, e_CRYPTO_zalloc); (SITE_OPENSSL_sk_new_null_1, e_CRYPTO_zalloc)] ++ HT_CALLS.
Definition NM_COST : Z := 1 + mcost 40 + 1 + HT_COST + mcost 56.
Definition nm_sk_cells : list cell :=
  [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 NM_CMP_THUNK); C8 (Z_to_bv 64 NM_SET_THUNK); C8 (Z_to_bv 64 NM_COPY_THUNK)].

(* [comment removed for export] *)
Definition namemap_new_stmt : Prop :=
  forall (Σ : rts RT) (PMc : Model -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc ->
  bv_unsigned a0 <> 0 ->
  tp = Z_to_bv 64 TP_A ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  lo + RT_STACK + 768 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_namemap_new (bv_unsigned ra :: outer) ->
  uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) NM_SITES NM_CALLS ->
  (length (rt_frames RT Σ) + 1 < FRAMES_MAX)%nat ->
  Z.of_nat (length (rt_live RT Σ)) + 8 < LIVE_MAX ->
  NM_COST <= rt_credit RT Σ ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_namemap_new m)))
    (fun c => exists (Σ' : rts RT) (p lk h hlk md nb rl rq sk : Z),
       ASTA RT Σ' PMc
         (fun ms => exists m' : mem,
            ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
            /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
            /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
            /\ cl_env m' (Z_to_bv 8 1) canary
            /\ rw_cells asegs m' p [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 h); C8 (Z_to_bv 64 lk); C8 (Z_to_bv 64 sk); C8 (Z_to_bv 64 0)]
            /\ acc asegs m' p 40
            /\ rw_cells asegs m' lk (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) /\ acc asegs m' lk 40
            /\ rw_cells asegs m' h (ht_tab4 a0 rl hlk md) /\ acc asegs m' h 96
            /\ rw_cells asegs m' hlk (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) /\ acc asegs m' hlk 40
            /\ rw_cells asegs m' md [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 511)] /\ acc asegs m' md 24
            /\ rw_cells asegs m' nb [CB (Z.to_nat NB_BYTES) (repeat (Z_to_bv 8 0) (Z.to_nat NB_BYTES))] /\ acc asegs m' nb NB_BYTES
            /\ rw_cells asegs m' rl (rcu_head a0 rq)
            /\ rw_cells asegs m' (rl + 48) (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
            /\ rw_cells asegs m' (rl + 88) (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
            /\ rw_cells asegs m' (rl + 128) cond_cells
            /\ rw_cells asegs m' (rl + 176) (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
            /\ rw_cells asegs m' (rl + 216) cond_cells
            /\ acc asegs m' rl 264
            /\ rw_cells asegs m' rq [CB 16 (repeat (Z_to_bv 8 0) 16)] /\ acc asegs m' rq 16
            /\ rw_cells asegs m' sk nm_sk_cells /\ acc asegs m' sk 56) c
       /\ rt_live RT Σ' = (sk, 56) :: (rq, 16) :: (rl, 264) :: (nb, NB_BYTES) :: (md, 24) :: (hlk, 40) :: (h, 96) :: (lk, 40) :: (p, 40) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ
       /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - NM_COST
       /\ 0 < p /\ p mod 16 = 0 /\ p + 40 < USTACK_TOP
       /\ 0 < lk /\ lk mod 16 = 0 /\ lk + 40 < USTACK_TOP
       /\ 0 < h /\ h mod 16 = 0 /\ h + 96 < USTACK_TOP
       /\ 0 < hlk /\ hlk mod 16 = 0 /\ hlk + 40 < USTACK_TOP
       /\ 0 < md /\ md mod 16 = 0 /\ md + 24 < USTACK_TOP
       /\ 0 < nb /\ nb mod 64 = 0 /\ nb + NB_BYTES < USTACK_TOP
       /\ 0 < rl /\ rl mod 16 = 0 /\ rl + 264 < USTACK_TOP
       /\ 0 < rq /\ rq mod 16 = 0 /\ rq + 16 < USTACK_TOP
       /\ 0 < sk /\ sk mod 16 = 0 /\ sk + 56 < USTACK_TOP
       /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem namemap_new_cps : namemap_new_stmt.
Proof using AF AFP SM1 MSET C_CZ C_LN C_HT C_SKN C_SKCMP C_SKCPY C_SKSET.
  unfold namemap_new_stmt.
  intros R0 Pm ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary
    only_fd stable ctx_set tp_val art_m inv_m callok room cgctx_m chain_m cghas_m few_frames few_live enough_credit env_m
    T c at_entry k_done.
  subst tp.
  destruct callok as (stk_m & lo_win & lo_room & sp_top & sp_al16).
  pose proof (af_sp0_win RT AF R0 m art_m) as sp0_low.
  pose proof (af_sp0_range RT AF R0 m art_m) as (_ & sp0_high).
  pose proof (af_client_consts RT AF R0 m art_m) as (_ & shadow_off & _ & uar_on & untouched_m).
  unfold RT_STACK, STACK_WIN, USTACK_TOP in *.
  remember (bv_unsigned sp mod 32) as pad eqn:pad_is.
  assert (pad_two : pad = 0 \/ pad = 16) by (subst pad; clear - sp_al16; lia).
  assert (lo_floor : 140735332483072 <= lo) by (clear - lo_win sp0_low; lia).
  assert (fsp_val : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) = bv_unsigned sp + -96 - pad)
    by (apply unsigned_lit; clear - pad_two sp_top lo_floor room; lia).
  assert (wr_sub : forall mm a n b k, wr_at asegs mm a n -> 0 <= b -> 0 <= k -> b + k <= n -> wr_at asegs mm (a + b) k).
  { intros mm a n b k (a_lo & a_hi & views) b_lo k_lo fits. split; [lia|]. split; [lia|].
    intros i i_rng. replace (a + b + i) with (a + (b + i)) by lia. apply views. lia. }
  (* prologue: frame, saved registers, fake-stack request *)
  pose proof (nm_w0 ra sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pad
                pad_two (eq_sym pad_is) stk_m ltac:(clear - room; lia) ltac:(clear - lo_floor; lia) ltac:(clear - sp_top; lia)
                untouched_m shadow_off uar_on inv_m) as step.
  cl_lift step at_entry c1 at_c1.
  destruct (ASTA_unpack RT R0 Pm _ c1 at_c1)
    as (ms1 & (a1_w0 & a2_w0 & spill_w0 & mw0 & -> & mu_w0 & wm_w0 & inv_w0 & regs_w0 & padgap_w0 & stk_w0) & at_c1').
  clear at_c1.
  assert (art_w0 : ART RT R0 mw0).
  { apply (af_frame RT AF R0 m mw0 lo art_m lo_win); [| exact wm_w0].
    intros a not_cl. apply mu_w0. cbn [outside]. split; [| exact I].
    intros in_frame. apply not_cl, acl_stack. unfold USTACK_TOP. clear - in_frame room sp_top. lia. }
  assert (cok_w0 : call_ok RT R0 mw0 (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) lo).
  { unfold call_ok. rewrite fsp_val. split; [exact stk_w0|].
    unfold RT_STACK, STACK_WIN, USTACK_TOP. clear - lo_win room sp_top pad_is pad_two sp_al16. repeat split; lia. }
  refine (SM1 R0 Pm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mw0 lo only_fd stable
            (or_intror (or_introl eq_refl)) eq_refl ltac:(clear - few_frames; lia)
            ltac:(unfold NM_COST, HT_COST in enough_credit; cbv [mcost] in enough_credit; cbn in enough_credit; clear - enough_credit; lia)
            art_w0 inv_w0 cok_w0 T c1 at_c1' _).
  intros c2 after_sm.
  destruct after_sm as (R1 & fb & at_c2 & frames_R1 & live_R1 & sp0_R1 & credit_R1 & fb_pos & fb_al & fb_top & cg_R1).
  destruct (ASTA_unpack RT R1 Pm _ c2 at_c2) as (ms2 & (mk1 & ret_k1 & aft_k1 & pres_k1 & wr_fb & wr_fbsh) & at_c2').
  clear at_c2.
  destruct ret_k1 as (t0_1 & t1_1 & t2_1 & a1_1 & a2_1 & a3_1 & a4_1 & a5_1 & a6_1 & a7_1 & t3_1 & t4_1 & t5_1 & t6_1 & F_1 & fc_1 & ->).
  destruct aft_k1 as (art_k1 & inv_k1 & wm_k1 & stk_k1).
  rewrite (ret_pc_even SITE_nm_smalloc) in at_c2' by (unfold SITE_nm_smalloc; lia).
  rewrite fsp_val in stk_k1, pres_k1.
  change (fs_size 1 - 8) with 120 in wr_fb. change (fs_size 1 / 8) with 16 in wr_fbsh. unfold shad, SHB in wr_fbsh.
  change (fs_size 1) with 128 in fb_top.
  assert (fb_in1 : In (fb, 1%nat) (rt_frames RT R1)) by (rewrite frames_R1; left; reflexivity).
  pose proof (af_frames_range RT AF R1 mk1 fb 1 art_k1 fb_in1) as (_ & fb_win & _ & fb_sep).
  pose proof (af_frames_hi RT AF R1 mk1 fb 1 art_k1 fb_in1) as fb_hi.
  pose proof (af_frames_align RT AF R1 mk1 fb 1 art_k1 fb_in1) as (_ & fb_seg).
  change (fs_size 1) with 128 in fb_win, fb_hi, fb_sep. unfold SEGTOP_A in fb_seg. unfold STACK_WIN in fb_win.
  rewrite sp0_R1 in fb_win.
  assert (lo_win1 : rt_sp0 RT R1 - 8388608 <= lo) by (rewrite sp0_R1; exact lo_win).
  (* everything at or above the new stack pointer is client memory for the callee *)
  assert (upper_cl : forall live frames y, bv_unsigned sp + -96 - pad <= y < bv_unsigned sp -> aclient live frames (bv_unsigned sp + -96 - pad) y).
  { intros live frames y y_rng. apply acl_stack. unfold USTACK_TOP. clear - y_rng sp_top. lia. }
  assert (regs_k1 : rw_cells asegs mk1 (bv_unsigned sp + -96) [CB 24 spill_w0; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs mw0 mk1 _ _ regs_w0); [| exact wm_k1].
    apply (agree_of_pres _ _ _ _ _ _ pres_k1). intros x x_in. cbn [cells_size csize Nat.add] in x_in.
    apply upper_cl. clear - x_in pad_two. lia. }
  assert (padgap_k1 : stk asegs mk1 (bv_unsigned sp + -96 - pad) (bv_unsigned sp + -96)).
  { apply (stk_agree asegs mw0 mk1 _ _ padgap_w0); [| exact wm_k1].
    apply (agree_of_pres _ _ _ _ _ _ pres_k1). intros x x_in. apply upper_cl. clear - x_in pad_two. lia. }
  pose proof (af_client_consts RT AF R1 mk1 art_k1) as (_ & _ & _ & _ & untouched_k1).
  destruct (wr_at_rw_CB mk1 fb 120 wr_fb ltac:(lia)) as (fjunk & fcell_k1).
  destruct (wr_at_rw_CB mk1 (fb / 8 + 2147450880) 16 wr_fbsh ltac:(lia)) as (sjunk & scell_k1).
  (* fake-frame descriptor and shadow poisoning, up to the clearing of the config tail *)
  pose proof (nm_w1 ra sp gp (Z_to_bv 64 TP_A) t0_1 t1_1 t2_1 a1_1 a2_1 a3_1 a4_1 a5_1 a6_1 a7_1 s2 a0 s4 s5 s6 s8 s9 s10 s11 t3_1 t4_1 t5_1 t6_1
                s0 s1 s2 s3 s4 s5 s6 s7 F_1 fc_1 mk1 fb lo pad spill_w0 fjunk sjunk
                pad_two fb_pos ltac:(clear - fb_win sp0_high; lia) ltac:(clear - fb_seg; lia) ltac:(clear - fb_hi; lia)
                ltac:(clear - lo_floor room; lia) ltac:(clear - sp_top; lia) ltac:(clear - fb_win lo_win room; lia)
                untouched_k1 regs_k1 fcell_k1 scell_k1 inv_k1) as step.
  cl_lift step at_c2' c3 at_c3.
  destruct (ASTA_unpack RT R1 Pm _ c3 at_c3)
    as (ms3 & (spill_w1 & fj_w1 & mw1 & -> & mu_w1 & wm_w1 & inv_w1 & regs_w1 & fcell_w1 & shadow_w1) & at_c3').
  clear at_c3.
  assert (frame_cl : forall live sp' y, fb <= y < fb + 120 -> aclient live (rt_frames RT R1) sp' y).
  { intros live sp' y y_rng. apply (acl_frame _ _ _ fb 1%nat); [exact fb_in1|]. change (fs_size 1) with 128. clear - y_rng. lia. }
  assert (fshadow_cl : forall live sp' y, fb / 8 + 2147450880 <= y < fb / 8 + 2147450880 + 16 -> aclient live (rt_frames RT R1) sp' y).
  { intros live sp' y y_rng. apply (acl_fshadow _ _ _ fb 1%nat); [exact fb_in1|].
    unfold shad, SHB. change (fs_size 1) with 128. clear - y_rng. lia. }
  assert (art_w1 : ART RT R1 mw1).
  { apply (af_frame RT AF R1 mk1 mw1 lo art_k1 lo_win1); [| exact wm_w1].
    intros a not_cl. apply mu_w1. cbn [outside].
    split; [| split; [| split; [| exact I]]]; intros inside; apply not_cl.
    - apply frame_cl. exact inside.
    - apply fshadow_cl. exact inside.
    - apply acl_stack. unfold USTACK_TOP. clear - inside room sp_top. lia. }
  assert (stk_w1 : stk asegs mw1 lo (bv_unsigned sp + -96 - pad)).
  { apply (stk_munch _ mk1 mw1 _ _ stk_k1 mu_w1 wm_w1). intros x x_rng. cbn [outside].
    clear - x_rng fb_win lo_win lo_floor sp0_high pad_two. repeat split; lia. }
  assert (padgap_w1 : stk asegs mw1 (bv_unsigned sp + -96 - pad) (bv_unsigned sp + -96)).
  { apply (stk_munch _ mk1 mw1 _ _ padgap_k1 mu_w1 wm_w1). intros x x_rng. cbn [outside].
    clear - x_rng fb_win lo_win lo_floor room sp0_high pad_two. repeat split; lia. }
  assert (cok_w1 : call_ok RT R1 mw1 (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) lo).
  { unfold call_ok. rewrite fsp_val, sp0_R1. split; [exact stk_w1|].
    unfold RT_STACK, STACK_WIN, USTACK_TOP. clear - lo_win room sp_top pad_is pad_two sp_al16. repeat split; lia. }
  (* the 40 config bytes after the context pointer are addressable: shadow bytes 5..9 of the fake frame are clear *)
  assert (acc_cfg : acc asegs mw1 (fb + 40) 40).
  { apply acc_ushadow; [clear - fb_al; lia | clear - fb_pos; lia | lia |].
    replace (shad (fb + 40)) with (fb / 8 + 2147450880 + Z.of_nat (cells_size (firstn 5 nm_shadow)))
      by (unfold shad, SHB; cbn [firstn nm_shadow cells_size csize Nat.add]; clear - fb_al; lia).
    pose proof (rw_cells_skip mw1 _ (firstn 5 nm_shadow) (skipn 5 nm_shadow) shadow_w1) as tail_sh.
    pose proof (rw_cells_bytes_at _ _ _ _ (proj1 (proj1 (rw_cells_app mw1 _ (firstn 5 (skipn 5 nm_shadow)) (skipn 5 (skipn 5 nm_shadow))) tail_sh))) as five.
    exact five. }
  assert (wr_fb_w1 : wr_at asegs mw1 fb 120) by exact (wr_at_wm mk1 mw1 fb 120 wr_fb wm_w1).
  assert (chk_cfg : checked_dst RT R1 mw1 (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) (fb + 40) 40).
  { unfold checked_dst. rewrite fsp_val. split; [intros _; split; [exact acc_cfg|] | split].
    - unfold rng_class. right; left. exists fb, 1%nat. split; [exact fb_in1|]. change (fs_size 1) with 128. lia.
    - intros i i_rng. apply frame_cl. clear - i_rng. lia.
    - exact (wr_sub mw1 fb 120 40 40 wr_fb_w1 ltac:(lia) ltac:(lia) ltac:(lia)). }
  refine (MSET R1 Pm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mw1
            (fb + 40) 40 (Z_to_bv 8 0) lo only_fd stable eq_refl eq_refl eq_refl
            ltac:(clear - fb_win sp0_high fb_pos; lia) ltac:(lia) chk_cfg art_w1 inv_w1 cok_w1 T c3 at_c3' _).
  intros c4 after_ms. unfold icpt_post in after_ms.
  destruct (ASTA_unpack RT R1 Pm _ c4 after_ms) as (ms4 & (mk2 & ret_k2 & aft_k2 & pres_k2 & zero_k2) & at_c4').
  clear after_ms.
  destruct ret_k2 as (t0_2 & t1_2 & t2_2 & a1_2 & a2_2 & a3_2 & a4_2 & a5_2 & a6_2 & a7_2 & t3_2 & t4_2 & t5_2 & t6_2 & F_2 & fc_2 & ->).
  destruct aft_k2 as (art_k2 & inv_k2 & wm_k2 & stk_k2).
  rewrite (ret_pc_even SITE_nm_memset) in at_c4' by (unfold SITE_nm_memset; lia).
  rewrite fsp_val in stk_k2, pres_k2.
  (* the memset only wrote its own 40 bytes: carry what lies elsewhere *)
  assert (ms_keep : forall P : Z -> Prop,
            (forall x, P x -> aclient (rt_live RT R1) (rt_frames RT R1) (bv_unsigned sp + -96 - pad) x /\ ~ (fb + 40 <= x < fb + 40 + 40)) ->
            agree_on P mw1 mk2).
  { intros P P_ok. exact (agree_of_pres_ex _ _ _ _ _ _ _ _ pres_k2 P_ok). }
  assert (regs_k2 : rw_cells asegs mk2 (bv_unsigned sp + -96) [CB 24 spill_w1; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs mw1 mk2 _ _ regs_w1); [| exact wm_k2].
    apply ms_keep. intros x x_in. cbn [cells_size csize Nat.add] in x_in. split.
    - apply upper_cl. clear - x_in pad_two. lia.
    - clear - x_in fb_win lo_win room. lia. }
  assert (padgap_k2 : stk asegs mk2 (bv_unsigned sp + -96 - pad) (bv_unsigned sp + -96)).
  { apply (stk_agree asegs mw1 mk2 _ _ padgap_w1); [| exact wm_k2].
    apply ms_keep. intros x x_in. split.
    - apply upper_cl. clear - x_in pad_two. lia.
    - clear - x_in fb_win lo_win room pad_two. lia. }
  assert (shadow_k2 : rw_cells asegs mk2 (fb / 8 + 2147450880) nm_shadow).
  { apply (rw_cells_agree asegs mw1 mk2 _ _ shadow_w1); [| exact wm_k2].
    apply ms_keep. intros x x_in. cbn [nm_shadow cells_size csize Nat.add] in x_in. split.
    - apply fshadow_cl. clear - x_in. lia.
    - clear - x_in fb_hi fb_pos. lia. }
  assert (wr_fb_k2 : wr_at asegs mk2 fb 120) by exact (wr_at_wm mw1 mk2 fb 120 wr_fb_w1 wm_k2).
  assert (wr_ctx_k2 : wr_at asegs mk2 (fb + 32) 8) by exact (wr_sub mk2 fb 120 32 8 wr_fb_k2 ltac:(lia) ltac:(lia) ltac:(lia)).
  pose proof (wr_at_rw_CB mk2 (fb + 32) 8 wr_ctx_k2 ltac:(lia)) as (ctxj & ctx_k2).
  pose proof (wp_zero_rw_CB asegs mk2 (fb + 40) 40 zero_k2 (wr_sub mk2 fb 120 40 40 wr_fb_k2 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia))
    as zcfg_k2.
  assert (cfg_k2 : rw_cells asegs mk2 (fb + 32) [CB 8 ctxj; CB 40 (repeat (Z_to_bv 8 0) 40)]).
  { apply (proj2 (rw_cells_app mk2 (fb + 32) [CB 8 ctxj] [CB 40 (repeat (Z_to_bv 8 0) 40)])). split; [exact ctx_k2|].
    cbn [cells_size csize]. replace (fb + 32 + Z.of_nat 8) with (fb + 40) by lia. exact zcfg_k2. }
  (* config record filled in, up to the namemap allocation *)
  pose proof (nm_w2 sp gp (Z_to_bv 64 TP_A) t0_2 t1_2 t2_2 (Z_to_bv 64 (fb + 40)) a1_2 a2_2 a3_2 a4_2 a5_2 a6_2 a7_2 a0 s4 s8 s9 s10 s11
                t3_2 t4_2 t5_2 t6_2 F_2 fc_2 mk2 fb lo pad ctxj
                fb_pos ltac:(clear - fb_seg; lia) ltac:(clear - fb_win sp0_high; lia) cfg_k2 inv_k2) as step.
  cl_lift step at_c4' c5 at_c5.
  destruct (ASTA_unpack RT R1 Pm _ c5 at_c5)
    as (ms5 & (t0_w2 & t1_w2 & t2_w2 & a3_w2 & a4_w2 & a5_w2 & a6_w2 & a7_w2 & t3_w2 & t4_w2 & t5_w2 & t6_w2 & mw2 & -> & mu_w2 & wm_w2 & inv_w2 & conf_w2) & at_c5').
  clear at_c5.
  assert (art_w2 : ART RT R1 mw2).
  { apply (af_frame RT AF R1 mk2 mw2 lo art_k2 lo_win1); [| exact wm_w2].
    intros a not_cl. apply mu_w2. cbn [outside]. split; [| exact I]. intros inside. apply not_cl, frame_cl. clear - inside. lia. }
  assert (off_cfg : forall x, x < fb \/ fb + 128 <= x -> outside [(fb + 32, fb + 80)] x)
    by (intros x x_far; cbn [outside]; split; [clear - x_far; lia | exact I]).
  assert (stk_w2 : stk asegs mw2 lo (bv_unsigned sp + -96 - pad)).
  { apply (stk_munch _ mk2 mw2 _ _ stk_k2 mu_w2 wm_w2). intros x x_rng. apply off_cfg. clear - x_rng fb_win lo_win. lia. }
  assert (regs_w2 : rw_cells asegs mw2 (bv_unsigned sp + -96) [CB 24 spill_w1; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (wg_keep_seg _ mk2 mw2 _ _ regs_k2 mu_w2 wm_w2). intros x x_in. cbn [cells_size csize Nat.add] in x_in.
    apply off_cfg. clear - x_in fb_win lo_win room. lia. }
  (* the caller's memory: what it owns lies above sp or below lo, and away from the new fake frame *)
  assert (caller_split : forall x, aclient (rt_live RT R0) (rt_frames RT R0) (bv_unsigned sp) x -> bv_unsigned sp <= x \/ x < lo).
  { intros x owned. destruct (aclient_split RT AF R0 m (bv_unsigned sp) x art_m owned) as [above | below]; [left; exact above|].
    right. unfold STACK_WIN in below. clear - below lo_win. lia. }
  assert (caller_off_fb : forall x, aclient (rt_live RT R0) (rt_frames RT R0) (bv_unsigned sp) x ->
                          ~ (fb <= x < fb + 128) /\ ~ (fb / 8 + 2147450880 <= x < fb / 8 + 2147450880 + 16)).
  { intros x owned.
    destruct (newframe_apart RT AF R0 R1 mk1 fb 1 (bv_unsigned sp) x art_k1 frames_R1 live_R1 sp0_R1
                ltac:(unfold STACK_WIN; clear - lo_win room; lia) owned) as (off_f & off_s).
    change (fs_size 1) with 128 in off_f, off_s. unfold shad, SHB in off_s.
    split; [exact off_f | clear - off_s; lia]. }
  assert (caller_in1 : forall x, aclient (rt_live RT R0) (rt_frames RT R0) (bv_unsigned sp) x ->
                       aclient (rt_live RT R1) (rt_frames RT R1) (bv_unsigned sp + -96 - pad) x).
  { intros x owned. apply (aclient_mono _ _ _ _ _ _ _ owned).
    - intros e e_in. rewrite live_R1. exact e_in.
    - intros e e_in. rewrite frames_R1. right. exact e_in.
    - clear - pad_two. lia. }
  assert (caller_w2 : agree_on (aclient (rt_live RT R0) (rt_frames RT R0) (bv_unsigned sp)) m mw2).
  { apply (agree_trans _ m mk2 mw2); [apply (agree_trans _ m mw1 mk2); [apply (agree_trans _ m mk1 mw1); [apply (agree_trans _ m mw0 mk1)|]|]|].
    - apply (agree_of_munch _ m mw0 _ mu_w0). intros x owned. cbn [outside].
      destruct (caller_split x owned) as [side | side]; clear - side room; (split; [lia | exact I]).
    - apply (agree_of_pres _ _ _ mw0 mk1 _ pres_k1). intros x owned.
      apply (aclient_mono _ _ _ _ _ _ _ owned); [intros e e_in; exact e_in | intros e e_in; exact e_in | clear - pad_two; lia].
    - apply (agree_of_munch _ mk1 mw1 _ mu_w1). intros x owned. cbn [outside].
      destruct (caller_off_fb x owned) as (nf & ns). destruct (caller_split x owned) as [side | side];
      clear - side nf ns room; repeat split; lia.
    - apply ms_keep. intros x owned. split; [exact (caller_in1 x owned)|].
      destruct (caller_off_fb x owned) as (nf & _). clear - nf. lia.
    - apply (agree_of_munch _ mk2 mw2 _ mu_w2). intros x owned. cbn [outside].
      destruct (caller_off_fb x owned) as (nf & _). split; [clear - nf; lia | exact I]. }
  assert (env_w2 : cl_env mw2 lb canary).
  { apply (cl_env_agree m mw2 _ _ env_m). intros a cell_a. apply caller_w2. apply acl_static. exact (cl_cell_static _ cell_a). }
  assert (cok_w2 : call_ok RT R1 mw2 (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) lo).
  { unfold call_ok. rewrite fsp_val, sp0_R1. split; [exact stk_w2|].
    unfold RT_STACK, STACK_WIN, USTACK_TOP. clear - lo_win room sp_top pad_is pad_two sp_al16. repeat split; lia. }
  assert (cgh1 : cg_has (rt_cg RT R1) NM_SITES NM_CALLS) by (rewrite cg_R1; exact cghas_m).
  assert (cgx1 : cg_ctx (rt_cg RT R1) e_namemap_new (bv_unsigned ra :: outer)) by (rewrite cg_R1; exact cgctx_m).
  assert (ra_cells_w2 : rw_cells asegs mw2 (bv_unsigned sp - 16) [C8 s0; C8 ra]).
  { pose proof (rw_cells_skip mw2 (bv_unsigned sp + -96) [CB 24 spill_w1; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1]
                  [C8 s0; C8 ra] regs_w2) as top2.
    cbn [cells_size csize Nat.add] in top2. replace (bv_unsigned sp - 16) with (bv_unsigned sp + -96 + Z.of_nat 80) by lia. exact top2. }
  destruct (cl_chain_call (rt_cg RT R1) e_namemap_new e_CRYPTO_zalloc SITE_nm_zalloc m mw2 ra s0 sp
              (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) outer cgx1
              (cg_has_site _ _ _ _ _ cgh1 ltac:(unfold NM_SITES; left; reflexivity))
              (cg_has_call _ _ _ _ _ cgh1 ltac:(unfold NM_CALLS; left; reflexivity))
              chain_m
              (agree_sub _ _ m mw2 caller_w2 ltac:(intros x x_rng; apply acl_stack; exact x_rng))
              ra_cells_w2 ltac:(rewrite fsp_val; clear - pad_two; lia) ltac:(unfold USTACK_TOP; clear - sp_top; lia)) as (cgx_z & chain_z).
  rewrite <- (unsigned_lit SITE_nm_zalloc) in cgx_z by (unfold SITE_nm_zalloc; lia).
  assert (cg_alloc1 : cg_has (rt_cg RT R1) [(SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)]
                        [(SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)])
    by (apply (cg_has_weaken _ _ _ _ _ cgh1); vm_compute; reflexivity).
  (* the namemap record *)
  refine (C_CZ R1 Pm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mw2 40 lo (bv_unsigned ra :: outer) lb canary
            only_fd stable eq_refl eq_refl ltac:(lia) art_w2 inv_w2 cok_w2
            ltac:(rewrite fsp_val; unfold RT_STACK; clear - room pad_two; lia) cgx_z chain_z cg_alloc1
            ltac:(rewrite live_R1; clear - few_live; lia)
            ltac:(rewrite credit_R1; unfold NM_COST, HT_COST in enough_credit; cbv [mcost] in enough_credit |- *; cbn in enough_credit |- *;
                  clear - enough_credit; lia)
            env_w2 T c5 at_c5' _).
  intros c6 after_nm.
  destruct after_nm as (R2 & nm & at_c6 & live_R2 & frames_R2 & sp0_R2 & credit_R2 & nm_pos & nm_al & nm_top & cg_R2).
  destruct (ASTA_unpack RT R2 Pm _ c6 at_c6) as (ms6 & (mk3 & ret_k3 & aft_k3 & pres_k3 & env_k3 & wr_nm & acc_nm & zero_nm) & at_c6').
  clear at_c6.
  destruct ret_k3 as (t0_3 & t1_3 & t2_3 & a1_3 & a2_3 & a3_3 & a4_3 & a5_3 & a6_3 & a7_3 & t3_3 & t4_3 & t5_3 & t6_3 & F_3 & fc_3 & ->).
  destruct aft_k3 as (art_k3 & inv_k3 & wm_k3 & stk_k3).
  rewrite (ret_pc_even SITE_nm_zalloc) in at_c6' by (unfold SITE_nm_zalloc; lia).
  rewrite fsp_val in stk_k3, pres_k3.
  (* namemap pointer kept in a callee-saved register, up to the lock allocation *)
  pose proof (nm_w3 sp gp (Z_to_bv 64 TP_A) t0_3 t1_3 t2_3 a1_3 a2_3 a3_3 a4_3 a5_3 a6_3 a7_3 a0 s4 s8 s9 s10 s11 t3_3 t4_3 t5_3 t6_3
                F_3 fc_3 mk3 fb nm pad nm_pos ltac:(unfold USTACK_TOP in nm_top; clear - nm_top; lia) inv_k3) as step.
  cl_lift step at_c6' c7 at_c7.
  destruct (ASTA_unpack RT R2 Pm _ c7 at_c7) as (ms7 & -> & at_c7'). clear at_c7.
  assert (nm_in2 : In (nm, 40) (rt_live RT R2)) by (rewrite live_R2; left; reflexivity).
  pose proof (afp_live_hi RT GOBJ AFP R2 mk3 nm 40 art_k3 nm_in2 ltac:(lia)) as nm_hi.
  pose proof (af_live_range RT AF R2 mk3 nm 40 art_k3 nm_in2) as (_ & nm_win & _).
  unfold STACK_WIN in nm_win. rewrite sp0_R2, sp0_R1 in nm_win.
  assert (fb_in2 : In (fb, 1%nat) (rt_frames RT R2)) by (rewrite frames_R2; exact fb_in1).
  assert (lo_win2 : rt_sp0 RT R2 - 8388608 <= lo) by (rewrite sp0_R2, sp0_R1; exact lo_win).
  (* what zalloc may touch, seen from this frame *)
  assert (z_keep : forall P : Z -> Prop,
            (forall x, P x -> aclient (rt_live RT R1) (rt_frames RT R1) (bv_unsigned sp + -96 - pad) x /\ outside [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] x) ->
            agree_on P mw2 mk3).
  { intros P P_ok. exact (agree_of_pres_fp _ _ _ _ _ _ _ pres_k3 P_ok). }
  assert (own_stack1 : forall x, bv_unsigned sp + -96 - pad <= x < bv_unsigned sp ->
                       aclient (rt_live RT R1) (rt_frames RT R1) (bv_unsigned sp + -96 - pad) x /\ outside [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] x).
  { intros x x_rng. split; [apply upper_cl; exact x_rng|]. cbn [outside]. unfold G_ALLOW_CUST.
    split; [clear - x_rng lo_floor room pad_two; lia | exact I]. }
  assert (own_frame1 : forall x, fb <= x < fb + 120 ->
                       aclient (rt_live RT R1) (rt_frames RT R1) (bv_unsigned sp + -96 - pad) x /\ outside [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] x).
  { intros x x_rng. split; [apply frame_cl; exact x_rng|]. cbn [outside]. unfold G_ALLOW_CUST.
    split; [clear - x_rng fb_seg; lia | exact I]. }
  assert (regs_k3 : rw_cells asegs mk3 (bv_unsigned sp + -96) [CB 24 spill_w1; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs mw2 mk3 _ _ regs_w2); [| exact wm_k3].
    apply z_keep. intros x x_in. cbn [cells_size csize Nat.add] in x_in. apply own_stack1. clear - x_in pad_two. lia. }
  assert (caller_k3 : agree_on (fun x => aclient (rt_live RT R0) (rt_frames RT R0) (bv_unsigned sp) x
                                       /\ outside [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] x) m mk3).
  { apply (agree_trans _ m mw2 mk3).
    - apply (agree_sub _ _ m mw2 caller_w2). intros x (owned & _). exact owned.
    - apply z_keep. intros x (owned & off_g). exact (conj (caller_in1 x owned) off_g). }
  assert (top_k3 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m mk3).
  { apply (agree_sub _ _ m mk3 caller_k3). intros x x_rng. split; [apply acl_stack; exact x_rng|].
    cbn [outside]. unfold G_ALLOW_CUST. split; [clear - x_rng lo_floor room; lia | exact I]. }
  assert (ra_cells_k3 : rw_cells asegs mk3 (bv_unsigned sp - 16) [C8 s0; C8 ra]).
  { pose proof (rw_cells_skip mk3 (bv_unsigned sp + -96) [CB 24 spill_w1; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1]
                  [C8 s0; C8 ra] regs_k3) as top3.
    cbn [cells_size csize Nat.add] in top3. replace (bv_unsigned sp - 16) with (bv_unsigned sp + -96 + Z.of_nat 80) by lia. exact top3. }
  assert (cgh2 : cg_has (rt_cg RT R2) NM_SITES NM_CALLS) by (rewrite cg_R2; exact cgh1).
  assert (cgx2 : cg_ctx (rt_cg RT R2) e_namemap_new (bv_unsigned ra :: outer)) by (rewrite cg_R2; exact cgx1).
  destruct (cl_chain_call (rt_cg RT R2) e_namemap_new e_lock_new SITE_nm_locknew m mk3 ra s0 sp
              (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) outer cgx2
              (cg_has_site _ _ _ _ _ cgh2 ltac:(unfold NM_SITES; right; left; reflexivity))
              (cg_has_call _ _ _ _ _ cgh2 ltac:(unfold NM_CALLS; right; left; reflexivity))
              chain_m top_k3 ra_cells_k3 ltac:(rewrite fsp_val; clear - pad_two; lia) ltac:(unfold USTACK_TOP; clear - sp_top; lia))
    as (cgx_l & chain_l).
  rewrite <- (unsigned_lit SITE_nm_locknew) in cgx_l by (unfold SITE_nm_locknew; lia).
  assert (cg_lock2 : cg_has (rt_cg RT R2) [(SITE_ln_zalloc, e_lock_new); (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)]
                       [(SITE_ln_zalloc, e_CRYPTO_zalloc); (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)])
    by (apply (cg_has_weaken _ _ _ _ _ cgh2); vm_compute; reflexivity).
  assert (stk_k3' : stk asegs mk3 lo (bv_unsigned sp + -96 - pad)) by exact stk_k3.
  assert (cok_k3 : call_ok RT R2 mk3 (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) lo).
  { unfold call_ok. rewrite fsp_val, sp0_R2, sp0_R1. split; [exact stk_k3'|].
    unfold RT_STACK, STACK_WIN, USTACK_TOP. clear - lo_win room sp_top pad_is pad_two sp_al16. repeat split; lia. }
  (* the namemap lock *)
  refine (C_LN R2 Pm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mk3 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary
            only_fd stable eq_refl art_k3 inv_k3 cok_k3
            ltac:(rewrite fsp_val; unfold RT_STACK; clear - room pad_two; lia) cgx_l chain_l cg_lock2
            ltac:(rewrite frames_R2, frames_R1; cbn [length]; clear - few_frames; lia)
            ltac:(rewrite live_R2, live_R1; cbn [length]; clear - few_live; lia)
            ltac:(rewrite credit_R2, credit_R1; unfold NM_COST, HT_COST in enough_credit; cbv [mcost] in enough_credit |- *;
                  cbn in enough_credit |- *; clear - enough_credit; lia)
            env_k3 T c7 at_c7' _).
  intros c8 after_lk.
  destruct after_lk as (R3 & lk & at_c8 & live_R3 & frames_R3 & sp0_R3 & credit_R3 & lk_pos & lk_al & lk_top & cg_R3).
  destruct (ASTA_unpack RT R3 Pm _ c8 at_c8) as (ms8 & (mk4 & ret_k4 & aft_k4 & pres_k4 & env_k4 & mutex_k4 & acc_lk) & at_c8').
  clear at_c8.
  destruct ret_k4 as (t0_4 & t1_4 & t2_4 & a1_4 & a2_4 & a3_4 & a4_4 & a5_4 & a6_4 & a7_4 & t3_4 & t4_4 & t5_4 & t6_4 & F_4 & fc_4 & ->).
  destruct aft_k4 as (art_k4 & inv_k4 & wm_k4 & stk_k4).
  rewrite (ret_pc_even SITE_nm_locknew) in at_c8' by (unfold SITE_nm_locknew; lia).
  rewrite fsp_val in stk_k4, pres_k4.
  assert (nm_in3 : In (nm, 40) (rt_live RT R3)) by (rewrite live_R3; right; exact nm_in2).
  pose proof (wp_zero_rw_CB asegs mk3 nm 40 zero_nm wr_nm ltac:(lia)) as nmz_k3.
  assert (nmz_k4 : rw_cells asegs mk4 nm [CB 40 (repeat (Z_to_bv 8 0) 40)]).
  { apply (wg_keep_live _ _ _ _ mk3 mk4 nm 40 nm _ nmz_k3 pres_k4 wm_k4 nm_in2); [lia | cbn [cells_size csize]; lia |].
    intros x x_in. cbn [cells_size csize] in x_in. cbn [outside]. unfold G_ALLOW_CUST.
    split; [clear - x_in nm_hi; lia | exact I]. }
  assert (nm_cells_k4 : rw_cells asegs mk4 nm [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_recast mk4 nm _ _ nmz_k4); vm_compute; [| reflexivity]. repeat constructor. }
  pose proof (af_acc_live RT AF R3 mk4 nm 40 art_k4 nm_in3) as (_ & acc_nm4).
  (* lock pointer stored, up to the hash-table construction *)
  pose proof (nm_w4 sp gp (Z_to_bv 64 TP_A) t0_4 t1_4 t2_4 a1_4 a2_4 a3_4 a4_4 a5_4 a6_4 a7_4 s4 s8 s9 s10 s11 t3_4 t4_4 t5_4 t6_4
                F_4 fc_4 mk4 fb nm lk pad fb_pos ltac:(clear - fb_win sp0_high; lia) nm_hi
                ltac:(clear - nm_win sp0_high; lia) ltac:(clear - nm_al; lia) lk_pos ltac:(unfold USTACK_TOP in lk_top; clear - lk_top; lia)
                nm_cells_k4 acc_nm4 inv_k4) as step.
  cl_lift step at_c8' c9 at_c9.
  destruct (ASTA_unpack RT R3 Pm _ c9 at_c9) as (ms9 & (mw4 & -> & mu_w4 & wm_w4 & inv_w4 & nm_cells_w4) & at_c9').
  clear at_c9.
  assert (nm_in_l3 : In (nm, 40) (rt_live RT R3)) by exact nm_in3.
  assert (lk_in3 : In (lk, 40) (rt_live RT R3)) by (rewrite live_R3; left; reflexivity).
  assert (fb_in3 : In (fb, 1%nat) (rt_frames RT R3)) by (rewrite frames_R3; exact fb_in2).
  assert (lo_win3 : rt_sp0 RT R3 - 8388608 <= lo) by (rewrite sp0_R3; exact lo_win2).
  pose proof (af_frames_range RT AF R3 mk4 fb 1 art_k4 fb_in3) as (_ & _ & _ & fb_sep3).
  change (fs_size 1) with 128 in fb_sep3.
  pose proof (fb_sep3 nm 40 nm_in_l3) as fb_nm.
  assert (nm_store : forall x, x < nm \/ nm + 40 <= x -> outside [(nm + 16, nm + 24)] x)
    by (intros x x_far; cbn [outside]; split; [clear - x_far; lia | exact I]).
  assert (art_w4 : ART RT R3 mw4).
  { apply (af_frame RT AF R3 mk4 mw4 lo art_k4 lo_win3); [| exact wm_w4].
    intros a not_cl. apply mu_w4. cbn [outside]. split; [| exact I]. intros inside. apply not_cl.
    apply (acl_live _ _ _ nm 40); [exact nm_in_l3 | clear - inside; lia]. }
  assert (stk_w4 : stk asegs mw4 lo (bv_unsigned sp + -96 - pad)).
  { apply (stk_munch _ mk4 mw4 _ _ stk_k4 mu_w4 wm_w4). intros x x_rng. apply nm_store. clear - x_rng nm_win lo_win. lia. }
  assert (cok_w4 : call_ok RT R3 mw4 (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) lo).
  { unfold call_ok. rewrite fsp_val, sp0_R3, sp0_R2, sp0_R1. split; [exact stk_w4|].
    unfold RT_STACK, STACK_WIN, USTACK_TOP. clear - lo_win room sp_top pad_is pad_two sp_al16. repeat split; lia. }
  (* what the lock allocation may touch, seen from this frame *)
  assert (l_keep : forall P : Z -> Prop,
            (forall x, P x -> aclient (rt_live RT R2) (rt_frames RT R2) (bv_unsigned sp + -96 - pad) x /\ outside [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] x) ->
            agree_on P mk3 mk4).
  { intros P P_ok. exact (agree_of_pres_fp _ _ _ _ _ _ _ pres_k4 P_ok). }
  assert (own_stack2 : forall x, bv_unsigned sp + -96 - pad <= x < bv_unsigned sp ->
                       aclient (rt_live RT R2) (rt_frames RT R2) (bv_unsigned sp + -96 - pad) x /\ outside [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] x).
  { intros x x_rng. split; [apply upper_cl; exact x_rng|]. cbn [outside]. unfold G_ALLOW_CUST.
    split; [clear - x_rng lo_floor room pad_two; lia | exact I]. }
  assert (own_frame2 : forall x, (fb <= x < fb + 120 \/ fb / 8 + 2147450880 <= x < fb / 8 + 2147450880 + 16) ->
                       aclient (rt_live RT R2) (rt_frames RT R2) (bv_unsigned sp + -96 - pad) x /\ outside [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] x).
  { intros x [in_f | in_s]; split; cbn [outside]; unfold G_ALLOW_CUST.
    - rewrite frames_R2. apply frame_cl. exact in_f.
    - split; [clear - in_f fb_seg; lia | exact I].
    - rewrite frames_R2. apply fshadow_cl. exact in_s.
    - split; [clear - in_s fb_pos; lia | exact I]. }
  assert (regs_w4 : rw_cells asegs mw4 (bv_unsigned sp + -96) [CB 24 spill_w1; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (wg_keep_seg [(nm + 16, nm + 24)] mk4 mw4); [| exact mu_w4 | exact wm_w4 |].
    - apply (rw_cells_agree asegs mk3 mk4 _ _ regs_k3); [| exact wm_k4].
      apply l_keep. intros x x_in. cbn [cells_size csize Nat.add] in x_in. apply own_stack2. clear - x_in pad_two. lia.
    - intros x x_in. cbn [cells_size csize Nat.add] in x_in. apply nm_store. clear - x_in nm_win lo_win room. lia. }
  (* the hash-table configuration in the fake frame, and its shadow *)
  assert (shadow_w2 : rw_cells asegs mw2 (fb / 8 + 2147450880) nm_shadow).
  { apply (wg_keep_seg _ mk2 mw2 _ _ shadow_k2 mu_w2 wm_w2). intros x x_in. cbn [nm_shadow cells_size csize Nat.add] in x_in.
    apply off_cfg. clear - x_in fb_hi fb_pos. lia. }
  assert (shadow_w4 : rw_cells asegs mw4 (fb / 8 + 2147450880) nm_shadow).
  { apply (wg_keep_seg [(nm + 16, nm + 24)] mk4 mw4); [| exact mu_w4 | exact wm_w4 |].
    - apply (rw_cells_agree asegs mk3 mk4); [| | exact wm_k4].
      + apply (rw_cells_agree asegs mw2 mk3 _ _ shadow_w2); [| exact wm_k3].
        apply z_keep. intros x x_in. cbn [nm_shadow cells_size csize Nat.add] in x_in. split.
        * apply fshadow_cl. clear - x_in. lia.
        * cbn [outside]. unfold G_ALLOW_CUST. split; [clear - x_in fb_pos; lia | exact I].
      + apply l_keep. intros x x_in. cbn [nm_shadow cells_size csize Nat.add] in x_in. apply own_frame2. right. clear - x_in. lia.
    - intros x x_in. cbn [nm_shadow cells_size csize Nat.add] in x_in. apply nm_store.
      pose proof (proj1 (af_fshadow_apart RT AF R3 mk4 fb 1 art_k4 fb_in3) nm 40 nm_in_l3) as sh_nm.
      change (fs_size 1) with 128 in sh_nm. unfold shad, SHB in sh_nm. clear - x_in sh_nm fb_al. lia. }
  assert (conf_w4 : rw_cells asegs mw4 (fb + 32) (nm_conf0 a0)).
  { apply (wg_keep_seg [(nm + 16, nm + 24)] mk4 mw4); [| exact mu_w4 | exact wm_w4 |].
    - apply (rw_cells_agree asegs mk3 mk4); [| | exact wm_k4].
      + apply (rw_cells_agree asegs mw2 mk3 _ _ conf_w2); [| exact wm_k3].
        apply z_keep. intros x x_in. cbn [nm_conf0 cells_size csize Nat.add] in x_in. apply own_frame1. clear - x_in. lia.
      + apply l_keep. intros x x_in. cbn [nm_conf0 cells_size csize Nat.add] in x_in. apply own_frame2. left. clear - x_in. lia.
    - intros x x_in. cbn [nm_conf0 cells_size csize Nat.add] in x_in. apply nm_store. clear - x_in fb_nm. lia. }
  assert (conf_ht_w4 : rw_cells asegs mw4 (fb + 32) (ht_conf a0)).
  { apply (rw_cells_recast mw4 (fb + 32) (nm_conf0 a0) (ht_conf a0) conf_w4); [cbn; repeat split |].
    cbn [cells_bytes ht_conf nm_conf0 app]. f_equal. vm_compute. repeat (f_equal; try (apply bv_eq; reflexivity)). }
  assert (acc_conf_w4 : acc asegs mw4 (fb + 32) 48).
  { apply acc_ushadow; [clear - fb_al; lia | clear - fb_pos; lia | lia |].
    replace (shad (fb + 32)) with (fb / 8 + 2147450880 + Z.of_nat (cells_size (firstn 4 nm_shadow)))
      by (unfold shad, SHB; cbn [firstn nm_shadow cells_size csize Nat.add]; clear - fb_al; lia).
    pose proof (rw_cells_skip mw4 _ (firstn 4 nm_shadow) (skipn 4 nm_shadow) shadow_w4) as tail_sh.
    exact (rw_cells_bytes_at _ _ _ _ (proj1 (proj1 (rw_cells_app mw4 _ (firstn 6 (skipn 4 nm_shadow)) (skipn 6 (skipn 4 nm_shadow))) tail_sh))). }
  (* the caller's memory up to the call, the call-graph context, and the environment *)
  assert (caller_w4 : agree_on (fun x => aclient (rt_live RT R0) (rt_frames RT R0) (bv_unsigned sp) x
                                       /\ outside [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] x) m mw4).
  { apply (agree_trans _ m mk4 mw4); [apply (agree_trans _ m mk3 mk4)|].
    - exact caller_k3.
    - apply l_keep. intros x (owned & off_g). split; [| exact off_g].
      apply (aclient_mono _ _ _ _ _ _ _ (caller_in1 x owned)).
      + intros e e_in. rewrite live_R2. right. exact e_in.
      + intros e e_in. rewrite frames_R2. exact e_in.
      + lia.
    - apply (agree_of_munch _ mk4 mw4 _ mu_w4). intros x (owned & _). apply nm_store.
      destruct (caller_split x owned) as [side | side]; [clear - side nm_win room lo_win; lia|].
      destruct (Z_lt_le_dec x nm) as [lt_nm | nm_le]; [left; exact lt_nm|]. right.
      pose proof (newchunk_apart RT AF R1 R2 mk3 nm 40 (bv_unsigned sp + -96 - pad) x art_k3 live_R2 frames_R2 sp0_R2
                    ltac:(rewrite sp0_R1; unfold STACK_WIN; clear - lo_win room pad_two; lia) ltac:(lia) (caller_in1 x owned)) as off_nm.
      clear - off_nm nm_le. lia. }
  assert (top_w4 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m mw4).
  { apply (agree_sub _ _ m mw4 caller_w4). intros x x_rng. split; [apply acl_stack; exact x_rng|].
    cbn [outside]. unfold G_ALLOW_CUST. split; [clear - x_rng lo_floor room; lia | exact I]. }
  assert (ra_cells_w4 : rw_cells asegs mw4 (bv_unsigned sp - 16) [C8 s0; C8 ra]).
  { pose proof (rw_cells_skip mw4 (bv_unsigned sp + -96) [CB 24 spill_w1; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1]
                  [C8 s0; C8 ra] regs_w4) as top4.
    cbn [cells_size csize Nat.add] in top4. replace (bv_unsigned sp - 16) with (bv_unsigned sp + -96 + Z.of_nat 80) by lia. exact top4. }
  assert (cgh3 : cg_has (rt_cg RT R3) NM_SITES NM_CALLS) by (rewrite cg_R3; exact cgh2).
  assert (cgx3 : cg_ctx (rt_cg RT R3) e_namemap_new (bv_unsigned ra :: outer)) by (rewrite cg_R3; exact cgx2).
  destruct (cl_chain_call (rt_cg RT R3) e_namemap_new e_ht_new SITE_nm_htnew m mw4 ra s0 sp
              (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) outer cgx3
              (cg_has_site _ _ _ _ _ cgh3 ltac:(unfold NM_SITES; right; right; left; reflexivity))
              (cg_has_call _ _ _ _ _ cgh3 ltac:(unfold NM_CALLS; right; right; left; reflexivity))
              chain_m top_w4 ra_cells_w4 ltac:(rewrite fsp_val; clear - pad_two; lia) ltac:(unfold USTACK_TOP; clear - sp_top; lia))
    as (cgx_h & chain_h).
  rewrite <- (unsigned_lit SITE_nm_htnew) in cgx_h by (unfold SITE_nm_htnew; lia).
  assert (cg_ht3 : cg_has (rt_cg RT R3) HT_SITES HT_CALLS)
    by (apply (cg_has_weaken _ _ _ _ _ cgh3); vm_compute; reflexivity).
  assert (env_w4 : cl_env mw4 (Z_to_bv 8 1) canary).
  { apply (cl_env_agree mk4 mw4 _ _ env_k4). intros a cell_a. apply mu_w4.
    pose proof (client_static_range _ (cl_cell_static _ cell_a)) as a_rng. unfold SEGTOP_A in a_rng.
    apply nm_store. clear - a_rng nm_hi. lia. }
  assert (frames_n3 : (length (rt_frames RT R3) < FRAMES_MAX)%nat)
    by (rewrite frames_R3, frames_R2, frames_R1; cbn [length]; clear - few_frames; lia).
  assert (live_n3 : Z.of_nat (length (rt_live RT R3)) + 6 < LIVE_MAX)
    by (rewrite live_R3, live_R2, live_R1; cbn [length]; clear - few_live; lia).
  assert (credit3 : rt_credit RT R3 = rt_credit RT R0 - 2)
    by (rewrite credit_R3, credit_R2, credit_R1; change (mcost 40) with 0; lia).
  assert (ht_credit3 : HT_COST <= rt_credit RT R3)
    by (rewrite credit3; unfold NM_COST in enough_credit; change (mcost 40) with 0 in enough_credit;
        change (mcost 56) with 0 in enough_credit; clear - enough_credit; lia).
  assert (padgap_w4 : stk asegs mw4 (bv_unsigned sp + -96 - pad) (bv_unsigned sp + -96)).
  { apply (stk_munch [(nm + 16, nm + 24)] mk4 mw4); [| exact mu_w4 | exact wm_w4 |].
    - apply (stk_agree asegs mk3 mk4); [| | exact wm_k4].
      + apply (stk_agree asegs mw2 mk3); [| | exact wm_k3].
        * apply (stk_munch _ mk2 mw2 _ _ padgap_k2 mu_w2 wm_w2). intros x x_rng. apply off_cfg. clear - x_rng fb_win lo_win room pad_two. lia.
        * apply z_keep. intros x x_rng. apply own_stack1. clear - x_rng pad_two. lia.
      + apply l_keep. intros x x_rng. apply own_stack2. clear - x_rng pad_two. lia.
    - intros x x_rng. apply nm_store. clear - x_rng nm_win lo_win room pad_two. lia. }
  assert (caller_off_nm : forall x, aclient (rt_live RT R0) (rt_frames RT R0) (bv_unsigned sp) x -> ~ (nm <= x < nm + 40)).
  { intros x owned. destruct (caller_split x owned) as [side | side]; [clear - side nm_win room lo_win; lia|].
    exact (newchunk_apart RT AF R1 R2 mk3 nm 40 (bv_unsigned sp + -96 - pad) x art_k3 live_R2 frames_R2 sp0_R2
             ltac:(rewrite sp0_R1; unfold STACK_WIN; clear - lo_win room pad_two; lia) ltac:(lia) (caller_in1 x owned)). }
  assert (caller_in3 : forall x, aclient (rt_live RT R0) (rt_frames RT R0) (bv_unsigned sp) x ->
                       aclient (rt_live RT R3) (rt_frames RT R3) (bv_unsigned sp + -96 - pad) x).
  { intros x owned. apply (aclient_mono _ _ _ _ _ _ _ (caller_in1 x owned)).
    - intros e e_in. rewrite live_R3, live_R2. right; right. exact e_in.
    - intros e e_in. rewrite frames_R3, frames_R2. exact e_in.
    - lia. }
  assert (lk_win : lk + 40 <= lo).
  { pose proof (af_live_range RT AF R3 mk4 lk 40 art_k4 lk_in3) as (_ & lk_w & _).
    unfold STACK_WIN in lk_w. rewrite sp0_R3, sp0_R2, sp0_R1 in lk_w. clear - lk_w lo_win. lia. }
  pose proof (afp_live_hi RT GOBJ AFP R3 mk4 lk 40 art_k4 lk_in3 ltac:(lia)) as lk_hi.
  pose proof (wg_live_apart RT AF R3 mk4 [] lk 40 (rt_live RT R2) nm 40 art_k4 live_R3 nm_in2) as lk_nm.
  pose proof (fb_sep3 lk 40 lk_in3) as fb_lk.
  assert (lk_mutex_w4 : rw_cells asegs mw4 lk (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { apply (wg_keep_seg [(nm + 16, nm + 24)] mk4 mw4 _ _ mutex_k4 mu_w4 wm_w4).
    intros x x_in. cbn [mutex_cells cells_size csize Nat.add] in x_in. apply nm_store. clear - x_in lk_nm. lia. }
  (* the name-to-number hash table *)
  refine (C_HT R3 Pm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mw4 lo (bv_unsigned ra :: outer) (fb + 32) fb 1%nat a0
            (Z_to_bv 8 1) canary only_fd stable eq_refl eq_refl fb_in3 ltac:(clear - fb_pos; lia)
            ltac:(change (fs_size 1) with 128; clear - fb_pos; lia) ltac:(clear - fb_al; lia)
            conf_ht_w4 acc_conf_w4 ctx_set art_w4 inv_w4 cok_w4
            ltac:(rewrite fsp_val; unfold RT_STACK; clear - room pad_two; lia) cgx_h chain_h cg_ht3 frames_n3
            ltac:(clear - live_n3; lia) ht_credit3 env_w4 T c9 at_c9' _).
  intros ch after_tab.
  destruct after_tab as (R4 & ht & hlk & md & nb & rl & rq & at_tab & live_R4 & frames_R4 & sp0_R4 & credit_R4
                         & ht_pos & ht_al & ht_top & hlk_pos & hlk_al & hlk_top & md_pos & md_al & md_top
                         & nb_pos & nb_al & nb_top & rl_pos & rl_al & rl_top & rq_pos & rq_al & rq_top & cg_R4).
  destruct (ASTA_unpack RT R4 Pm _ ch at_tab)
    as (msh & (mh & ret_h & aft_h & pres_h & env_h & tab_h & acc_tab_h & hlk_h & acc_hlk_h & md_h & acc_md_h & nb_h & acc_nb_h
               & rl_h & rl48_h & rl88_h & rl128_h & rl176_h & rl216_h & acc_rl_h & rq_h & acc_rq_h) & at_ch).
  clear at_tab.
  destruct ret_h as (t0h & t1h & t2h & a1h & a2h & a3h & a4h & a5h & a6h & a7h & t3h & t4h & t5h & t6h & Fh & fch & ->).
  destruct aft_h as (art_h & inv_h & wm_h & stk_h).
  rewrite (ret_pc_even SITE_nm_htnew) in at_ch by (unfold SITE_nm_htnew; lia).
  rewrite fsp_val in stk_h, pres_h.
  assert (ht_rng : 0 < ht < 2 ^ 64) by (unfold USTACK_TOP in ht_top; clear - ht_pos ht_top; lia).
  (* the table chunks' addresses are only needed for the final statement: keep them out of arithmetic's sight until then *)
  assert (ht_addr : 0 < ht /\ ht mod 16 = 0 /\ ht + 96 < USTACK_TOP /\ 0 < hlk /\ hlk mod 16 = 0 /\ hlk + 40 < USTACK_TOP /\
                    0 < md /\ md mod 16 = 0 /\ md + 24 < USTACK_TOP /\ 0 < nb /\ nb mod 64 = 0 /\ nb + NB_BYTES < USTACK_TOP /\
                    0 < rl /\ rl mod 16 = 0 /\ rl + 264 < USTACK_TOP /\ 0 < rq /\ rq mod 16 = 0 /\ rq + 16 < USTACK_TOP)
    by (repeat split; assumption).
  clear ht_pos ht_al ht_top hlk_pos hlk_al hlk_top md_pos md_al md_top nb_pos nb_al nb_top rl_pos rl_al rl_top rq_pos rq_al rq_top.
  revert ht_addr.
  remember (0 < ht /\ ht mod 16 = 0 /\ ht + 96 < USTACK_TOP /\ 0 < hlk /\ hlk mod 16 = 0 /\ hlk + 40 < USTACK_TOP /\
            0 < md /\ md mod 16 = 0 /\ md + 24 < USTACK_TOP /\ 0 < nb /\ nb mod 64 = 0 /\ nb + NB_BYTES < USTACK_TOP /\
            0 < rl /\ rl mod 16 = 0 /\ rl + 264 < USTACK_TOP /\ 0 < rq /\ rq mod 16 = 0 /\ rq + 16 < USTACK_TOP) as ht_addr_P eqn:ht_addr_eq.
  intros ht_addr.
  assert (in4 : forall e, In e (rt_live RT R3) -> In e (rt_live RT R4))
    by (intros e e_in; rewrite live_R4; do 6 right; exact e_in).
  pose proof (in4 _ nm_in_l3) as nm_in4. pose proof (in4 _ lk_in3) as lk_in4.
  assert (fb_in4 : In (fb, 1%nat) (rt_frames RT R4)) by (rewrite frames_R4; exact fb_in3).
  assert (lo_win4 : rt_sp0 RT R4 - 8388608 <= lo) by (rewrite sp0_R4; exact lo_win3).
  assert (h_keep : forall P : Z -> Prop,
            (forall x, P x -> aclient (rt_live RT R3) (rt_frames RT R3) (bv_unsigned sp + -96 - pad) x /\ outside [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] x) ->
            agree_on P mw4 mh).
  { intros P P_ok. exact (agree_of_pres_fp _ _ _ _ _ _ _ pres_h P_ok). }
  assert (win_h : agree_on (fun x => bv_unsigned sp + -96 - pad <= x < bv_unsigned sp) mw4 mh).
  { apply h_keep. intros x x_rng. split; [apply upper_cl; exact x_rng|]. cbn [outside]. unfold G_ALLOW_CUST.
    split; [clear - x_rng lo_floor room pad_two; lia | exact I]. }
  assert (nm_cells_h : rw_cells asegs mh nm [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 lk); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
  { apply (wg_keep_live _ _ _ _ mw4 mh nm 40 nm _ nm_cells_w4 pres_h wm_h nm_in_l3); [lia | cbn [cells_size csize Nat.add]; lia |].
    intros x x_in. cbn [cells_size csize Nat.add] in x_in. cbn [outside]. unfold G_ALLOW_CUST.
    split; [clear - x_in nm_hi; lia | exact I]. }
  pose proof (af_acc_live RT AF R4 mh nm 40 art_h nm_in4) as (_ & acc_nm_h).
  (* table pointer stored, up to the name-number stack *)
  pose proof (nm_w5 sp gp (Z_to_bv 64 TP_A) t0h t1h t2h a1h a2h a3h a4h a5h a6h a7h s4 s8 s9 s10 s11 t3h t4h t5h t6h Fh fch mh fb nm lk ht pad
                fb_pos ltac:(clear - fb_win sp0_high; lia) nm_hi ltac:(clear - nm_win sp0_high; lia) ltac:(clear - nm_al; lia)
                (proj1 ht_rng) (proj2 ht_rng) nm_cells_h acc_nm_h inv_h) as step.
  cl_lift step at_ch c10 at_c10.
  destruct (ASTA_unpack RT R4 Pm _ c10 at_c10) as (ms10 & (mw5 & -> & mu_w5 & wm_w5 & inv_w5 & nm_cells_w5) & at_c10').
  clear at_c10.
  assert (nm_slot8 : forall x, x < nm \/ nm + 40 <= x -> outside [(nm + 8, nm + 16)] x)
    by (intros x x_far; cbn [outside]; split; [clear - x_far; lia | exact I]).
  assert (art_w5 : ART RT R4 mw5).
  { apply (af_frame RT AF R4 mh mw5 lo art_h lo_win4); [| exact wm_w5].
    intros a not_cl. apply mu_w5. cbn [outside]. split; [| exact I]. intros inside. apply not_cl.
    apply (acl_live _ _ _ nm 40); [exact nm_in4 | clear - inside; lia]. }
  assert (stk_w5 : stk asegs mw5 lo (bv_unsigned sp + -96 - pad)).
  { apply (stk_munch _ mh mw5 _ _ stk_h mu_w5 wm_w5). intros x x_rng. apply nm_slot8. clear - x_rng nm_win lo_win. lia. }
  assert (win_w5 : agree_on (fun x => bv_unsigned sp + -96 - pad <= x < bv_unsigned sp) mw4 mw5).
  { apply (agree_trans _ mw4 mh mw5 win_h). apply (agree_of_munch _ mh mw5 _ mu_w5). intros x x_rng. apply nm_slot8.
    clear - x_rng nm_win lo_win room pad_two. lia. }
  assert (wm_4_5 : wmono asegs mw4 mw5) by exact (wmono_trans asegs mw4 mh mw5 wm_h wm_w5).
  assert (regs_w5 : rw_cells asegs mw5 (bv_unsigned sp + -96) [CB 24 spill_w1; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs mw4 mw5 _ _ regs_w4); [| exact wm_4_5].
    apply (agree_sub _ _ mw4 mw5 win_w5). intros x x_in. cbn [cells_size csize Nat.add] in x_in. clear - x_in pad_two. lia. }
  assert (caller_w5 : agree_on (fun x => aclient (rt_live RT R0) (rt_frames RT R0) (bv_unsigned sp) x
                                       /\ outside [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] x) m mw5).
  { apply (agree_trans _ m mh mw5); [apply (agree_trans _ m mw4 mh caller_w4)|].
    - apply h_keep. intros x (owned & off_g). exact (conj (caller_in3 x owned) off_g).
    - apply (agree_of_munch _ mh mw5 _ mu_w5). intros x (owned & _). apply nm_slot8.
      pose proof (caller_off_nm x owned) as off_nm. clear - off_nm. lia. }
  assert (env_w5 : cl_env mw5 (Z_to_bv 8 1) canary).
  { apply (cl_env_agree mh mw5 _ _ env_h). intros a cell_a. apply mu_w5.
    pose proof (client_static_range _ (cl_cell_static _ cell_a)) as a_rng. unfold SEGTOP_A in a_rng.
    apply nm_slot8. clear - a_rng nm_hi. lia. }
  assert (cok_w5 : call_ok RT R4 mw5 (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) lo).
  { unfold call_ok. rewrite fsp_val, sp0_R4, sp0_R3, sp0_R2, sp0_R1. split; [exact stk_w5|].
    unfold RT_STACK, STACK_WIN, USTACK_TOP. clear - lo_win room sp_top pad_is pad_two sp_al16. repeat split; lia. }
  assert (ra_cells_w5 : rw_cells asegs mw5 (bv_unsigned sp - 16) [C8 s0; C8 ra]).
  { pose proof (rw_cells_skip mw5 (bv_unsigned sp + -96) [CB 24 spill_w1; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1]
                  [C8 s0; C8 ra] regs_w5) as top5.
    cbn [cells_size csize Nat.add] in top5. replace (bv_unsigned sp - 16) with (bv_unsigned sp + -96 + Z.of_nat 80) by lia. exact top5. }
  assert (top_w5 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m mw5).
  { apply (agree_sub _ _ m mw5 caller_w5). intros x x_rng. split; [apply acl_stack; exact x_rng|].
    cbn [outside]. unfold G_ALLOW_CUST. split; [clear - x_rng lo_floor room; lia | exact I]. }
  assert (cgh4 : cg_has (rt_cg RT R4) NM_SITES NM_CALLS) by (rewrite cg_R4; exact cgh3).
  assert (cgx4 : cg_ctx (rt_cg RT R4) e_namemap_new (bv_unsigned ra :: outer)) by (rewrite cg_R4; exact cgx3).
  destruct (cl_chain_call (rt_cg RT R4) e_namemap_new e_OPENSSL_sk_new_null SITE_nm_sknew m mw5 ra s0 sp
              (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) outer cgx4
              (cg_has_site _ _ _ _ _ cgh4 ltac:(unfold NM_SITES; right; right; right; left; reflexivity))
              (cg_has_call _ _ _ _ _ cgh4 ltac:(unfold NM_CALLS; right; right; right; left; reflexivity))
              chain_m top_w5 ra_cells_w5 ltac:(rewrite fsp_val; clear - pad_two; lia) ltac:(unfold USTACK_TOP; clear - sp_top; lia))
    as (cgx_s & chain_s).
  rewrite <- (unsigned_lit SITE_nm_sknew) in cgx_s by (unfold SITE_nm_sknew; lia).
  assert (cg_skn4 : cg_has (rt_cg RT R4) [(SITE_OPENSSL_sk_new_null_1, e_OPENSSL_sk_new_null); (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)]
                      [(SITE_OPENSSL_sk_new_null_1, e_CRYPTO_zalloc); (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)])
    by (apply (cg_has_weaken _ _ _ _ _ cgh4); vm_compute; reflexivity).
  (* the name-number stack *)
  refine (C_SKN R4 Pm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mw5 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary
            only_fd stable eq_refl art_w5 inv_w5 cok_w5
            ltac:(rewrite fsp_val; unfold RT_STACK; clear - room pad_two; lia) cgx_s chain_s cg_skn4
            ltac:(rewrite live_R4, live_R3, live_R2, live_R1; cbn [length]; clear - few_live; lia)
            ltac:(rewrite credit_R4, credit3; unfold NM_COST in enough_credit; change (mcost 40) with 0 in enough_credit;
                  change (mcost 56) with 0 in enough_credit |- *; clear - enough_credit; lia)
            env_w5 T c10 at_c10' _).
  intros c11 after_sk.
  destruct after_sk as (R5 & sk & at_c11 & live_R5 & frames_R5 & sp0_R5 & credit_R5 & sk_pos & sk_al & sk_top & cg_R5).
  destruct (ASTA_unpack RT R5 Pm _ c11 at_c11) as (ms11 & (mk6 & ret_k6 & aft_k6 & pres_k6 & env_k6 & wr_sk & acc_sk & sk_cells_k6) & at_c11').
  clear at_c11.
  destruct ret_k6 as (t0_6 & t1_6 & t2_6 & a1_6 & a2_6 & a3_6 & a4_6 & a5_6 & a6_6 & a7_6 & t3_6 & t4_6 & t5_6 & t6_6 & F_6 & fc_6 & ->).
  destruct aft_k6 as (art_k6 & inv_k6 & wm_k6 & stk_k6).
  rewrite (ret_pc_even SITE_nm_sknew) in at_c11' by (unfold SITE_nm_sknew; lia).
  rewrite fsp_val in stk_k6, pres_k6.
  (* thunk installation for the stack: three calls that only write the stack record *)
  pose proof (nm_w6 sp gp (Z_to_bv 64 TP_A) t0_6 t1_6 t2_6 a1_6 a2_6 a3_6 a4_6 a5_6 a6_6 a7_6 s4 s8 s9 s10 s11 t3_6 t4_6 t5_6 t6_6
                F_6 fc_6 mk6 fb nm sk pad inv_k6) as step.
  cl_lift step at_c11' c12 at_c12.
  destruct (ASTA_unpack RT R5 Pm _ c12 at_c12) as (ms12 & -> & at_c12'). clear at_c12.
  assert (sk_in5 : In (sk, 56) (rt_live RT R5)) by (rewrite live_R5; left; reflexivity).
  assert (in5 : forall e, In e (rt_live RT R4) -> In e (rt_live RT R5)) by (intros e e_in; rewrite live_R5; right; exact e_in).
  pose proof (afp_live_hi RT GOBJ AFP R5 mk6 sk 56 art_k6 sk_in5 ltac:(lia)) as sk_hi.
  pose proof (af_live_range RT AF R5 mk6 sk 56 art_k6 sk_in5) as (_ & sk_win & _).
  unfold STACK_WIN in sk_win. rewrite sp0_R5, sp0_R4, sp0_R3, sp0_R2, sp0_R1 in sk_win.
  assert (apart5 : forall p n, In (p, n) (rt_live RT R4) -> sk + 56 <= p \/ p + n <= sk)
    by (intros p n pn_in; exact (wg_live_apart RT AF R5 mk6 [] sk 56 (rt_live RT R4) p n art_k6 live_R5 pn_in)).
  pose proof (apart5 nm 40 nm_in4) as sk_nm. pose proof (apart5 lk 40 lk_in4) as sk_lk.
  assert (fb_in5 : In (fb, 1%nat) (rt_frames RT R5)) by (rewrite frames_R5; exact fb_in4).
  pose proof (af_frames_range RT AF R5 mk6 fb 1 art_k6 fb_in5) as (_ & _ & _ & fb_sep5).
  change (fs_size 1) with 128 in fb_sep5. pose proof (fb_sep5 sk 56 sk_in5) as fb_sk.
  pose proof (af_fshadow_apart RT AF R5 mk6 fb 1 art_k6 fb_in5) as (sh_live5 & _).
  change (fs_size 1) with 128 in sh_live5. unfold shad, SHB in sh_live5.
  assert (lo_win5 : rt_sp0 RT R5 - 8388608 <= lo) by (rewrite sp0_R5; exact lo_win4).
  assert (cok5 : forall mm, stk asegs mm lo (bv_unsigned sp + -96 - pad) -> call_ok RT R5 mm (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) lo).
  { intros mm stk_mm. unfold call_ok. rewrite fsp_val, sp0_R5, sp0_R4, sp0_R3, sp0_R2, sp0_R1. split; [exact stk_mm|].
    unfold RT_STACK, STACK_WIN, USTACK_TOP. clear - lo_win room sp_top pad_is pad_two sp_al16. repeat split; lia. }
  (* everything this frame still needs that a thunk setter leaves alone *)
  assert (setter_keep : forall (mm mm' : mem) (P : Z -> Prop),
            rt_pres_fp (rt_live RT R5) (rt_frames RT R5) (bv_unsigned sp + -96 - pad) [(sk, sk + 56)] mm mm' ->
            (forall x, P x -> aclient (rt_live RT R5) (rt_frames RT R5) (bv_unsigned sp + -96 - pad) x /\ ~ (sk <= x < sk + 56)) ->
            agree_on P mm mm').
  { intros mm mm' P pres_mm P_ok. apply (agree_of_pres_fp _ _ _ _ _ _ _ pres_mm).
    intros x px. destruct (P_ok x px) as (cl_x & off_sk). split; [exact cl_x|]. cbn [outside]. split; [exact off_sk | exact I]. }
  refine (C_SKCMP R5 Pm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mk6 lo sk
            (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
            only_fd stable eq_refl eq_refl art_k6 inv_k6 (cok5 mk6 stk_k6)
            ltac:(rewrite fsp_val; clear - room pad_two; lia) sk_in5 sk_al sk_cells_k6 (ubs_raw8 sk ltac:(clear - sk_al; lia))
            T c12 at_c12' _).
  intros c13 after_cmp.
  destruct (ASTA_unpack RT R5 Pm _ c13 after_cmp) as (ms13 & (mc7 & ret_c7 & aft_c7 & pres_c7 & sk_cells_c7) & at_c13').
  clear after_cmp.
  destruct ret_c7 as (t0_7 & t1_7 & t2_7 & a1_7 & a2_7 & a3_7 & a4_7 & a5_7 & a6_7 & a7_7 & t3_7 & t4_7 & t5_7 & t6_7 & F_7 & fc_7 & ->).
  destruct aft_c7 as (art_c7 & inv_c7 & wm_c7 & stk_c7).
  rewrite (ret_pc_even SITE_nm_cmp) in at_c13' by (unfold SITE_nm_cmp; lia).
  rewrite fsp_val in stk_c7, pres_c7.
  pose proof (nm_w7 sp gp (Z_to_bv 64 TP_A) t0_7 t1_7 t2_7 a1_7 a2_7 a3_7 a4_7 a5_7 a6_7 a7_7 s8 s9 s10 s11 t3_7 t4_7 t5_7 t6_7
                F_7 fc_7 mc7 fb nm sk pad inv_c7) as step.
  cl_lift step at_c13' c14 at_c14.
  destruct (ASTA_unpack RT R5 Pm _ c14 at_c14) as (ms14 & -> & at_c14'). clear at_c14.
  refine (C_SKCPY R5 Pm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc7 lo sk
            (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 NM_CMP_THUNK) (Z_to_bv 64 0) (Z_to_bv 64 0)
            only_fd stable eq_refl eq_refl art_c7 inv_c7 (cok5 mc7 stk_c7)
            ltac:(rewrite fsp_val; clear - room pad_two; lia) sk_in5 sk_al sk_cells_c7 (ubs_raw8 sk ltac:(clear - sk_al; lia))
            T c14 at_c14' _).
  intros c15 after_cpy.
  destruct (ASTA_unpack RT R5 Pm _ c15 after_cpy) as (ms15 & (mc8 & ret_c8 & aft_c8 & pres_c8 & sk_cells_c8) & at_c15').
  clear after_cpy.
  destruct ret_c8 as (t0_8 & t1_8 & t2_8 & a1_8 & a2_8 & a3_8 & a4_8 & a5_8 & a6_8 & a7_8 & t3_8 & t4_8 & t5_8 & t6_8 & F_8 & fc_8 & ->).
  destruct aft_c8 as (art_c8 & inv_c8 & wm_c8 & stk_c8).
  rewrite (ret_pc_even SITE_nm_copy) in at_c15' by (unfold SITE_nm_copy; lia).
  rewrite fsp_val in stk_c8, pres_c8.
  pose proof (nm_w8 sp gp (Z_to_bv 64 TP_A) t0_8 t1_8 t2_8 a1_8 a2_8 a3_8 a4_8 a5_8 a6_8 a7_8 s8 s9 s10 s11 t3_8 t4_8 t5_8 t6_8
                F_8 fc_8 mc8 fb nm sk pad inv_c8) as step.
  cl_lift step at_c15' c16 at_c16.
  destruct (ASTA_unpack RT R5 Pm _ c16 at_c16) as (ms16 & -> & at_c16'). clear at_c16.
  refine (C_SKSET R5 Pm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc8 lo sk
            (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 NM_CMP_THUNK) (Z_to_bv 64 0)
            (Z_to_bv 64 NM_COPY_THUNK)
            only_fd stable eq_refl eq_refl art_c8 inv_c8 (cok5 mc8 stk_c8)
            ltac:(rewrite fsp_val; clear - room pad_two; lia) sk_in5 sk_al sk_cells_c8 (ubs_raw8 sk ltac:(clear - sk_al; lia))
            T c16 at_c16' _).
  intros c17 after_set.
  destruct (ASTA_unpack RT R5 Pm _ c17 after_set) as (ms17 & (mc9 & ret_c9 & aft_c9 & pres_c9 & sk_cells_c9) & at_c17').
  clear after_set.
  destruct ret_c9 as (t0_9 & t1_9 & t2_9 & a1_9 & a2_9 & a3_9 & a4_9 & a5_9 & a6_9 & a7_9 & t3_9 & t4_9 & t5_9 & t6_9 & F_9 & fc_9 & ->).
  destruct aft_c9 as (art_c9 & inv_c9 & wm_c9 & stk_c9).
  rewrite (ret_pc_even SITE_nm_set) in at_c17' by (unfold SITE_nm_set; lia).
  rewrite fsp_val in stk_c9, pres_c9.
  assert (thunks : agree_on (fun x => aclient (rt_live RT R5) (rt_frames RT R5) (bv_unsigned sp + -96 - pad) x /\ ~ (sk <= x < sk + 56)) mk6 mc9).
  { apply (agree_trans _ mk6 mc8 mc9); [apply (agree_trans _ mk6 mc7 mc8)|];
      [apply (setter_keep _ _ _ pres_c7) | apply (setter_keep _ _ _ pres_c8) | apply (setter_keep _ _ _ pres_c9)]; intros x px; exact px. }
  assert (wm_6_9 : wmono asegs mk6 mc9) by exact (wmono_trans asegs mk6 mc7 mc9 wm_c7 (wmono_trans asegs mc7 mc8 mc9 wm_c8 wm_c9)).
  (* the namemap record, from the table return to the stack store *)
  assert (nm_cells_k6 : rw_cells asegs mk6 nm [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 ht); C8 (Z_to_bv 64 lk); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
  { apply (wg_keep_live _ _ _ _ mw5 mk6 nm 40 nm _ nm_cells_w5 pres_k6 wm_k6 nm_in4); [lia | cbn [cells_size csize Nat.add]; lia |].
    intros x x_in. cbn [cells_size csize Nat.add] in x_in. cbn [outside]. unfold G_ALLOW_CUST.
    split; [clear - x_in nm_hi; lia | exact I]. }
  assert (nm_cells_c9 : rw_cells asegs mc9 nm [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 ht); C8 (Z_to_bv 64 lk); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_agree asegs mk6 mc9 _ _ nm_cells_k6); [| exact wm_6_9].
    apply (agree_sub _ _ mk6 mc9 thunks). intros x x_in. cbn [cells_size csize Nat.add] in x_in. split.
    - apply (acl_live _ _ _ nm 40); [exact (in5 _ nm_in4) | clear - x_in; lia].
    - clear - x_in sk_nm. lia. }
  pose proof (af_acc_live RT AF R5 mc9 nm 40 art_c9 (in5 _ nm_in4)) as (_ & acc_nm_c9).
  pose proof (nm_w9 sp gp (Z_to_bv 64 TP_A) t0_9 t1_9 t2_9 a1_9 a2_9 a3_9 a4_9 a5_9 a6_9 a7_9 s8 s9 s10 s11 t3_9 t4_9 t5_9 t6_9
                F_9 fc_9 mc9 fb nm lk ht sk pad fb_pos ltac:(clear - fb_win sp0_high; lia) nm_hi ltac:(clear - nm_win sp0_high; lia)
                ltac:(clear - nm_al; lia) sk_pos ltac:(unfold USTACK_TOP in sk_top; clear - sk_top; lia) nm_cells_c9 acc_nm_c9 inv_c9) as step.
  cl_lift step at_c17' c18 at_c18.
  destruct (ASTA_unpack RT R5 Pm _ c18 at_c18) as (ms18 & (mw9 & -> & mu_w9 & wm_w9 & inv_w9 & nm_cells_w9) & at_c18').
  clear at_c18.
  assert (nm_slot24 : forall x, x < nm \/ nm + 40 <= x -> outside [(nm + 24, nm + 32)] x)
    by (intros x x_far; cbn [outside]; split; [clear - x_far; lia | exact I]).
  assert (art_w9 : ART RT R5 mw9).
  { apply (af_frame RT AF R5 mc9 mw9 lo art_c9 lo_win5); [| exact wm_w9].
    intros a not_cl. apply mu_w9. cbn [outside]. split; [| exact I]. intros inside. apply not_cl.
    apply (acl_live _ _ _ nm 40); [exact (in5 _ nm_in4) | clear - inside; lia]. }
  assert (stk_w9 : stk asegs mw9 lo (bv_unsigned sp + -96 - pad)).
  { apply (stk_munch _ mc9 mw9 _ _ stk_c9 mu_w9 wm_w9). intros x x_rng. apply nm_slot24. clear - x_rng nm_win lo_win. lia. }
  (* fake frame retired: its descriptor and shadow are rewritten *)
  assert (wm_1_9 : wmono asegs mk1 mw9).
  { apply (wmono_trans asegs mk1 mw1 mw9 wm_w1), (wmono_trans asegs mw1 mk2 mw9 wm_k2), (wmono_trans asegs mk2 mw2 mw9 wm_w2),
      (wmono_trans asegs mw2 mk3 mw9 wm_k3), (wmono_trans asegs mk3 mk4 mw9 wm_k4), (wmono_trans asegs mk4 mw4 mw9 wm_w4),
      (wmono_trans asegs mw4 mw5 mw9 wm_4_5), (wmono_trans asegs mw5 mk6 mw9 wm_k6), (wmono_trans asegs mk6 mc9 mw9 wm_6_9). exact wm_w9. }
  pose proof (wr_at_rw_CB mw9 (fb + 0) 32 (wr_sub mw9 fb 120 0 32 (wr_at_wm mk1 mw9 fb 120 wr_fb wm_1_9) ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia))
    as (hjunk & hcell_w9).
  replace (fb + 0) with fb in hcell_w9 by lia.
  pose proof (wr_at_rw_CB mw9 (fb / 8 + 2147450880) 16 (wr_at_wm mk1 mw9 _ 16 wr_fbsh wm_1_9) ltac:(lia)) as (sjunk9 & scell_w9).
  pose proof (nm_w10 sp gp (Z_to_bv 64 TP_A) t0_9 t1_9 t2_9 (Z_to_bv 64 sk) (Z_to_bv 64 (nm + 24)) (Z_to_bv 64 0) a3_9 a4_9 a5_9 a6_9 a7_9
                s8 s9 s10 s11 t3_9 t4_9 t5_9 t6_9 F_9 fc_9 mw9 fb nm sk lo pad hjunk sjunk9
                ltac:(clear - room; lia) ltac:(clear - lo_floor; lia) ltac:(clear - sp_top; lia) fb_pos ltac:(clear - fb_seg; lia)
                ltac:(clear - fb_win lo_win; lia) ltac:(clear - fb_hi; lia) stk_w9 hcell_w9 scell_w9 inv_w9) as step.
  cl_lift step at_c18' c19 at_c19.
  destruct (ASTA_unpack RT R5 Pm _ c19 at_c19)
    as (ms19 & (a0_10 & hj10 & sj10 & mw10 & -> & mu_w10 & wm_w10 & inv_w10 & stk_w10 & hcell_w10 & scell_w10) & at_c19').
  clear at_c19.
  assert (off_frame : forall x, (x < fb \/ fb + 128 <= x) -> (x < fb / 8 + 2147450880 \/ fb / 8 + 2147450880 + 16 <= x) ->
                      outside [(fb, fb + 32); (fb / 8 + 2147450880, fb / 8 + 2147450880 + 16)] x)
    by (intros x x_far x_far'; cbn [outside]; repeat split; clear - x_far x_far'; lia).
  assert (art_w10 : ART RT R5 mw10).
  { apply (af_frame RT AF R5 mw9 mw10 lo art_w9 lo_win5); [| exact wm_w10].
    intros a not_cl. apply mu_w10. cbn [outside]. split; [| split; [| exact I]]; intros inside; apply not_cl.
    - apply (acl_frame _ _ _ fb 1%nat); [rewrite frames_R5, frames_R4; exact fb_in3|]. change (fs_size 1) with 128. clear - inside. lia.
    - apply (acl_fshadow _ _ _ fb 1%nat); [rewrite frames_R5, frames_R4; exact fb_in3|].
      unfold shad, SHB. change (fs_size 1) with 128. clear - inside. lia. }
  assert (frames_R5' : rt_frames RT R5 = (fb, 1%nat) :: rt_frames RT R0)
    by (rewrite frames_R5, frames_R4, frames_R3, frames_R2; exact frames_R1).
  destruct (af_frame_release RT AF R5 mw10 fb 1 (rt_frames RT R0) art_w10 frames_R5')
    as (R6 & fl & flag10 & fl_far & fl_pos & fl_win & fl_ptr & release).
  change (fs_size 1) with 128 in fl_ptr. replace (fb + 128 - 8) with (fb + 120) in fl_ptr by lia.
  unfold STACK_WIN in fl_win. rewrite sp0_R5, sp0_R4, sp0_R3, sp0_R2, sp0_R1 in fl_win.
  (* the stack window of this frame, untouched since the table call *)
  assert (win_10 : agree_on (fun x => bv_unsigned sp + -96 - pad <= x < bv_unsigned sp) mw4 mw10).
  { apply (agree_trans _ mw4 mw9 mw10); [apply (agree_trans _ mw4 mc9 mw9); [apply (agree_trans _ mw4 mk6 mc9); [apply (agree_trans _ mw4 mw5 mk6 win_w5)|]|]|].
    - apply (agree_of_pres_fp _ _ _ _ _ _ _ pres_k6). intros x x_rng. split; [apply upper_cl; exact x_rng|].
      cbn [outside]. unfold G_ALLOW_CUST. split; [clear - x_rng lo_floor room pad_two; lia | exact I].
    - apply (agree_sub _ _ mk6 mc9 thunks). intros x x_rng. split; [apply upper_cl; exact x_rng | clear - x_rng sk_win lo_win room pad_two; lia].
    - apply (agree_of_munch _ mc9 mw9 _ mu_w9). intros x x_rng. apply nm_slot24. clear - x_rng nm_win lo_win room pad_two. lia.
    - apply (agree_of_munch _ mw9 mw10 _ mu_w10). intros x x_rng. apply off_frame; clear - x_rng fb_win fb_pos lo_win lo_floor sp0_high room pad_two; lia. }
  assert (wm_4_10 : wmono asegs mw4 mw10).
  { apply (wmono_trans asegs mw4 mw5 mw10 wm_4_5), (wmono_trans asegs mw5 mk6 mw10 wm_k6), (wmono_trans asegs mk6 mc9 mw10 wm_6_9),
      (wmono_trans asegs mc9 mw9 mw10 wm_w9). exact wm_w10. }
  assert (regs_w10 : rw_cells asegs mw10 (bv_unsigned sp + -96) [CB 24 spill_w1; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs mw4 mw10 _ _ regs_w4); [| exact wm_4_10].
    apply (agree_sub _ _ mw4 mw10 win_10). intros x x_in. cbn [cells_size csize Nat.add] in x_in. clear - x_in pad_two. lia. }
  assert (padgap_w10 : stk asegs mw10 (bv_unsigned sp + -96 - pad) (bv_unsigned sp + -96)).
  { apply (stk_agree asegs mw4 mw10 _ _ padgap_w4); [| exact wm_4_10].
    apply (agree_sub _ _ mw4 mw10 win_10). intros x x_in. clear - x_in pad_two. lia. }
  (* return: fake frame released, saved registers reloaded *)
  pose proof (nm_w11 ra sp gp (Z_to_bv 64 TP_A) t0_9 t1_9 t2_9 a0_10 (Z_to_bv 64 (nm + 24)) (Z_to_bv 64 0) a3_9 a4_9 a5_9 a6_9 a7_9
                s8 s9 s10 s11 t3_9 t4_9 t5_9 t6_9 s0 s1 s2 s3 s4 s5 s6 s7 F_9 fc_9 mw10 nm fb sk fl lo pad spill_w1
                pad_two ltac:(clear - room; lia) ltac:(clear - lo_floor; lia) ltac:(clear - sp_top; lia) fb_pos
                ltac:(clear - fb_win lo_win; lia) fl_pos ltac:(clear - fl_win lo_win; lia) stk_w10 padgap_w10 regs_w10 fl_ptr flag10 inv_w10)
    as step.
  cl_lift step at_c19' c20 at_c20.
  destruct (ASTA_unpack RT R5 Pm _ c20 at_c20) as (ms20 & (mend & -> & mu_end & wm_end & inv_end & stk_end & flag_end) & at_c20').
  clear at_c20.
  destruct (release mend mu_end wm_end flag_end) as (art_end & frames_R6 & live_R6 & sp0_R6 & credit_R6 & allow_R6 & artm_R6 & cg_R6).
  (* what the caller sees *)
  assert (fl_off_live : forall p n x, In (p, n) (rt_live RT R5) -> p <= x < p + n -> x <> fl).
  { intros p n x pn_in x_rng x_fl. subst x. apply fl_far. exact (acl_live _ _ _ p n fl pn_in x_rng). }
  assert (fl_munch : forall x, x <> fl -> outside [(fl, fl + 1)] x)
    by (intros x x_ne; cbn [outside]; split; [clear - x_ne; lia | exact I]).
  assert (caller_in4 : forall x, aclient (rt_live RT R0) (rt_frames RT R0) (bv_unsigned sp) x ->
                       aclient (rt_live RT R4) (rt_frames RT R4) (bv_unsigned sp + -96 - pad) x).
  { intros x owned. apply (aclient_mono _ _ _ _ _ _ _ (caller_in3 x owned)); [exact in4 | rewrite frames_R4; intros e e_in; exact e_in | lia]. }
  assert (caller_in5 : forall x, aclient (rt_live RT R0) (rt_frames RT R0) (bv_unsigned sp) x ->
                       aclient (rt_live RT R5) (rt_frames RT R5) (bv_unsigned sp + -96 - pad) x).
  { intros x owned. apply (aclient_mono _ _ _ _ _ _ _ (caller_in4 x owned)); [exact in5 | rewrite frames_R5; intros e e_in; exact e_in | lia]. }
  assert (caller_off_sk : forall x, aclient (rt_live RT R0) (rt_frames RT R0) (bv_unsigned sp) x -> ~ (sk <= x < sk + 56)).
  { intros x owned.
    exact (newchunk_apart RT AF R4 R5 mk6 sk 56 (bv_unsigned sp + -96 - pad) x art_k6 live_R5 frames_R5 sp0_R5
             ltac:(rewrite sp0_R4, sp0_R3, sp0_R2, sp0_R1; unfold STACK_WIN; clear - lo_win room pad_two; lia) ltac:(lia) (caller_in4 x owned)). }
  assert (caller_not_fl : forall x, aclient (rt_live RT R0) (rt_frames RT R0) (bv_unsigned sp) x -> x <> fl).
  { intros x owned x_fl. destruct (caller_split x owned) as [side | side]; [clear - side x_fl fl_win lo_win room; lia|].
    subst x. apply fl_far. destruct owned as [on_stack | [is_static | [in_lv | [in_fr | in_fs]]]].
    - clear - on_stack side room. lia.
    - right; left; exact is_static.
    - right; right; left. destruct in_lv as (pp & nn & pin & prng). exists pp, nn. split; [| exact prng].
      apply in5, in4. rewrite live_R3, live_R2, live_R1. right; right; exact pin.
    - right; right; right; left. destruct in_fr as (ff & kk & fin & frng). exists ff, kk. split; [| exact frng].
      rewrite frames_R5'. right; exact fin.
    - right; right; right; right. destruct in_fs as (ff & kk & fin & frng). exists ff, kk. split; [| exact frng].
      rewrite frames_R5'. right; exact fin. }
  assert (caller_end : agree_on (fun x => aclient (rt_live RT R0) (rt_frames RT R0) (bv_unsigned sp) x
                                        /\ outside [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] x) m mend).
  { apply (agree_trans _ m mw10 mend); [apply (agree_trans _ m mw9 mw10); [apply (agree_trans _ m mc9 mw9);
      [apply (agree_trans _ m mk6 mc9); [apply (agree_trans _ m mw5 mk6 caller_w5)|]|]|]|].
    - apply (agree_of_pres_fp _ _ _ _ _ _ _ pres_k6). intros x (owned & off_g). exact (conj (caller_in4 x owned) off_g).
    - apply (agree_sub _ _ mk6 mc9 thunks). intros x (owned & _). exact (conj (caller_in5 x owned) (caller_off_sk x owned)).
    - apply (agree_of_munch _ mc9 mw9 _ mu_w9). intros x (owned & _). apply nm_slot24.
      pose proof (caller_off_nm x owned) as off_nm. clear - off_nm. lia.
    - apply (agree_of_munch _ mw9 mw10 _ mu_w10). intros x (owned & _).
      destruct (caller_off_fb x owned) as (nf & ns). apply off_frame; clear - nf ns; lia.
    - apply (agree_of_munch _ mw10 mend _ mu_end). intros x (owned & _). exact (fl_munch x (caller_not_fl x owned)). }
  assert (wm_all : wmono asegs m mend).
  { apply (wmono_trans asegs m mw0 mend wm_w0), (wmono_trans asegs mw0 mk1 mend wm_k1), (wmono_trans asegs mk1 mw9 mend wm_1_9),
      (wmono_trans asegs mw9 mw10 mend wm_w10). exact wm_end. }
  assert (env_end : cl_env mend (Z_to_bv 8 1) canary).
  { apply (cl_env_agree mk6 mend _ _ env_k6). intros a cell_a.
    pose proof (cl_cell_static _ cell_a) as a_static. pose proof (client_static_range _ a_static) as a_rng. unfold SEGTOP_A in a_rng.
    assert (a_ne : bv_unsigned a <> fl) by (intros a_fl; apply fl_far; rewrite <- a_fl; apply acl_static; exact a_static).
    rewrite (mu_end a (fl_munch _ a_ne)), (mu_w10 a ltac:(apply off_frame; clear - a_rng fb_seg; lia)),
      (mu_w9 a ltac:(apply nm_slot24; clear - a_rng nm_hi; lia)).
    apply thunks. split; [apply acl_static; exact a_static | clear - a_rng sk_hi; lia]. }
  assert (late_keep : forall p n, In (p, n) (rt_live RT R5) -> nm + 40 <= p \/ p + n <= nm -> fb + 128 <= p \/ p + n <= fb ->
                      agree_on (fun x => p <= x < p + n) mc9 mend).
  { intros p n pn_in off_nm off_fb.
    pose proof (sh_live5 p n pn_in) as off_sh.
    apply (agree_trans _ mc9 mw10 mend); [apply (agree_trans _ mc9 mw9 mw10)|].
    - apply (agree_of_munch _ mc9 mw9 _ mu_w9). intros x x_rng. apply nm_slot24. clear - x_rng off_nm. lia.
    - apply (agree_of_munch _ mw9 mw10 _ mu_w10). intros x x_rng. apply off_frame; clear - x_rng off_fb off_sh fb_al; lia.
    - apply (agree_of_munch _ mw10 mend _ mu_end). intros x x_rng. exact (fl_munch x (fl_off_live p n x pn_in x_rng)). }
  assert (wm_9_end : wmono asegs mc9 mend)
    by exact (wmono_trans asegs mc9 mw9 mend wm_w9 (wmono_trans asegs mw9 mw10 mend wm_w10 wm_end)).
  assert (sk_end : rw_cells asegs mend sk nm_sk_cells).
  { apply (rw_cells_agree asegs mc9 mend _ _ sk_cells_c9); [| exact wm_9_end].
    apply (agree_sub _ _ mc9 mend (late_keep sk 56 sk_in5 (proj1 (or_comm _ _) sk_nm) fb_sk)).
    intros x x_in. cbn [cells_size csize Nat.add] in x_in. clear - x_in. lia. }
  assert (nm_end : rw_cells asegs mend nm [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 ht); C8 (Z_to_bv 64 lk); C8 (Z_to_bv 64 sk); C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_agree asegs mw9 mend _ _ nm_cells_w9); [| exact (wmono_trans asegs mw9 mw10 mend wm_w10 wm_end)].
    apply (agree_trans _ mw9 mw10 mend).
    - apply (agree_of_munch _ mw9 mw10 _ mu_w10). intros x x_in. cbn [cells_size csize Nat.add] in x_in.
      pose proof (sh_live5 nm 40 (in5 _ nm_in4)) as off_sh. apply off_frame; clear - x_in fb_nm off_sh fb_al; lia.
    - apply (agree_of_munch _ mw10 mend _ mu_end). intros x x_in. cbn [cells_size csize Nat.add] in x_in.
      apply fl_munch. apply (fl_off_live nm 40 x (in5 _ nm_in4)). clear - x_in. lia. }
  assert (lk_end : rw_cells asegs mend lk (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { apply (rw_cells_agree asegs mw4 mend _ _ lk_mutex_w4);
      [| exact (wmono_trans asegs mw4 mk6 mend (wmono_trans asegs mw4 mw5 mk6 wm_4_5 wm_k6) (wmono_trans asegs mk6 mc9 mend wm_6_9 wm_9_end))].
    cbn [mutex_cells cells_size csize Nat.add].
    apply (agree_trans _ mw4 mc9 mend); [apply (agree_trans _ mw4 mk6 mc9); [apply (agree_trans _ mw4 mw5 mk6); [apply (agree_trans _ mw4 mh mw5)|]|]|].
    - apply h_keep. intros x x_in. split; [apply (acl_live _ _ _ lk 40); [exact lk_in3 | clear - x_in; lia]|].
      cbn [outside]. unfold G_ALLOW_CUST. split; [clear - x_in lk_hi; lia | exact I].
    - apply (agree_of_munch _ mh mw5 _ mu_w5). intros x x_in. apply nm_slot8. clear - x_in lk_nm. lia.
    - apply (agree_of_pres_fp _ _ _ _ _ _ _ pres_k6). intros x x_in. split; [apply (acl_live _ _ _ lk 40); [exact lk_in4 | clear - x_in; lia]|].
      cbn [outside]. unfold G_ALLOW_CUST. split; [clear - x_in lk_hi; lia | exact I].
    - apply (agree_sub _ _ mk6 mc9 thunks). intros x x_in. split; [apply (acl_live _ _ _ lk 40); [exact (in5 _ lk_in4) | clear - x_in; lia]|].
      clear - x_in sk_lk. lia.
    - exact (late_keep lk 40 (in5 _ lk_in4) ltac:(clear - lk_nm; lia) fb_lk). }
  (* the hash table's own chunks: allocated by the table call, untouched by the rest of the body *)
  assert (wm_h_end : wmono asegs mh mend)
    by exact (wmono_trans asegs mh mw5 mend wm_w5 (wmono_trans asegs mw5 mk6 mend wm_k6 (wmono_trans asegs mk6 mc9 mend wm_6_9 wm_9_end))).
  assert (cell_keep : forall (p n off X : Z) (cs : list cell), rw_cells asegs mh X cs -> In (p, n) (rt_live RT R4) ->
                      (n <=? 64512) = true -> (0 <=? off) = true -> (off + Z.of_nat (cells_size cs) <=? n) = true -> X = p + off ->
                      (p + n <= nm \/ nm + 40 <= p) -> rw_cells asegs mend X cs).
  { intros p n off X cs cells_h pn_in n_small off_lo off_hi X_is off_nm.
    apply Z.leb_le in n_small, off_lo, off_hi. subst X.
    assert (lo_X : p <= p + off) by (clear - off_lo; lia).
    assert (hi_X : p + off + Z.of_nat (cells_size cs) <= p + n) by (clear - off_hi; lia).
    pose proof (afp_live_hi RT GOBJ AFP R4 mh p n art_h pn_in n_small) as p_hi.
    pose proof (fb_sep5 p n (in5 _ pn_in)) as off_fb.
    pose proof (apart5 p n pn_in) as off_sk.
    apply (rw_cells_agree asegs mh mend _ _ cells_h); [| exact wm_h_end].
    apply (agree_sub (fun x => p <= x < p + n)); [| intros x x_in; clear - x_in lo_X hi_X; lia].
    apply (agree_trans _ mh mc9 mend); [apply (agree_trans _ mh mk6 mc9); [apply (agree_trans _ mh mw5 mk6)|]|].
    - apply (agree_of_munch _ mh mw5 _ mu_w5). intros x x_rng. apply nm_slot8. clear - x_rng off_nm. lia.
    - apply (agree_of_pres_fp _ _ _ _ _ _ _ pres_k6). intros x x_rng. split; [apply (acl_live _ _ _ p n); [exact pn_in | exact x_rng]|].
      cbn [outside]. unfold G_ALLOW_CUST. split; [clear - x_rng p_hi; lia | exact I].
    - apply (agree_sub _ _ mk6 mc9 thunks). intros x x_rng. split; [apply (acl_live _ _ _ p n); [exact (in5 _ pn_in) | exact x_rng]|].
      clear - x_rng off_sk. lia.
    - exact (late_keep p n (in5 _ pn_in) ltac:(clear - off_nm; lia) off_fb). }
  assert (ht_off_nm : forall l1 p n l2, rt_live RT R4 = l1 ++ (p, n) :: l2 -> In (nm, 40) (l1 ++ l2) -> p + n <= nm \/ nm + 40 <= p)
    by (intros l1 p n l2 split_eq nm_in; exact (wg_live_apart RT AF R4 mh l1 p n l2 nm 40 art_h split_eq nm_in)).
  assert (rq_in4 : In (rq, 16) (rt_live RT R4)) by (rewrite live_R4; left; reflexivity).
  assert (rl_in4 : In (rl, 264) (rt_live RT R4)) by (rewrite live_R4; right; left; reflexivity).
  assert (nb_in4 : In (nb, NB_BYTES) (rt_live RT R4)) by (rewrite live_R4; do 2 right; left; reflexivity).
  assert (md_in4 : In (md, 24) (rt_live RT R4)) by (rewrite live_R4; do 3 right; left; reflexivity).
  assert (hlk_in4 : In (hlk, 40) (rt_live RT R4)) by (rewrite live_R4; do 4 right; left; reflexivity).
  assert (ht_in4 : In (ht, 96) (rt_live RT R4)) by (rewrite live_R4; do 5 right; left; reflexivity).
  pose proof (ht_off_nm [] rq 16 _ live_R4 ltac:(apply in_or_app; right; repeat right; exact nm_in_l3)) as rq_nm.
  pose proof (ht_off_nm [(rq, 16)] rl 264 _ live_R4 ltac:(apply in_or_app; right; repeat right; exact nm_in_l3)) as rl_nm.
  pose proof (ht_off_nm [(rq, 16); (rl, 264)] nb NB_BYTES _ live_R4 ltac:(apply in_or_app; right; repeat right; exact nm_in_l3)) as nb_nm.
  pose proof (ht_off_nm [(rq, 16); (rl, 264); (nb, NB_BYTES)] md 24 _ live_R4
                ltac:(apply in_or_app; right; repeat right; exact nm_in_l3)) as md_nm.
  pose proof (ht_off_nm [(rq, 16); (rl, 264); (nb, NB_BYTES); (md, 24)] hlk 40 _ live_R4
                ltac:(apply in_or_app; right; repeat right; exact nm_in_l3)) as hlk_nm.
  pose proof (ht_off_nm [(rq, 16); (rl, 264); (nb, NB_BYTES); (md, 24); (hlk, 40)] ht 96 _ live_R4
                ltac:(apply in_or_app; right; exact nm_in_l3)) as ht_nm.
  pose proof (cell_keep ht 96 0 ht _ tab_h ht_in4 eq_refl eq_refl eq_refl (eq_sym (Z.add_0_r ht)) ht_nm) as tab_end.
  pose proof (cell_keep hlk 40 0 hlk _ hlk_h hlk_in4 eq_refl eq_refl eq_refl (eq_sym (Z.add_0_r hlk)) hlk_nm) as hlk_end.
  pose proof (cell_keep md 24 0 md _ md_h md_in4 eq_refl eq_refl eq_refl (eq_sym (Z.add_0_r md)) md_nm) as md_end.
  pose proof (cell_keep nb NB_BYTES 0 nb _ nb_h nb_in4 eq_refl eq_refl ltac:(vm_compute; reflexivity) (eq_sym (Z.add_0_r nb)) nb_nm)
    as nb_end.
  pose proof (cell_keep rl 264 0 rl _ rl_h rl_in4 eq_refl eq_refl eq_refl (eq_sym (Z.add_0_r rl)) rl_nm) as rl_end.
  pose proof (cell_keep rl 264 48 (rl + 48) _ rl48_h rl_in4 eq_refl eq_refl eq_refl eq_refl rl_nm) as rl48_end.
  pose proof (cell_keep rl 264 88 (rl + 88) _ rl88_h rl_in4 eq_refl eq_refl eq_refl eq_refl rl_nm) as rl88_end.
  pose proof (cell_keep rl 264 128 (rl + 128) _ rl128_h rl_in4 eq_refl eq_refl eq_refl eq_refl rl_nm) as rl128_end.
  pose proof (cell_keep rl 264 176 (rl + 176) _ rl176_h rl_in4 eq_refl eq_refl eq_refl eq_refl rl_nm) as rl176_end.
  pose proof (cell_keep rl 264 216 (rl + 216) _ rl216_h rl_in4 eq_refl eq_refl eq_refl eq_refl rl_nm) as rl216_end.
  pose proof (cell_keep rq 16 0 rq _ rq_h rq_in4 eq_refl eq_refl eq_refl (eq_sym (Z.add_0_r rq)) rq_nm) as rq_end.
  assert (in6 : forall e, In e (rt_live RT R5) -> In e (rt_live RT R6)) by (intros e e_in; rewrite live_R6; exact e_in).
  pose proof (af_acc_live RT AF R6 mend nm 40 art_end (in6 _ (in5 _ nm_in4))) as (_ & acc_nm_end).
  pose proof (af_acc_live RT AF R6 mend lk 40 art_end (in6 _ (in5 _ lk_in4))) as (_ & acc_lk_end).
  pose proof (af_acc_live RT AF R6 mend sk 56 art_end (in6 _ sk_in5)) as (_ & acc_sk_end).
  pose proof (af_acc_live RT AF R6 mend ht 96 art_end (in6 _ (in5 _ ht_in4))) as (_ & acc_ht_end).
  pose proof (af_acc_live RT AF R6 mend hlk 40 art_end (in6 _ (in5 _ hlk_in4))) as (_ & acc_hlk_end).
  pose proof (af_acc_live RT AF R6 mend md 24 art_end (in6 _ (in5 _ md_in4))) as (_ & acc_md_end).
  pose proof (af_acc_live RT AF R6 mend nb NB_BYTES art_end (in6 _ (in5 _ nb_in4))) as (_ & acc_nb_end).
  pose proof (af_acc_live RT AF R6 mend rl 264 art_end (in6 _ (in5 _ rl_in4))) as (_ & acc_rl_end).
  pose proof (af_acc_live RT AF R6 mend rq 16 art_end (in6 _ (in5 _ rq_in4))) as (_ & acc_rq_end).
  apply k_done. exists R6, nm, lk, ht, hlk, md, nb, rl, rq, sk. split.
  - apply (ASTA_conseq RT R6 Pm _ _ c20 (ASTA_switch RT R5 R6 Pm _ c20 at_c20' allow_R6 artm_R6)).
    intros ms <-. exists mend.
    split; [do 16 eexists; reflexivity|].
    split; [split; [exact art_end | split; [exact inv_end | split; [exact wm_all | exact stk_end]]]|].
    split; [intros a owned off_g; exact (caller_end a (conj owned off_g))|].
    split; [exact env_end|]. split; [exact nm_end|]. split; [exact acc_nm_end|].
    split; [exact lk_end|]. split; [exact acc_lk_end|].
    split; [exact tab_end|]. split; [exact acc_ht_end|].
    split; [exact hlk_end|]. split; [exact acc_hlk_end|].
    split; [exact md_end|]. split; [exact acc_md_end|].
    split; [exact nb_end|]. split; [exact acc_nb_end|].
    split; [exact rl_end|]. split; [exact rl48_end|]. split; [exact rl88_end|]. split; [exact rl128_end|].
    split; [exact rl176_end|]. split; [exact rl216_end|]. split; [exact acc_rl_end|].
    split; [exact rq_end|]. split; [exact acc_rq_end|].
    split; [exact sk_end|]. exact acc_sk_end.
  - rewrite ht_addr_eq in ht_addr.
    destruct ht_addr as (ht_pos & ht_al & ht_top & hlk_pos & hlk_al & hlk_top & md_pos & md_al & md_top
                         & nb_pos & nb_al & nb_top & rl_pos & rl_al & rl_top & rq_pos & rq_al & rq_top).
    rewrite live_R6, live_R5, live_R4, live_R3, live_R2, live_R1, frames_R6, sp0_R6, sp0_R5, sp0_R4, sp0_R3, sp0_R2, sp0_R1,
      credit_R6, credit_R5, credit_R4, credit3, cg_R6, cg_R5, cg_R4, cg_R3, cg_R2, cg_R1.
    unfold NM_COST. change (mcost 40) with 0. change (mcost 56) with 0.
    repeat split; try reflexivity; try assumption; ring.
Qed.
End NamemapNew.
