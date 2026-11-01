(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout Th_mutex Th_mutex_init Th_cond I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_G_kit Fz_ckit Fz_M_malloc Fz_M_zalloc Fz_env Fz_M_locknew Fz_M_aligned Fz_M_aligned_array Fz_G_CRYPTO_calloc Fz_G_ossl_lib_ctx_get_concrete Fz_T_rcuw Fz_T_rcu Fz_I2_anl Fz_I2_htw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Notation TP_A := (0xba3ef0)%Z (only parsing).

(* [comment removed for export] *)
Lemma memalign_plain_nb : memalign_plain 64 NB_BYTES.
Proof. unfold memalign_plain, NB_BYTES. repeat split; vm_compute; try reflexivity; try lia; discriminate. Qed.

(* [comment removed for export] *)
Lemma rw_CB_of_bytes : forall (m : mem) a bs, bytes_at asegs m a bs -> wr_at asegs m a (Z.of_nat (length bs)) -> rw_cells asegs m a [CB (length bs) bs].
Proof.
  intros m a bs got_bytes got_room.
  assert (one_cell : Z.of_nat (cells_size [CB (length bs) bs]) = Z.of_nat (length bs)) by (cbn [cells_size csize]; lia).
  split; [| rewrite one_cell; exact got_room].
  split.
  - cbn [cells_wf cell_wf]. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact got_bytes.
Qed.

Section HtNew.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis MCP : memcpy_icontract RT e_asan_memcpy.
Hypothesis C_CZ : crypto_zalloc_env_stmt RT.
Hypothesis C_LN : crypto_lock_new_env_stmt RT.
Hypothesis C_ANL : anl_stmt RT.
Hypothesis C_RCU : rcu_lock_new_stmt RT.

Definition HT_SITES : list (Z * Z) :=
  [(SITE_ht_zalloc1, e_ht_new); (SITE_ht_locknew, e_ht_new); (SITE_ht_zalloc2, e_ht_new); (SITE_ht_anl, e_ht_new); (SITE_ht_rcu, e_ht_new);
   (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc); (SITE_ln_zalloc, e_lock_new)] ++ ANL_SITES ++ RCU_SITES.
Definition HT_CALLS : list (Z * Z) :=
  [(SITE_ht_zalloc1, e_CRYPTO_zalloc); (SITE_ht_locknew, e_lock_new); (SITE_ht_zalloc2, e_CRYPTO_zalloc); (SITE_ht_anl, e_anl); (SITE_ht_rcu, e_rcu_lock_new);
   (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc); (SITE_ln_zalloc, e_CRYPTO_zalloc)] ++ ANL_CALLS ++ RCU_CALLS.
Definition HT_COST : Z := mcost 96 + 1 + mcost 24 + (1 + mcost NB_BYTES) + (1 + mcost 264 + mcost 16).

(* [comment removed for export] *)
Definition ht_new_stmt : Prop :=
  forall (Σ : rts RT) (PMc : Model -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (outer : list Z)
    (conf fcf : Z) (kcf : nat) (ctx : word) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc ->
  tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 conf ->
  In (fcf, kcf) (rt_frames RT Σ) -> fcf <= conf -> conf + 48 <= fcf + fs_size kcf - 8 -> conf mod 8 = 0 ->
  rw_cells asegs m conf (ht_conf ctx) -> acc asegs m conf 48 ->
  bv_unsigned ctx <> 0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  lo + RT_STACK + 656 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_ht_new (bv_unsigned ra :: outer) ->
  uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) HT_SITES HT_CALLS ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat ->
  Z.of_nat (length (rt_live RT Σ)) + 6 <= LIVE_MAX ->
  HT_COST <= rt_credit RT Σ ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_ht_new m)))
    (fun c => exists (Σ' : rts RT) (h lk md nb rl rq : Z),
       ASTA RT Σ' PMc
         (fun ms => exists m' : mem,
            ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 h) m' ms
            /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
            /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
            /\ cl_env m' (Z_to_bv 8 1) canary
            /\ rw_cells asegs m' h (ht_tab4 ctx rl lk md) /\ acc asegs m' h 96
            /\ rw_cells asegs m' lk (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) /\ acc asegs m' lk 40
            /\ rw_cells asegs m' md [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 511)] /\ acc asegs m' md 24
            /\ rw_cells asegs m' nb [CB (Z.to_nat NB_BYTES) (repeat (Z_to_bv 8 0) (Z.to_nat NB_BYTES))] /\ acc asegs m' nb NB_BYTES
            /\ rw_cells asegs m' rl (rcu_head ctx rq)
            /\ rw_cells asegs m' (rl + 48) (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
            /\ rw_cells asegs m' (rl + 88) (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
            /\ rw_cells asegs m' (rl + 128) cond_cells
            /\ rw_cells asegs m' (rl + 176) (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
            /\ rw_cells asegs m' (rl + 216) cond_cells
            /\ acc asegs m' rl 264
            /\ rw_cells asegs m' rq [CB 16 (repeat (Z_to_bv 8 0) 16)] /\ acc asegs m' rq 16) c
       /\ rt_live RT Σ' = (rq, 16) :: (rl, 264) :: (nb, NB_BYTES) :: (md, 24) :: (lk, 40) :: (h, 96) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ
       /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - HT_COST
       /\ 0 < h /\ h mod 16 = 0 /\ h + 96 < USTACK_TOP
       /\ 0 < lk /\ lk mod 16 = 0 /\ lk + 40 < USTACK_TOP
       /\ 0 < md /\ md mod 16 = 0 /\ md + 24 < USTACK_TOP
       /\ 0 < nb /\ nb mod 64 = 0 /\ nb + NB_BYTES < USTACK_TOP
       /\ 0 < rl /\ rl mod 16 = 0 /\ rl + 264 < USTACK_TOP
       /\ 0 < rq /\ rq mod 16 = 0 /\ rq + 16 < USTACK_TOP
       /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem ht_new_cps : ht_new_stmt.
Proof.
  unfold ht_new_stmt.
  intros S0 PM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer conf fcf kcf ctx lb canary
    pm_fds pm_stable tp_is a0_is cf_in cf_from cf_to cf_al8 cf_cells cf_acc ctx_nz
    art_e inv_e cok_e room_e cgx_e chain_e cgh_e nfr_e nlv_e cred_e env_e.
  intros T k_e start_e finish.
  subst tp a0.
  pose (apart := fun a n b k : Z => a + n <= b \/ b + k <= a).
  (* runtime facts at entry *)
  destruct cok_e as (stk_e & win_e & _ & top_e & sp16_e).
  pose proof (af_sp0_win RT AF S0 m art_e) as sp0_lo.
  pose proof (af_sp0_range RT AF S0 m art_e) as (_ & sp0_hi).
  pose proof (af_client_consts RT AF S0 m art_e) as (_ & shdyn_e & _ & _ & ut_e).
  pose proof (af_frames_range RT AF S0 m fcf kcf art_e cf_in) as (fcf_pos & fcf_win & _ & _).
  pose proof (af_frames_align RT AF S0 m fcf kcf art_e cf_in) as (_ & fcf_seg).
  pose proof (afp_frame_mem RT GOBJ AFP S0 m fcf kcf art_e cf_in) as (_ & fcf_47).
  assert (fs_pos : 0 <= fs_size kcf).
  { unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. pose proof (Z.pow_nonneg 2 (Z.of_nat kcf) ltac:(lia)). lia. }
  unfold SEGTOP_A in fcf_seg.
  assert (lo_big : 0x10007fff8000 <= lo) by (unfold STACK_WIN in win_e; lia).
  assert (sp_fit : bv_unsigned sp <= 2^47) by (unfold USTACK_TOP in top_e; lia).
  assert (lo_sp : lo + 656 <= bv_unsigned sp) by (unfold RT_STACK in room_e; lia).
  assert (csp_u : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; lia).
  (* the region the caller keeps, and four facts about it *)
  pose (keep0 := fun x => aclient (rt_live RT S0) (rt_frames RT S0) (bv_unsigned sp) x /\ outside [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] x).
  assert (keep0_side : forall x, keep0 x -> bv_unsigned sp <= x \/ x < lo).
  { intros x (kx & _). destruct (aclient_split RT AF S0 m (bv_unsigned sp) x art_e kx) as [up | down]; [left; exact up | right; lia]. }
  assert (keep0_lift : forall live', (forall e, In e (rt_live RT S0) -> In e live') ->
            forall x, keep0 x -> aclient live' (rt_frames RT S0) (bv_unsigned sp + -96) x /\ outside [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] x).
  { intros live' grows x (kx & ox). split; [| exact ox]. apply (aclient_mono _ _ _ _ _ _ _ kx grows); [tauto | lia]. }
  assert (cf_kept : forall x, conf <= x < conf + 48 -> keep0 x).
  { intros x xin. split.
    - apply (acl_frame _ _ _ fcf kcf); [exact cf_in | lia].
    - cbn [outside]. unfold G_ALLOW_CUST. split; [lia | exact I]. }
  assert (cfsh_kept : forall x, shad conf <= x <= shad (conf + 48 - 1) -> keep0 x).
  { intros x xin. split.
    - apply (acl_fshadow _ _ _ fcf kcf); [exact cf_in |]. unfold shad in *.
      pose proof (Z.div_le_mono fcf conf 8 ltac:(lia) ltac:(lia)).
      assert ((conf + 48 - 1) / 8 < (fcf + fs_size kcf) / 8) by (Z.div_mod_to_equations; lia). lia.
    - cbn [outside]. unfold shad, SHB, G_ALLOW_CUST in *. split; [| exact I].
      pose proof (Z.div_pos conf 8 ltac:(lia) ltac:(lia)). lia. }
  (* frame set-up, up to the first allocation *)
  pose proof (ht_w0 ra sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 conf) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                stk_e ltac:(lia) lo_big sp_fit ut_e shdyn_e inv_e) as walk.
  cl_lift walk start_e k_f at_f.
  destruct (ASTA_unpack RT S0 PM _ k_f at_f) as (ms_f & (junk_f & m_f & -> & mu_f & wm_f & inv_f & frame_f & stk_f) & at_f'). clear at_f.
  assert (art_f : ART RT S0 m_f).
  { apply (cl_seg_ART RT AF S0 m m_f (bv_unsigned sp) 96 [] art_e ltac:(lia) ltac:(lia) mu_f); [| exact wm_f].
    intros x no. exfalso. apply no. exact I. }
  assert (ag_f : agree_on keep0 m m_f).
  { apply (agree_of_munch _ m m_f _ mu_f). intros x kx. cbn [outside].
    destruct (keep0_side x kx); (split; [lia | exact I]). }
  assert (env_f : cl_env m_f lb canary).
  { apply (cl_env_seg _ m m_f lb canary env_e mu_f). apply cl_fp_cons; [| exact cl_fp_nil]. unfold ssp_guard. right; left. lia. }
  (* helper facts that later steps of this proof use *)
  pose proof (rw_cells_skip m_f _ [CB 8 junk_f; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] frame_f) as link_f.
  cbn [cells_size csize Nat.add] in link_f.
  replace (bv_unsigned sp + -96 + Z.of_nat 80) with (bv_unsigned sp - 16) in link_f by lia.
  pose (above := fun x => bv_unsigned sp - 96 <= x < USTACK_TOP).
  assert (link_at : forall (mi : mem) r G, agree_on above m_f mi -> wmono asegs m_f mi ->
            In (r, e_ht_new) HT_SITES -> In (r, G) HT_CALLS -> 0 <= r < 2^64 ->
            cg_ctx (rt_cg RT S0) G (bv_unsigned (Z_to_bv 64 r) :: bv_unsigned ra :: outer)
            /\ uw_chain mi (Z_to_bv 64 (bv_unsigned sp + -96)) sp (bv_unsigned ra :: outer)).
  { intros mi r G ag wm site call r_rng. rewrite (unsigned_lit r r_rng).
    apply (cl_chain_call (rt_cg RT S0) e_ht_new G r m mi ra s0 sp (Z_to_bv 64 (bv_unsigned sp + -96)) outer cgx_e).
    - exact (cg_has_site _ _ _ _ _ cgh_e site).
    - exact (cg_has_call _ _ _ _ _ cgh_e call).
    - exact chain_e.
    - apply (agree_trans _ m m_f mi).
      + apply (agree_sub _ _ _ _ ag_f). intros x xr. split; [apply acl_stack; exact xr |].
        cbn [outside]. unfold G_ALLOW_CUST. split; [lia | exact I].
      + apply (agree_sub _ _ _ _ ag). intros x xr. unfold above. lia.
    - apply (rw_cells_agree asegs m_f mi _ _ link_f); [| exact wm].
      apply (agree_sub _ _ _ _ ag). intros x xr. cbn [cells_size csize Nat.add] in xr. unfold above. lia.
    - rewrite csp_u. lia.
    - exact top_e. }
  assert (above_pres : forall live frs W (ma mb : mem), rt_pres_fp live frs (bv_unsigned sp + -96) W ma mb ->
            (forall x, bv_unsigned sp - 96 <= x -> outside W x) -> agree_on above ma mb).
  { intros live frs W ma mb pres outw. apply (agree_of_pres_fp _ _ _ _ _ _ _ pres). intros x xr. unfold above in xr.
    split; [apply acl_stack; lia | apply outw; lia]. }
  assert (above_munch : forall W (ma mb : mem), munch W ma mb -> (forall x, bv_unsigned sp - 96 <= x -> outside W x) -> agree_on above ma mb).
  { intros W ma mb mu outw. apply (agree_of_munch _ _ _ _ mu). intros x xr. unfold above in xr. apply outw. lia. }
  assert (keep_pres : forall live W (ma mb : mem), rt_pres_fp live (rt_frames RT S0) (bv_unsigned sp + -96) W ma mb ->
            (forall e, In e (rt_live RT S0) -> In e live) -> (forall x, keep0 x -> outside W x) -> agree_on keep0 ma mb).
  { intros live W ma mb pres grows outw. apply (agree_of_pres_fp _ _ _ _ _ _ _ pres). intros x kx.
    split; [exact (proj1 (keep0_lift live grows x kx)) | exact (outw x kx)]. }
  assert (cf_at : forall mi, agree_on keep0 m mi -> wmono asegs m mi -> rw_cells asegs mi conf (ht_conf ctx) /\ acc asegs mi conf 48).
  { intros mi ag wm. split.
    - apply (rw_cells_agree asegs m mi _ _ cf_cells); [| exact wm]. exact (agree_sub _ _ _ _ ag cf_kept).
    - apply (acc_agree m mi conf 48 cf_acc); [lia |]. exact (agree_sub _ _ _ _ ag cfsh_kept). }
  assert (art_walk : forall Si (ma mb : mem) p n a b, ART RT Si ma -> rt_sp0 RT Si = rt_sp0 RT S0 -> In (p, n) (rt_live RT Si) ->
            p <= a -> b <= p + n -> munch [(a, b)] ma mb -> wmono asegs ma mb -> ART RT Si mb).
  { intros Si ma mb p n a b art same inl pa bp mu wm. apply (af_frame RT AF Si ma mb (bv_unsigned sp) art); [rewrite same; lia | | exact wm].
    intros w far. apply mu. cbn [outside]. split; [| exact I]. intros win. apply far. apply (acl_live _ _ _ p n); [exact inl | lia]. }
  assert (env_walk : forall a b (ma mb : mem) lb', cl_env ma lb' canary -> munch [(a, b)] ma mb -> ssp_guard + 8 <= a -> cl_env mb lb' canary).
  { intros a b ma mb lb' env mu far. apply (cl_env_seg _ ma mb lb' canary env mu). apply cl_fp_cons; [right; left; exact far | exact cl_fp_nil]. }
  assert (mcz : mcost 96 = 0 /\ mcost 24 = 0 /\ mcost NB_BYTES = 0 /\ mcost 264 = 0 /\ mcost 16 = 0) by (repeat split; reflexivity).
  destruct mcz as (mc96 & mc24 & mcnb & mc264 & mc16).
  assert (cost3 : HT_COST = 3) by (unfold HT_COST; rewrite mc96, mc24, mcnb, mc264, mc16; reflexivity).
  rewrite cost3 in cred_e.
  assert (room_c : forall need, need <= 560 -> lo + RT_STACK + need <= bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96))).
  { intros need small. rewrite csp_u. unfold RT_STACK in *. lia. }
  (* the table header: CRYPTO_zalloc(96) *)
  destruct (link_at m_f SITE_ht_zalloc1 e_CRYPTO_zalloc (fun _ _ => eq_refl) (wmono_refl asegs m_f)
              ltac:(unfold HT_SITES; left; reflexivity) ltac:(unfold HT_CALLS; left; reflexivity)
              ltac:(unfold SITE_ht_zalloc1; lia)) as (cgx_1 & chain_1).
  assert (cok_f : call_ok RT S0 m_f (Z_to_bv 64 (bv_unsigned sp + -96)) lo).
  { unfold call_ok. rewrite csp_u. split; [exact stk_f |]. unfold RT_STACK, USTACK_TOP in *. repeat split; lia. }
  assert (cz_cg0 : cg_has (rt_cg RT S0) [(SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)]
                     [(SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)])
    by (apply (cg_has_weaken _ _ _ _ _ cgh_e); vm_compute; reflexivity).
  assert (cr_1 : mcost 96 <= rt_credit RT S0) by (rewrite mc96; lia).
  refine (C_CZ S0 PM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m_f 96 lo (bv_unsigned ra :: outer) lb canary
            pm_fds pm_stable eq_refl eq_refl ltac:(lia) art_f inv_f cok_f (room_c 256 ltac:(lia))
            cgx_1 chain_1 cz_cg0 ltac:(lia) cr_1 env_f T k_f at_f' _).
  intros k_h got_h.
  destruct got_h as (S1 & h & at_h & live_h & frs_h & sp0_h & cred_h & h_pos & h_al & h_top & cg_h).
  destruct (ASTA_unpack RT S1 PM _ k_h at_h) as (ms_h & (m_h & ret_h & aft_h & pres_h & env_h & wr_h & _ & zero_h) & at_h'). clear at_h.
  destruct ret_h as (t0b & t1b & t2b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & Fb & fcb & ->).
  destruct aft_h as (art_h & inv_h & wm_h & stk_h).
  rewrite (ret_pc_even SITE_ht_zalloc1) in at_h' by (unfold SITE_ht_zalloc1; lia).
  rewrite csp_u in stk_h, pres_h.
  assert (h_in : In (h, 96) (rt_live RT S1)) by (rewrite live_h; left; reflexivity).
  pose proof (afp_live_hi RT GOBJ AFP S1 m_h h 96 art_h h_in ltac:(lia)) as h_hi.
  pose proof (af_live_range RT AF S1 m_h h 96 art_h h_in) as (_ & h_win & _).
  rewrite sp0_h in h_win.
  assert (h_lo : h + 96 <= lo) by (unfold STACK_WIN in *; lia).
  assert (cf_h : apart fcf (fs_size kcf) h 96).
  { unfold apart. apply (proj2 (proj2 (proj2 (af_frames_range RT AF S1 m_h fcf kcf art_h ltac:(rewrite frs_h; exact cf_in))))). exact h_in. }
  assert (h_fresh : forall x, keep0 x -> ~ (h <= x < h + 96)).
  { intros x kx. exact (wg_newchunk_apart RT AF S0 S1 m_h [(h, 96)] h 96 (bv_unsigned sp) x art_h live_h (or_introl eq_refl) frs_h sp0_h
                          ltac:(lia) ltac:(lia) (proj1 kx)). }
  assert (ag_h : agree_on keep0 m m_h).
  { apply (agree_trans _ m m_f m_h ag_f). apply (keep_pres _ _ m_f m_h pres_h); [tauto | exact (fun x kx => proj2 kx)]. }
  assert (up_h : agree_on above m_f m_h).
  { apply (above_pres _ _ _ m_f m_h pres_h). intros x far. cbn [outside]. unfold G_ALLOW_CUST. split; [lia | exact I]. }
  assert (mono_h : wmono asegs m m_h) by exact (wmono_trans _ _ _ _ wm_f wm_h).
  destruct (cf_at m_h ag_h mono_h) as (cfc_h & cfa_h).
  assert (h_al8 : h mod 8 = 0) by (apply wg_mod16_8; exact h_al).
  (* reads of the config, no store, up to the lock allocation *)
  pose proof (ht_w1 sp gp (Z_to_bv 64 TP_A) t0b t1b t2b a1b a2b a3b a4b a5b a6b a7b s1 s2 s3 s5 s7 s8 s9 s10 s11 t3b t4b t5b t6b Fb fcb m_h h conf ctx
                h_pos ltac:(unfold USTACK_TOP in *; lia) h_al8 ltac:(lia) ltac:(lia) cf_al8 cfc_h cfa_h inv_h) as walk.
  cl_lift walk at_h' k_g at_g.
  destruct (ASTA_unpack RT S1 PM _ k_g at_g) as (ms_g & -> & at_g'). clear at_g.
  (* the table lock: CRYPTO_THREAD_lock_new() *)
  destruct (link_at m_h SITE_ht_locknew e_lock_new up_h wm_h
              ltac:(unfold HT_SITES; right; left; reflexivity) ltac:(unfold HT_CALLS; right; left; reflexivity)
              ltac:(unfold SITE_ht_locknew; lia)) as (cgx_2 & chain_2).
  rewrite <- cg_h in cgx_2.
  assert (cok_h : call_ok RT S1 m_h (Z_to_bv 64 (bv_unsigned sp + -96)) lo).
  { unfold call_ok. rewrite csp_u, sp0_h. split; [exact stk_h |]. unfold RT_STACK, USTACK_TOP in *. repeat split; lia. }
  assert (ln_cg1 : cg_has (rt_cg RT S1) [(SITE_ln_zalloc, e_lock_new); (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)]
                     [(SITE_ln_zalloc, e_CRYPTO_zalloc); (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)])
    by (rewrite cg_h; apply (cg_has_weaken _ _ _ _ _ cgh_e); vm_compute; reflexivity).
  refine (C_LN S1 PM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m_h lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary
            pm_fds pm_stable eq_refl art_h inv_h cok_h (room_c 512 ltac:(lia)) cgx_2 chain_2 ln_cg1
            ltac:(rewrite frs_h; exact nfr_e) ltac:(rewrite live_h; cbn [length]; lia) ltac:(rewrite cred_h, mc96; lia) env_h T k_g at_g' _).
  intros k_l got_l.
  destruct got_l as (S2 & lk & at_l & live_l & frs_l & sp0_l & cred_l & lk_pos & lk_al & lk_top & cg_l).
  destruct (ASTA_unpack RT S2 PM _ k_l at_l) as (ms_l & (m_l & ret_l & aft_l & pres_l & env_l & lk_cells & lk_acc) & at_l'). clear at_l.
  destruct ret_l as (t0c & t1c & t2c & a1c & a2c & a3c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & Fc & fcc & ->).
  destruct aft_l as (art_l & inv_l & wm_l & stk_l).
  rewrite (ret_pc_even SITE_ht_locknew) in at_l' by (unfold SITE_ht_locknew; lia).
  rewrite csp_u in stk_l, pres_l.
  rewrite live_h in live_l. rewrite frs_h in frs_l, pres_l. rewrite sp0_h in sp0_l. rewrite cg_h in cg_l. rewrite cred_h in cred_l.
  assert (lk_in : In (lk, 40) (rt_live RT S2)) by (rewrite live_l; left; reflexivity).
  assert (h_in2 : In (h, 96) (rt_live RT S2)) by (rewrite live_l; right; left; reflexivity).
  pose proof (af_live_range RT AF S2 m_l lk 40 art_l lk_in) as (_ & lk_win & _).
  rewrite sp0_l in lk_win.
  assert (lk_lo : lk + 40 <= lo) by (unfold STACK_WIN in *; lia).
  pose proof (afp_live_hi RT GOBJ AFP S2 m_l lk 40 art_l lk_in ltac:(lia)) as lk_hi.
  assert (lk_h : apart lk 40 h 96).
  { unfold apart. apply (wg_live_apart RT AF S2 m_l [] lk 40 (rt_live RT S1) h 96 art_l); [rewrite live_l, live_h; reflexivity | rewrite live_h; left; reflexivity]. }
  assert (ag_l : agree_on keep0 m m_l).
  { apply (agree_trans _ m m_h m_l ag_h). apply (keep_pres _ _ m_h m_l pres_l); [rewrite live_h; intros e ein; right; exact ein | exact (fun x kx => proj2 kx)]. }
  assert (up_l : agree_on above m_f m_l).
  { apply (agree_trans _ m_f m_h m_l up_h). apply (above_pres _ _ _ m_h m_l pres_l). intros x far. cbn [outside]. unfold G_ALLOW_CUST. split; [lia | exact I]. }
  (* the zeroed header, as the walk wants it *)
  pose proof (rw_CB_of_bytes m_h h _ zero_h wr_h) as h_zero.
  assert (h_tab0 : rw_cells asegs m_h h ht_tab0).
  { apply (rw_cells_recast m_h h _ _ h_zero); [cbn; repeat split | reflexivity]. }
  assert (h_tab0' : rw_cells asegs m_l h ht_tab0).
  { apply (wg_keep_live _ _ _ _ m_h m_l h 96 h ht_tab0 h_tab0 pres_l wm_l); [rewrite live_h; left; reflexivity | lia | cbn; lia |].
    intros x xr. cbn [outside]. unfold G_ALLOW_CUST. split; [lia | exact I]. }
  pose proof (af_acc_live RT AF S2 m_l h 96 art_l h_in2) as (_ & h_acc_l).
  (* storing the lock pointer, up to the copy of the config *)
  pose proof (ht_w2 sp gp (Z_to_bv 64 TP_A) t0c t1c t2c a1c a2c a3c a4c a5c a6c a7c s5 s8 s9 s10 s11 t3c t4c t5c t6c Fc fcc m_l h conf lk
                h_hi ltac:(unfold USTACK_TOP in *; lia) h_al8 lk_pos ltac:(unfold USTACK_TOP in *; lia) ltac:(lia) ltac:(lia)
                h_tab0' h_acc_l inv_l) as walk.
  cl_lift walk at_l' k_p at_p.
  destruct (ASTA_unpack RT S2 PM _ k_p at_p) as (ms_p & (m_p & -> & mu_p & wm_p & inv_p & h_cells_p) & at_p'). clear at_p.
  assert (art_p : ART RT S2 m_p) by exact (art_walk S2 m_l m_p h 96 (h + 56) (h + 64) art_l sp0_l h_in2 ltac:(lia) ltac:(lia) mu_p wm_p).
  assert (ag_p : agree_on keep0 m m_p).
  { apply (agree_trans _ m m_l m_p ag_l). apply (agree_of_munch _ _ _ _ mu_p). intros x kx. cbn [outside]. split; [| exact I].
    pose proof (h_fresh x kx). lia. }
  assert (up_p : agree_on above m_f m_p).
  { apply (agree_trans _ m_f m_l m_p up_l). apply (above_munch _ _ _ mu_p). intros x far. cbn [outside]. split; [lia | exact I]. }
  assert (stk_p : stk asegs m_p lo (bv_unsigned sp + -96)).
  { apply (stk_munch _ m_l m_p _ _ stk_l mu_p wm_p). intros x xr. cbn [outside]. split; [lia | exact I]. }
  assert (env_p : cl_env m_p (Z_to_bv 8 1) canary) by exact (env_walk _ _ m_l m_p _ env_l mu_p ltac:(unfold ssp_guard; lia)).
  assert (mono_p : wmono asegs m m_p) by exact (wmono_trans _ _ _ _ (wmono_trans _ _ _ _ mono_h wm_l) wm_p).
  destruct (cf_at m_p ag_p mono_p) as (cfc_p & cfa_p).
  (* the config copy: __asan_memcpy(ht, conf, 48) *)
  assert (cfb_len : Z.of_nat (length (cells_bytes (ht_conf ctx))) = 48).
  { rewrite cells_bytes_length by (cbn; repeat split). reflexivity. }
  assert (a2_48 : Z_to_bv 64 48 = Z_to_bv 64 (Z.of_nat (length (cells_bytes (ht_conf ctx))))) by (rewrite cfb_len; reflexivity).
  assert (src_ok : checked_src RT S2 m_p (Z_to_bv 64 (bv_unsigned sp + -96)) lo conf (Z.of_nat (length (cells_bytes (ht_conf ctx))))).
  { rewrite cfb_len. split.
    - intros _. split; [exact cfa_p |]. right; left. exists fcf, kcf. split; [rewrite frs_l; exact cf_in | lia].
    - left. lia. }
  assert (dst_ok : checked_dst RT S2 m_p (Z_to_bv 64 (bv_unsigned sp + -96)) h (Z.of_nat (length (cells_bytes (ht_conf ctx))))).
  { rewrite cfb_len. exact (Fz_mkit.live_checked_dst RT AF S2 m_p _ h 96 h 48 art_p h_in2 ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (cok_p : call_ok RT S2 m_p (Z_to_bv 64 (bv_unsigned sp + -96)) lo).
  { unfold call_ok. rewrite csp_u, sp0_l. split; [exact stk_p |]. unfold RT_STACK, USTACK_TOP in *. repeat split; lia. }
  refine (MCP S2 PM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m_p h conf (cells_bytes (ht_conf ctx)) lo
            pm_fds pm_stable eq_refl eq_refl a2_48 ltac:(lia) ltac:(lia) ltac:(rewrite cfb_len; lia)
            (rw_cells_bytes_at asegs m_p conf (ht_conf ctx) cfc_p) src_ok dst_ok ltac:(rewrite cfb_len; unfold apart in cf_h; lia) art_p inv_p cok_p T k_p at_p' _).
  intros k_y got_y. unfold icpt_post in got_y.
  destruct (ASTA_unpack RT S2 PM _ k_y got_y) as (ms_y & (m_y & ret_y & aft_y & pres_y & copied_y) & at_y'). clear got_y.
  destruct ret_y as (t0d & t1d & t2d & a1d & a2d & a3d & a4d & a5d & a6d & a7d & t3d & t4d & t5d & t6d & Fd & fcd & ->).
  destruct aft_y as (art_y & inv_y & wm_y & stk_y).
  rewrite (ret_pc_even SITE_ht_memcpy) in at_y' by (unfold SITE_ht_memcpy; lia).
  rewrite csp_u in stk_y, pres_y. rewrite cfb_len in pres_y.
  assert (ag_y : agree_on keep0 m m_y).
  { apply (agree_trans _ m m_p m_y ag_p). apply (agree_of_pres_ex _ _ _ _ _ _ _ _ pres_y). intros x kx.
    split; [| pose proof (h_fresh x kx); lia]. rewrite frs_l.
    exact (proj1 (keep0_lift (rt_live RT S2) ltac:(rewrite live_l; intros e ein; right; right; exact ein) x kx)). }
  assert (up_y : agree_on above m_f m_y).
  { apply (agree_trans _ m_f m_p m_y up_p). apply (agree_of_pres_ex _ _ _ _ _ _ _ _ pres_y). intros x xr. unfold above in xr.
    split; [apply acl_stack; lia | lia]. }
  assert (env_y : cl_env m_y (Z_to_bv 8 1) canary).
  { apply (cl_env_pres_ex _ _ _ _ _ m_p m_y _ _ env_p pres_y). intros x cx.
    pose proof (client_static_range x (cl_cell_static x cx)) as xr. unfold SEGTOP_A in xr. lia. }
  (* the header now starts with the config *)
  pose proof (rw_cells_tail m_p h _ _ h_cells_p) as h_rest_p. cbn [csize] in h_rest_p.
  assert (h_rest_y : rw_cells asegs m_y (h + 48) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 lk); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 (repeat (Z_to_bv 8 0) 16)]).
  { apply (rw_cells_agree asegs m_p m_y _ _ h_rest_p); [| exact wm_y].
    apply (agree_of_pres_ex _ _ _ _ _ _ _ _ pres_y). intros x xr. cbn [cells_size csize Nat.add] in xr.
    split; [apply (acl_live _ _ _ h 96); [exact h_in2 | lia] | lia]. }
  assert (h_wr48 : wr_at asegs m_y h 48).
  { apply (wr_at_wm m_p m_y h 48); [| exact wm_y]. apply (wr_at_sub m_p h 96 h 48); [exact (proj2 h_cells_p) | lia | lia | lia]. }
  pose proof (rw_CB_of_bytes m_y h _ copied_y ltac:(rewrite cfb_len; exact h_wr48)) as h_cfg_y.
  assert (h_conf_y : rw_cells asegs m_y h (ht_conf ctx)).
  { apply (rw_cells_recast m_y h _ _ h_cfg_y); [cbn; repeat split | exact (eq_sym (app_nil_r _))]. }
  assert (h_tab1 : rw_cells asegs m_y h (ht_tab1 ctx lk)).
  { change (ht_tab1 ctx lk) with (ht_conf ctx ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 lk); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 (repeat (Z_to_bv 8 0) 16)]).
    apply (proj2 (rw_cells_app m_y h _ _)). split; [exact h_conf_y | exact h_rest_y]. }
  pose proof (af_acc_live RT AF S2 m_y h 96 art_y h_in2) as (_ & h_acc_y).
  (* stores the default free callback at h+8 and 512 at h+72, up to the second allocation *)
  pose proof (ht_w3 sp gp (Z_to_bv 64 TP_A) t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d s5 s8 s9 s10 s11 t3d t4d t5d t6d Fd fcd m_y h conf lk ctx
                h_hi ltac:(unfold USTACK_TOP in *; lia) h_al8 ltac:(lia) ltac:(lia) h_tab1 h_acc_y inv_y) as walk.
  cl_lift walk at_y' k_r at_r.
  destruct (ASTA_unpack RT S2 PM _ k_r at_r) as (ms_r & (m_r & -> & mu_r & wm_r & inv_r & h_tab2) & at_r'). clear at_r.
  assert (art_r : ART RT S2 m_r) by exact (art_walk S2 m_y m_r h 96 h (h + 96) art_y sp0_l h_in2 ltac:(lia) ltac:(lia) mu_r wm_r).
  assert (ag_r : agree_on keep0 m m_r).
  { apply (agree_trans _ m m_y m_r ag_y). apply (agree_of_munch _ _ _ _ mu_r). intros x kx. cbn [outside]. split; [| exact I].
    pose proof (h_fresh x kx). lia. }
  assert (up_r : agree_on above m_f m_r).
  { apply (agree_trans _ m_f m_y m_r up_y). apply (above_munch _ _ _ mu_r). intros x far. cbn [outside]. split; [lia | exact I]. }
  assert (stk_r : stk asegs m_r lo (bv_unsigned sp + -96)).
  { apply (stk_munch _ m_y m_r _ _ stk_y mu_r wm_r). intros x xr. cbn [outside]. split; [lia | exact I]. }
  assert (env_r : cl_env m_r (Z_to_bv 8 1) canary) by exact (env_walk _ _ m_y m_r _ env_y mu_r ltac:(unfold ssp_guard; lia)).
  assert (wf_r : wmono asegs m_f m_r) by exact (wmono_trans _ _ _ _ (wmono_trans _ _ _ _ (wmono_trans _ _ _ _ (wmono_trans _ _ _ _ wm_h wm_l) wm_p) wm_y) wm_r).
  (* the mutable part: CRYPTO_zalloc(24) *)
  destruct (link_at m_r SITE_ht_zalloc2 e_CRYPTO_zalloc up_r wf_r
              ltac:(unfold HT_SITES; right; right; left; reflexivity) ltac:(unfold HT_CALLS; right; right; left; reflexivity)
              ltac:(unfold SITE_ht_zalloc2; lia)) as (cgx_3 & chain_3).
  rewrite <- cg_l in cgx_3.
  assert (cok_r : call_ok RT S2 m_r (Z_to_bv 64 (bv_unsigned sp + -96)) lo).
  { unfold call_ok. rewrite csp_u, sp0_l. split; [exact stk_r |]. unfold RT_STACK, USTACK_TOP in *. repeat split; lia. }
  assert (cz_cg2 : cg_has (rt_cg RT S2) [(SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)]
                     [(SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)]) by (rewrite cg_l; exact cz_cg0).
  refine (C_CZ S2 PM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m_r 24 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary
            pm_fds pm_stable eq_refl eq_refl ltac:(lia) art_r inv_r cok_r (room_c 256 ltac:(lia))
            cgx_3 chain_3 cz_cg2 ltac:(rewrite live_l; cbn [length]; lia) ltac:(rewrite cred_l, mc24, mc96; lia) env_r T k_r at_r' _).
  intros k_z got_z.
  destruct got_z as (S3 & md & at_z & live_z & frs_z & sp0_z & cred_z & md_pos & md_al & md_top & cg_z).
  destruct (ASTA_unpack RT S3 PM _ k_z at_z) as (ms_z & (m_z & ret_z & aft_z & pres_z & env_z & wr_md & _ & zero_md) & at_z'). clear at_z.
  destruct ret_z as (t0e & t1e & t2e & a1e & a2e & a3e & a4e & a5e & a6e & a7e & t3e & t4e & t5e & t6e & Fe & fce & ->).
  destruct aft_z as (art_z & inv_z & wm_z & stk_z).
  rewrite (ret_pc_even SITE_ht_zalloc2) in at_z' by (unfold SITE_ht_zalloc2; lia).
  rewrite csp_u in stk_z, pres_z.
  rewrite live_l in live_z. rewrite frs_l in frs_z, pres_z. rewrite sp0_l in sp0_z. rewrite cg_l in cg_z. rewrite cred_l in cred_z.
  assert (md_in : In (md, 24) (rt_live RT S3)) by (rewrite live_z; left; reflexivity).
  assert (h_in3 : In (h, 96) (rt_live RT S3)) by (rewrite live_z; right; right; left; reflexivity).
  assert (lk_in3 : In (lk, 40) (rt_live RT S3)) by (rewrite live_z; right; left; reflexivity).
  pose proof (afp_live_hi RT GOBJ AFP S3 m_z md 24 art_z md_in ltac:(lia)) as md_hi.
  pose proof (af_live_range RT AF S3 m_z md 24 art_z md_in) as (_ & md_win & _).
  rewrite sp0_z in md_win.
  assert (md_lo : md + 24 <= lo) by (unfold STACK_WIN in *; lia).
  assert (md_h : apart md 24 h 96).
  { unfold apart. apply (wg_live_apart RT AF S3 m_z [] md 24 ((lk, 40) :: (h, 96) :: rt_live RT S0) h 96 art_z);
      [rewrite live_z; reflexivity | right; left; reflexivity]. }
  assert (md_lk : apart md 24 lk 40).
  { unfold apart. apply (wg_live_apart RT AF S3 m_z [] md 24 ((lk, 40) :: (h, 96) :: rt_live RT S0) lk 40 art_z);
      [rewrite live_z; reflexivity | left; reflexivity]. }
  assert (cf_md : apart fcf (fs_size kcf) md 24).
  { unfold apart. apply (proj2 (proj2 (proj2 (af_frames_range RT AF S3 m_z fcf kcf art_z ltac:(rewrite frs_z; exact cf_in))))). exact md_in. }
  assert (md_fresh : forall x, keep0 x -> ~ (md <= x < md + 24)).
  { intros x kx. exact (wg_newchunk_apart RT AF S0 S3 m_z [(md, 24); (lk, 40); (h, 96)] md 24 (bv_unsigned sp) x art_z live_z (or_introl eq_refl) frs_z sp0_z
                          ltac:(lia) ltac:(lia) (proj1 kx)). }
  assert (ag_z : agree_on keep0 m m_z).
  { apply (agree_trans _ m m_r m_z ag_r). apply (keep_pres _ _ m_r m_z pres_z); [rewrite live_l; intros e ein; right; right; exact ein | exact (fun x kx => proj2 kx)]. }
  assert (up_z : agree_on above m_f m_z).
  { apply (agree_trans _ m_f m_r m_z up_r). apply (above_pres _ _ _ m_r m_z pres_z). intros x far. cbn [outside]. unfold G_ALLOW_CUST. split; [lia | exact I]. }
  assert (h_tab2' : rw_cells asegs m_z h (ht_tab2 ctx lk)).
  { apply (wg_keep_live _ _ _ _ m_r m_z h 96 h _ h_tab2 pres_z wm_z); [rewrite live_l; right; left; reflexivity | lia | cbn; lia |].
    intros x xr. cbn [outside]. unfold G_ALLOW_CUST. split; [lia | exact I]. }
  pose proof (af_acc_live RT AF S3 m_z h 96 art_z h_in3) as (_ & h_acc_z).
  assert (md_al8 : md mod 8 = 0) by (apply wg_mod16_8; exact md_al).
  (* storing the mutable part, up to the bucket allocation *)
  pose proof (ht_w4 sp gp (Z_to_bv 64 TP_A) t0e t1e t2e a1e a2e a3e a4e a5e a6e a7e s9 s10 s11 t3e t4e t5e t6e Fe fce m_z h conf lk md ctx
                h_hi ltac:(unfold USTACK_TOP in *; lia) h_al8 ltac:(lia) ltac:(lia) md_pos ltac:(unfold USTACK_TOP in *; lia) md_al8
                h_tab2' h_acc_z inv_z) as walk.
  cl_lift walk at_z' k_n at_n.
  destruct (ASTA_unpack RT S3 PM _ k_n at_n) as (ms_n & (m_n & -> & mu_n & wm_n & inv_n & h_tab3) & at_n'). clear at_n.
  assert (art_n : ART RT S3 m_n) by exact (art_walk S3 m_z m_n h 96 (h + 64) (h + 72) art_z sp0_z h_in3 ltac:(lia) ltac:(lia) mu_n wm_n).
  assert (ag_n : agree_on keep0 m m_n).
  { apply (agree_trans _ m m_z m_n ag_z). apply (agree_of_munch _ _ _ _ mu_n). intros x kx. cbn [outside]. split; [| exact I].
    pose proof (h_fresh x kx). lia. }
  assert (up_n : agree_on above m_f m_n).
  { apply (agree_trans _ m_f m_z m_n up_z). apply (above_munch _ _ _ mu_n). intros x far. cbn [outside]. split; [lia | exact I]. }
  assert (stk_n : stk asegs m_n lo (bv_unsigned sp + -96)).
  { apply (stk_munch _ m_z m_n _ _ stk_z mu_n wm_n). intros x xr. cbn [outside]. split; [lia | exact I]. }
  assert (env_n : cl_env m_n (Z_to_bv 8 1) canary) by exact (env_walk _ _ m_z m_n _ env_z mu_n ltac:(unfold ssp_guard; lia)).
  assert (wf_n : wmono asegs m_f m_n) by exact (wmono_trans _ _ _ _ (wmono_trans _ _ _ _ wf_r wm_z) wm_n).
  (* the zeroed mutable part, cell by cell *)
  assert (md_zero : rw_cells asegs m_z md [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_recast m_z md _ _ (rw_CB_of_bytes m_z md _ zero_md wr_md)); [cbn; repeat split | reflexivity]. }
  destruct (proj1 (rw_cells_app m_z md [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] [C8 (Z_to_bv 64 0)]) md_zero) as (md01_z & md2_z').
  assert (md2_z : rw_cells asegs m_z (md + 16) [C8 (Z_to_bv 64 0)]) by exact md2_z'. clear md2_z'.
  pose proof (rw_cells_head m_z md _ _ md01_z) as md0_z. clear md01_z.
  assert (md0_n : rw_cells asegs m_n md [C8 (Z_to_bv 64 0)]).
  { apply (wg_keep_seg _ m_z m_n _ _ md0_z mu_n wm_n). intros x xr. cbn [cells_size csize Nat.add] in xr. cbn [outside].
    unfold apart in md_h. split; [lia | exact I]. }
  assert (md2_n : rw_cells asegs m_n (md + 16) [C8 (Z_to_bv 64 0)]).
  { apply (wg_keep_seg _ m_z m_n _ _ md2_z mu_n wm_n). intros x xr. cbn [cells_size csize Nat.add] in xr. cbn [outside].
    unfold apart in md_h. split; [lia | exact I]. }
  (* the bucket array: alloc_new_neighborhood_list(512, &md->neighborhood_ptr_to_free) *)
  destruct (link_at m_n SITE_ht_anl e_anl up_n wf_n
              ltac:(unfold HT_SITES; right; right; right; left; reflexivity) ltac:(unfold HT_CALLS; right; right; right; left; reflexivity)
              ltac:(unfold SITE_ht_anl; lia)) as (cgx_4 & chain_4).
  rewrite <- cg_z in cgx_4.
  change e_anl with Fz_I2_anl.e_anl in cgx_4.
  assert (cok_n : call_ok RT S3 m_n (Z_to_bv 64 (bv_unsigned sp + -96)) lo).
  { unfold call_ok. rewrite csp_u, sp0_z. split; [exact stk_n |]. unfold RT_STACK, USTACK_TOP in *. repeat split; lia. }
  assert (anl_cg3 : cg_has (rt_cg RT S3) ANL_SITES ANL_CALLS) by (rewrite cg_z; apply (cg_has_weaken _ _ _ _ _ cgh_e); vm_compute; reflexivity).
  refine (C_ANL S3 PM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m_n lo (bv_unsigned ra :: outer) (md + 8) md 24 (Z_to_bv 8 1) canary
            pm_fds pm_stable eq_refl eq_refl eq_refl memalign_plain_nb md_in ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
            art_n inv_n cok_n (room_c 560 ltac:(lia)) cgx_4 chain_4 anl_cg3
            ltac:(rewrite frs_z; exact nfr_e) ltac:(rewrite live_z; cbn [length]; lia) ltac:(rewrite cred_z, mcnb, mc24, mc96; lia) env_n T k_n at_n' _).
  intros k_b got_b.
  destruct got_b as (S4 & nb & at_b & live_b & frs_b & sp0_b & cred_b & nb_pos & nb_al & nb_top & cg_b).
  destruct (ASTA_unpack RT S4 PM _ k_b at_b) as (ms_b & (m_b & ret_b & aft_b & pres_b & env_b & wr_nb & _ & md1_b & zero_nb) & at_b'). clear at_b.
  destruct ret_b as (t0f & t1f & t2f & a1f & a2f & a3f & a4f & a5f & a6f & a7f & t3f & t4f & t5f & t6f & Ff & fcn & ->).
  destruct aft_b as (art_b & inv_b & wm_b & stk_b).
  rewrite (ret_pc_even SITE_ht_anl) in at_b' by (unfold SITE_ht_anl; lia).
  rewrite csp_u in stk_b, pres_b.
  rewrite live_z in live_b. rewrite frs_z in frs_b, pres_b. rewrite sp0_z in sp0_b. rewrite cg_z in cg_b. rewrite cred_z in cred_b.
  assert (nb_in : In (nb, NB_BYTES) (rt_live RT S4)) by (rewrite live_b; left; reflexivity).
  assert (md_in4 : In (md, 24) (rt_live RT S4)) by (rewrite live_b; right; left; reflexivity).
  assert (h_in4 : In (h, 96) (rt_live RT S4)) by (rewrite live_b; right; right; right; left; reflexivity).
  pose proof (af_live_range RT AF S4 m_b nb NB_BYTES art_b nb_in) as (_ & nb_win & _).
  rewrite sp0_b in nb_win.
  assert (nb_lo : nb + NB_BYTES <= lo) by (unfold STACK_WIN in *; lia).
  pose proof (afp_live_hi RT GOBJ AFP S4 m_b nb NB_BYTES art_b nb_in ltac:(unfold NB_BYTES; lia)) as nb_hi.
  assert (nb_apart : forall p n, In (p, n) ((md, 24) :: (lk, 40) :: (h, 96) :: rt_live RT S0) -> nb + NB_BYTES <= p \/ p + n <= nb).
  { intros p n pin. apply (wg_live_apart RT AF S4 m_b [] nb NB_BYTES ((md, 24) :: (lk, 40) :: (h, 96) :: rt_live RT S0) p n art_b); [rewrite live_b; reflexivity | exact pin]. }
  assert (nb_md : apart nb NB_BYTES md 24) by (unfold apart; apply nb_apart; left; reflexivity).
  assert (nb_lk : apart nb NB_BYTES lk 40) by (unfold apart; apply nb_apart; right; left; reflexivity).
  assert (nb_h : apart nb NB_BYTES h 96) by (unfold apart; apply nb_apart; right; right; left; reflexivity).
  assert (ag_b : agree_on keep0 m m_b).
  { apply (agree_trans _ m m_n m_b ag_n). apply (keep_pres _ _ m_n m_b pres_b); [rewrite live_z; intros e ein; right; right; right; exact ein |].
    intros x kx. cbn [outside]. split; [| exact I]. pose proof (md_fresh x kx). lia. }
  assert (up_b : agree_on above m_f m_b).
  { apply (agree_trans _ m_f m_n m_b up_n). apply (above_pres _ _ _ m_n m_b pres_b). intros x far. cbn [outside]. split; [lia | exact I]. }
  assert (wf_b : wmono asegs m_f m_b) by exact (wmono_trans _ _ _ _ wf_n wm_b).
  (* header, mutable part and config at the bucket return *)
  assert (h_tab3_b : rw_cells asegs m_b h (ht_tab3 ctx lk md)).
  { apply (wg_keep_live _ _ _ _ m_n m_b h 96 h _ h_tab3 pres_b wm_b); [exact h_in3 | lia | cbn; lia |].
    intros x xr. cbn [cells_size csize Nat.add ht_tab3] in xr. cbn [outside]. unfold apart in md_h. split; [lia | exact I]. }
  assert (md0_b : rw_cells asegs m_b md [C8 (Z_to_bv 64 0)]).
  { apply (wg_keep_live _ _ _ _ m_n m_b md 24 md _ md0_n pres_b wm_b); [exact md_in | lia | cbn; lia |].
    intros x xr. cbn [cells_size csize Nat.add] in xr. cbn [outside]. split; [lia | exact I]. }
  assert (md2_b : rw_cells asegs m_b (md + 16) [C8 (Z_to_bv 64 0)]).
  { apply (wg_keep_live _ _ _ _ m_n m_b md 24 (md + 16) _ md2_n pres_b wm_b); [exact md_in | lia | cbn; lia |].
    intros x xr. cbn [cells_size csize Nat.add] in xr. cbn [outside]. split; [lia | exact I]. }
  assert (md_cells_b : rw_cells asegs m_b md [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 0)]).
  { apply (proj2 (rw_cells_app m_b md [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 nb)] [C8 (Z_to_bv 64 0)])).
    split; [apply rw_cells_join2; [exact md0_b | exact md1_b] | exact md2_b]. }
  pose proof (af_acc_live RT AF S4 m_b h 96 art_b h_in4) as (_ & h_acc_b).
  pose proof (af_acc_live RT AF S4 m_b md 24 art_b md_in4) as (_ & md_acc_b).
  destruct (cf_at m_b ag_b (wmono_trans _ _ _ _ wm_f wf_b)) as (cfc_b & cfa_b).
  (* bucket pointers and mask, up to the rcu lock *)
  pose proof (ht_w5 sp gp (Z_to_bv 64 TP_A) t0f t1f t2f a1f a2f a3f a4f a5f a6f a7f s10 s11 t3f t4f t5f t6f Ff fcn m_b h conf lk md nb ctx
                h_hi ltac:(unfold USTACK_TOP in *; lia) h_al8 ltac:(lia) ltac:(lia) cf_al8 md_hi ltac:(unfold USTACK_TOP in *; lia) md_al8
                nb_pos ltac:(unfold USTACK_TOP, NB_BYTES in *; lia) ltac:(unfold apart in md_h; lia) ltac:(unfold apart in cf_h; lia)
                ltac:(unfold apart in cf_md; lia)
                h_tab3_b h_acc_b md_cells_b md_acc_b cfc_b cfa_b inv_b) as walk.
  cl_lift walk at_b' k_d at_d.
  destruct (ASTA_unpack RT S4 PM _ k_d at_d) as (ms_d & (a2g & m_d & -> & mu_d & wm_d & inv_d & md_cells_d) & at_d'). clear at_d.
  assert (art_d : ART RT S4 m_d) by exact (art_walk S4 m_b m_d md 24 md (md + 24) art_b sp0_b md_in4 ltac:(lia) ltac:(lia) mu_d wm_d).
  assert (ag_d : agree_on keep0 m m_d).
  { apply (agree_trans _ m m_b m_d ag_b). apply (agree_of_munch _ _ _ _ mu_d). intros x kx. cbn [outside]. split; [| exact I].
    pose proof (md_fresh x kx). lia. }
  assert (up_d : agree_on above m_f m_d).
  { apply (agree_trans _ m_f m_b m_d up_b). apply (above_munch _ _ _ mu_d). intros x far. cbn [outside]. split; [lia | exact I]. }
  assert (stk_d : stk asegs m_d lo (bv_unsigned sp + -96)).
  { apply (stk_munch _ m_b m_d _ _ stk_b mu_d wm_d). intros x xr. cbn [outside]. split; [lia | exact I]. }
  assert (env_d : cl_env m_d (Z_to_bv 8 1) canary) by exact (env_walk _ _ m_b m_d _ env_b mu_d ltac:(unfold ssp_guard; lia)).
  assert (wf_d : wmono asegs m_f m_d) by exact (wmono_trans _ _ _ _ wf_b wm_d).
  assert (h_tab3_d : rw_cells asegs m_d h (ht_tab3 ctx lk md)).
  { apply (wg_keep_seg _ m_b m_d _ _ h_tab3_b mu_d wm_d). intros x xr. cbn [cells_size csize Nat.add ht_tab3] in xr. cbn [outside].
    unfold apart in md_h. split; [lia | exact I]. }
  (* the rcu lock: ossl_rcu_lock_new(1, ctx) *)
  destruct (link_at m_d SITE_ht_rcu e_rcu_lock_new up_d wf_d
              ltac:(unfold HT_SITES; right; right; right; right; left; reflexivity) ltac:(unfold HT_CALLS; right; right; right; right; left; reflexivity)
              ltac:(unfold SITE_ht_rcu; lia)) as (cgx_5 & chain_5).
  rewrite <- cg_b in cgx_5.
  change e_rcu_lock_new with Fz_T_rcuw.e_rcu_lock_new in cgx_5.
  assert (cok_d : call_ok RT S4 m_d (Z_to_bv 64 (bv_unsigned sp + -96)) lo).
  { unfold call_ok. rewrite csp_u, sp0_b. split; [exact stk_d |]. unfold RT_STACK, USTACK_TOP in *. repeat split; lia. }
  assert (rcu_cg4 : cg_has (rt_cg RT S4) RCU_SITES RCU_CALLS) by (rewrite cg_b; apply (cg_has_weaken _ _ _ _ _ cgh_e); vm_compute; reflexivity).
  refine (C_RCU S4 PM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m_d lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary
            pm_fds pm_stable eq_refl ctx_nz eq_refl art_d inv_d cok_d (room_c 464 ltac:(lia)) cgx_5 chain_5 rcu_cg4
            ltac:(rewrite frs_b; exact nfr_e) ltac:(rewrite live_b; cbn [length]; lia) ltac:(rewrite cred_b, mcnb, mc24, mc96; lia) env_d T k_d at_d' _).
  intros k_u got_u.
  destruct got_u as (S5 & rl & rq & at_u & live_u & frs_u & sp0_u & cred_u & rl_pos & rl_al & rl_top & rq_pos & rq_al & rq_top & cg_u).
  destruct (ASTA_unpack RT S5 PM _ k_u at_u)
    as (ms_u & (m_u & ret_u & aft_u & pres_u & env_u & head_u & mx1_u & mx2_u & cd1_u & mx3_u & cd2_u & rl_acc_u & rq_cells_u & rq_acc_u) & at_u').
  clear at_u.
  destruct ret_u as (t0g & t1g & t2g & a1g & a2h & a3g & a4g & a5g & a6g & a7g & t3g & t4g & t5g & t6g & Fg & fcg & ->).
  destruct aft_u as (art_u & inv_u & wm_u & stk_u).
  rewrite (ret_pc_even SITE_ht_rcu) in at_u' by (unfold SITE_ht_rcu; lia).
  rewrite csp_u in stk_u, pres_u.
  rewrite live_b in live_u. rewrite frs_b in frs_u, pres_u. rewrite sp0_b in sp0_u. rewrite cg_b in cg_u. rewrite cred_b in cred_u.
  assert (rq_in : In (rq, 16) (rt_live RT S5)) by (rewrite live_u; left; reflexivity).
  assert (rl_in : In (rl, 264) (rt_live RT S5)) by (rewrite live_u; right; left; reflexivity).
  assert (nb_in5 : In (nb, NB_BYTES) (rt_live RT S5)) by (rewrite live_u; do 2 right; left; reflexivity).
  assert (md_in5 : In (md, 24) (rt_live RT S5)) by (rewrite live_u; do 3 right; left; reflexivity).
  assert (lk_in5 : In (lk, 40) (rt_live RT S5)) by (rewrite live_u; do 4 right; left; reflexivity).
  assert (h_in5 : In (h, 96) (rt_live RT S5)) by (rewrite live_u; do 5 right; left; reflexivity).
  assert (lk_in4 : In (lk, 40) (rt_live RT S4)) by (rewrite live_b; do 2 right; left; reflexivity).
  assert (rl_h : apart rl 264 h 96).
  { unfold apart. apply (wg_live_apart RT AF S5 m_u [(rq, 16)] rl 264 ((nb, NB_BYTES) :: (md, 24) :: (lk, 40) :: (h, 96) :: rt_live RT S0) h 96 art_u);
      [rewrite live_u; reflexivity | do 4 right; left; reflexivity]. }
  assert (rq_h : apart rq 16 h 96).
  { unfold apart. apply (wg_live_apart RT AF S5 m_u [] rq 16 ((rl, 264) :: (nb, NB_BYTES) :: (md, 24) :: (lk, 40) :: (h, 96) :: rt_live RT S0) h 96 art_u);
      [rewrite live_u; reflexivity | do 4 right; left; reflexivity]. }
  assert (ag_u : agree_on keep0 m m_u).
  { apply (agree_trans _ m m_d m_u ag_d). apply (keep_pres _ _ m_d m_u pres_u); [rewrite live_b; intros e ein; do 4 right; exact ein | exact (fun x kx => proj2 kx)]. }
  assert (up_u : agree_on above m_f m_u).
  { apply (agree_trans _ m_f m_d m_u up_d). apply (above_pres _ _ _ m_d m_u pres_u). intros x far. cbn [outside]. unfold G_ALLOW_CUST. split; [lia | exact I]. }
  assert (wf_u : wmono asegs m_f m_u) by exact (wmono_trans _ _ _ _ wf_d wm_u).
  assert (h_tab3_u : rw_cells asegs m_u h (ht_tab3 ctx lk md)).
  { apply (wg_keep_live _ _ _ _ m_d m_u h 96 h _ h_tab3_d pres_u wm_u); [exact h_in4 | lia | cbn; lia |].
    intros x xr. cbn [outside]. unfold G_ALLOW_CUST. split; [lia | exact I]. }
  pose proof (af_acc_live RT AF S5 m_u h 96 art_u h_in5) as (_ & h_acc_u).
  assert (frame_u : rw_cells asegs m_u (bv_unsigned sp + -96) [CB 8 junk_f; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m_f m_u _ _ frame_f); [| exact wf_u].
    apply (agree_sub _ _ _ _ up_u). intros x xr. cbn [cells_size csize Nat.add] in xr. unfold above. lia. }
  (* the lock pointer, the frame release and the return of the table *)
  pose proof (ht_w6 ra sp gp (Z_to_bv 64 TP_A) t0g t1g t2g a1g a2h a3g a4g a5g a6g a7g s10 s11 t3g t4g t5g t6g s0 s1 s2 s3 s4 s5 s6 s7 s8 s9
                Fg fcg m_u h conf rl lk md lo ctx junk_f
                ltac:(lia) lo_big sp_fit h_hi h_lo h_al8 ltac:(lia) ltac:(lia) rl_pos ltac:(unfold USTACK_TOP in *; lia)
                stk_u frame_u h_tab3_u h_acc_u inv_u) as walk.
  cl_lift walk at_u' k_x at_x.
  destruct (ASTA_unpack RT S5 PM _ k_x at_x) as (ms_x & (a1x & m_x & -> & mu_x & wm_x & inv_x & stk_x & h_tab4) & at_x'). clear at_x.
  assert (art_x : ART RT S5 m_x) by exact (art_walk S5 m_u m_x h 96 h (h + 96) art_u sp0_u h_in5 ltac:(lia) ltac:(lia) mu_x wm_x).
  assert (ag_x : agree_on keep0 m m_x).
  { apply (agree_trans _ m m_u m_x ag_u). apply (agree_of_munch _ _ _ _ mu_x). intros x kx. cbn [outside]. split; [| exact I].
    pose proof (h_fresh x kx). lia. }
  assert (env_x : cl_env m_x (Z_to_bv 8 1) canary) by exact (env_walk _ _ m_u m_x _ env_u mu_x ltac:(unfold ssp_guard; lia)).
  assert (mono_x : wmono asegs m m_x) by exact (wmono_trans _ _ _ _ wm_f (wmono_trans _ _ _ _ wf_u wm_x)).
  (* what the later steps left in place, block by block *)
  assert (blk_pres : forall live frs W (ma mb : mem) p n, rt_pres_fp live frs (bv_unsigned sp + -96) W ma mb -> In (p, n) live ->
            (forall x, p <= x < p + n -> outside W x) -> agree_on (fun x => p <= x < p + n) ma mb).
  { intros live frs W ma mb p n pres pin outw. apply (agree_of_pres_fp _ _ _ _ _ _ _ pres). intros x xr.
    split; [apply (acl_live _ _ _ p n); [exact pin | exact xr] | exact (outw x xr)]. }
  assert (blk_munch : forall a b (ma mb : mem) p n, munch [(a, b)] ma mb -> b <= p \/ p + n <= a -> agree_on (fun x => p <= x < p + n) ma mb).
  { intros a b ma mb p n mu far. apply (agree_of_munch _ _ _ _ mu). intros x xr. cbn [outside]. split; [lia | exact I]. }
  assert (lk_kept : agree_on (fun x => lk <= x < lk + 40) m_l m_x).
  { unfold apart in lk_h, md_lk.
    apply (agree_trans _ m_l m_u m_x); [| apply (blk_munch _ _ _ _ _ _ mu_x); lia].
    apply (agree_trans _ m_l m_d m_u); [| apply (blk_pres _ _ _ _ _ _ _ pres_u lk_in4); intros x xr; cbn [outside]; unfold G_ALLOW_CUST; split; [lia | exact I]].
    apply (agree_trans _ m_l m_b m_d); [| apply (blk_munch _ _ _ _ _ _ mu_d); lia].
    apply (agree_trans _ m_l m_n m_b); [| apply (blk_pres _ _ _ _ _ _ _ pres_b lk_in3); intros x xr; cbn [outside]; split; [lia | exact I]].
    apply (agree_trans _ m_l m_z m_n); [| apply (blk_munch _ _ _ _ _ _ mu_n); lia].
    apply (agree_trans _ m_l m_r m_z); [| apply (blk_pres _ _ _ _ _ _ _ pres_z lk_in); intros x xr; cbn [outside]; unfold G_ALLOW_CUST; split; [lia | exact I]].
    apply (agree_trans _ m_l m_y m_r); [| apply (blk_munch _ _ _ _ _ _ mu_r); lia].
    apply (agree_trans _ m_l m_p m_y); [apply (blk_munch _ _ _ _ _ _ mu_p); lia |].
    apply (agree_of_pres_ex _ _ _ _ _ _ _ _ pres_y). intros x xr. split; [apply (acl_live _ _ _ lk 40); [exact lk_in | exact xr] | lia]. }
  assert (wl_x : wmono asegs m_l m_x).
  { apply (wmono_trans _ _ m_u _); [| exact wm_x]. apply (wmono_trans _ _ m_d _); [| exact wm_u]. apply (wmono_trans _ _ m_b _); [| exact wm_d].
    apply (wmono_trans _ _ m_n _); [| exact wm_b]. apply (wmono_trans _ _ m_z _); [| exact wm_n]. apply (wmono_trans _ _ m_r _); [| exact wm_z].
    apply (wmono_trans _ _ m_y _); [| exact wm_r]. exact (wmono_trans _ _ _ _ wm_p wm_y). }
  assert (md_kept : agree_on (fun x => md <= x < md + 24) m_d m_x).
  { unfold apart in md_h. apply (agree_trans _ m_d m_u m_x); [| apply (blk_munch _ _ _ _ _ _ mu_x); lia].
    apply (blk_pres _ _ _ _ _ _ _ pres_u md_in4). intros x xr. cbn [outside]. unfold G_ALLOW_CUST. split; [lia | exact I]. }
  pose proof (wp_zero_rw_CB asegs m_b nb NB_BYTES zero_nb wr_nb ltac:(unfold NB_BYTES; lia)) as nb_zero_b.
  assert (nb_kept : agree_on (fun x => nb <= x < nb + NB_BYTES) m_b m_x).
  { unfold apart in nb_md, nb_h.
    apply (agree_trans _ m_b m_u m_x); [| apply (blk_munch _ _ _ _ _ _ mu_x); lia].
    apply (agree_trans _ m_b m_d m_u); [apply (blk_munch _ _ _ _ _ _ mu_d); lia |].
    apply (blk_pres _ _ _ _ _ _ _ pres_u nb_in). intros x xr. cbn [outside]. unfold G_ALLOW_CUST. split; [lia | exact I]. }
  assert (nb_size : Z.of_nat (cells_size [CB (Z.to_nat NB_BYTES) (repeat (Z_to_bv 8 0) (Z.to_nat NB_BYTES))]) = NB_BYTES).
  { cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id; [reflexivity | unfold NB_BYTES; lia]. }
  assert (rl_kept : agree_on (fun x => rl <= x < rl + 264) m_u m_x) by (unfold apart in rl_h; apply (blk_munch _ _ _ _ _ _ mu_x); lia).
  assert (rq_kept : agree_on (fun x => rq <= x < rq + 16) m_u m_x) by (unfold apart in rq_h; apply (blk_munch _ _ _ _ _ _ mu_x); lia).
  assert (wd_x : wmono asegs m_d m_x) by exact (wmono_trans _ _ _ _ wm_u wm_x).
  assert (wb_x : wmono asegs m_b m_x) by exact (wmono_trans _ _ _ _ wm_d wd_x).
  (* the caller's view *)
  apply finish. exists S5, h, lk, md, nb, rl, rq. split.
  - apply (ASTA_conseq RT S5 PM _ _ k_x at_x'). intros ms <-. exists m_x.
    split; [do 16 eexists; reflexivity |].
    split; [exact (conj art_x (conj inv_x (conj mono_x stk_x))) |].
    split; [intros a ka oa; exact (ag_x a (conj ka oa)) |].
    split; [exact env_x |].
    split; [exact h_tab4 |].
    split; [exact (proj2 (af_acc_live RT AF S5 m_x h 96 art_x h_in5)) |].
    split.
    { apply (rw_cells_agree asegs m_l m_x _ _ lk_cells); [| exact wl_x].
      apply (agree_sub _ _ _ _ lk_kept). intros x xr. cbn [mutex_cells cells_size csize Nat.add] in xr. lia. }
    split; [exact (proj2 (af_acc_live RT AF S5 m_x lk 40 art_x lk_in5)) |].
    split.
    { apply (rw_cells_agree asegs m_d m_x _ _ md_cells_d); [| exact wd_x].
      apply (agree_sub _ _ _ _ md_kept). intros x xr. cbn [cells_size csize Nat.add] in xr. lia. }
    split; [exact (proj2 (af_acc_live RT AF S5 m_x md 24 art_x md_in5)) |].
    split.
    { apply (rw_cells_agree asegs m_b m_x _ _ nb_zero_b); [| exact wb_x].
      apply (agree_sub _ _ _ _ nb_kept). intros x xr. rewrite nb_size in xr. exact xr. }
    split; [exact (proj2 (af_acc_live RT AF S5 m_x nb NB_BYTES art_x nb_in5)) |].
    split.
    { apply (rw_cells_agree asegs m_u m_x _ _ head_u); [| exact wm_x].
      apply (agree_sub _ _ _ _ rl_kept). intros x xr. cbn [rcu_head cells_size csize Nat.add] in xr. lia. }
    split.
    { apply (rw_cells_agree asegs m_u m_x _ _ mx1_u); [| exact wm_x].
      apply (agree_sub _ _ _ _ rl_kept). intros x xr. cbn [mutex_cells cells_size csize Nat.add] in xr. lia. }
    split.
    { apply (rw_cells_agree asegs m_u m_x _ _ mx2_u); [| exact wm_x].
      apply (agree_sub _ _ _ _ rl_kept). intros x xr. cbn [mutex_cells cells_size csize Nat.add] in xr. lia. }
    split.
    { apply (rw_cells_agree asegs m_u m_x _ _ cd1_u); [| exact wm_x].
      apply (agree_sub _ _ _ _ rl_kept). intros x xr. cbn [cond_cells cells_size csize Nat.add] in xr. lia. }
    split.
    { apply (rw_cells_agree asegs m_u m_x _ _ mx3_u); [| exact wm_x].
      apply (agree_sub _ _ _ _ rl_kept). intros x xr. cbn [mutex_cells cells_size csize Nat.add] in xr. lia. }
    split.
    { apply (rw_cells_agree asegs m_u m_x _ _ cd2_u); [| exact wm_x].
      apply (agree_sub _ _ _ _ rl_kept). intros x xr. cbn [cond_cells cells_size csize Nat.add] in xr. lia. }
    split; [exact (proj2 (af_acc_live RT AF S5 m_x rl 264 art_x rl_in)) |].
    split.
    { apply (rw_cells_agree asegs m_u m_x _ _ rq_cells_u); [| exact wm_x].
      apply (agree_sub _ _ _ _ rq_kept). intros x xr. cbn [cells_size csize Nat.add] in xr. lia. }
    exact (proj2 (af_acc_live RT AF S5 m_x rq 16 art_x rq_in)).
  - rewrite live_u, frs_u, sp0_u, cg_u, cred_u, cost3, ?mc96, ?mc24, ?mcnb.
    repeat split; first [reflexivity | assumption | lia].
Qed.
End HtNew.
