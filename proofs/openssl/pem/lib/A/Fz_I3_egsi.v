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
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_G_kit Fz_ckit Fz_env Fz_M_malloc Fz_M_zalloc Th_tsd Th_key Th_once Th_mutex Fz_T_once Fz_T_local Fz_T_sa Fz_T_sa_set Fz_T_master Fz_T_mtl Fz_T_its Fz_W5_glx Fz_W5_icb Fz_W5_gsi Fz_W5_gsi0 Fz_I3_glx0 Fz_G_OSSL_ERR_STATE_new Fz_I3_icfast Fz_I3_egsiw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Notation TP_A := (0xba3ef0)%Z (only parsing).

Section EgsiFirst.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_ICB : init_crypto_base_stmt RT.
Hypothesis C_NEW : OSSL_ERR_STATE_new_stmt RT.
Hypothesis C_ITS : its_first_stmt RT.
Hypothesis C_ICF : init_crypto_fast_stmt RT.
Hypothesis GO_mkey : GOBJ MK_KEY 4.
Hypothesis TSD : forall Σ m, ART RT Σ m -> rw_cells asegs m (TP_A + -88) [C8 (Z_to_bv 64 TSD_MAIN)].

Definition EG_SITES : list (Z * Z) := [(SITE_eg_new, e_get_state); (SITE_eg_its, e_get_state)] ++ (* [comment removed for export] *) [(SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)] ++ ITS_SITES.
Definition EG_CALLS : list (Z * Z) := [(SITE_eg_new, e_OSSL_ERR_STATE_new); (SITE_eg_new, e_CRYPTO_zalloc); (SITE_eg_its, e_its)] ++ [(SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)] ++ ITS_CALLS.
Definition EG_W (kd SA P : Z) : list (Z * Z) := (SA + 8, SA + 24) :: (P, P + 8) :: (G_ALLOW_CUST, G_ALLOW_CUST + 1) :: MTL_W kd.   (* [comment removed for export] *)

Definition egsi_first_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (k kd MK SA P : Z) (pad top : word)
    (jm1 jm2 jp : list byte) (u : byte) (r0 g0 oldcb : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A -> a0 = z64 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 864 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_get_state (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) EG_SITES EG_CALLS ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 7 <= LIVE_MAX -> 3 <= rt_credit RT Σ -> cl_env m lb canary ->
  rw_cells asegs m G_IC_STOPPED [C1 (Z_to_bv 8 0)] -> (exists od : word, rw_cells asegs m G_IC_OPTSDONE [C8 od] /\ Z.land (bv_unsigned od) 2 = 2) ->
  rw_cells asegs m G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)] -> rw_cells asegs m G_IC_BASE_RET [C4 (Z_to_bv 64 1)] ->
  rw_cells asegs m MK_ONCE [C4 (Z_to_bv 64 2)] -> rw_cells asegs m MK_KEY [C4 (Z_to_bv 64 k)] -> 1 <= k < 128 ->
  rw_cells asegs m (TSD_MAIN + 8 * k) [C8 (Z_to_bv 64 MK)] -> In (MK, 72) (rt_live RT Σ) -> MK mod 8 = 0 ->
  rw_cells asegs m MK [CB 24 jm1] -> rw_cells asegs m (MK + 24) [C8 (Z_to_bv 64 SA)] -> rw_cells asegs m (MK + 32) [CB 40 jm2] ->
  In (SA, 32) (rt_live RT Σ) -> SA mod 8 = 0 -> rw_cells asegs m SA (sa_hdr (Z_to_bv 64 1) pad top z64 (Z_to_bv 64 P)) ->
  In (P, 128) (rt_live RT Σ) -> P mod 8 = 0 -> rw_cells asegs m P [C8 z64] -> rw_cells asegs m (P + 8) [CB 120 jp] ->
  rw_cells asegs m 0x5a9f20 [C4 (Z_to_bv 64 kd); C4 (Z_to_bv 64 0xffffffff)] -> 1 <= kd < 128 -> kd <> k ->
  rw_cells asegs m (TSD_MAIN + 8 * kd) [C8 z64] -> rw_cells asegs m (TP_A + -150) [C1 u] -> rw_cells asegs m 0xb9f4a0 [C4 z64] ->
  rw_cells asegs m 0xb9f4c0 [C4 r0] -> rw_cells asegs m 0xb9f4e0 [C8 g0] -> rw_cells asegs m (TP_A + -96) [C8 oldcb] ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_get_state m)))
    (fun c => exists (Σ' : rts RT) (E N H G SK LK D : Z) (u' : byte) (top' : word),
       ASTA RT Σ' PMc (fun ms => exists m' : mem,
              ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 E) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (EG_W kd SA P) m m'
           /\ cl_env m' (Z_to_bv 8 1) canary /\ bv_unsigned top' = Z.max (bv_unsigned top) 0
           /\ rw_cells asegs m' SA (sa_hdr (Z_to_bv 64 1) pad top' (Z_to_bv 64 1) (Z_to_bv 64 P)) /\ rw_cells asegs m' P [C8 (Z_to_bv 64 E); CB 120 jp]
           /\ rw_cells asegs m' MK [CB 24 jm1; C8 (Z_to_bv 64 SA); CB 40 jm2] /\ rw_cells asegs m' E [CB 904 (repeat (Z_to_bv 8 0) 904)]
           /\ rw_cells asegs m' (TSD_MAIN + 8 * kd) [C8 (Z_to_bv 64 H)] /\ rw_cells asegs m' (TP_A + -150) [C1 u'] /\ rw_cells asegs m' 0xb9f4a0 [C4 (Z_to_bv 64 2)]
           /\ rw_cells asegs m' 0xb9f4c0 [C4 (Z_to_bv 64 1)] /\ rw_cells asegs m' 0xb9f4e0 [C8 (Z_to_bv 64 G)] /\ rw_cells asegs m' (TP_A + -96) [C8 oldcb]
           /\ rw_cells asegs m' H [C8 (Z_to_bv 64 N)] /\ rw_cells asegs m' N [C8 z64; C8 z64; C8 (Z_to_bv 64 ERR_DEL_THREAD_STATE); C8 z64]
           /\ rw_cells asegs m' G [C8 (Z_to_bv 64 SK); C8 (Z_to_bv 64 LK)]
           /\ rw_cells asegs m' SK (Fz_T_sk.sk_cells (Z_to_bv 64 1) z64 (Z_to_bv 64 D) (Z_to_bv 64 1) (Z_to_bv 64 4) z64 (Z_to_bv 64 TEV_CMP) (Z_to_bv 64 TEV_FREE) (Z_to_bv 64 TEV_COPY))
           /\ rw_cells asegs m' LK (mutex_cells z64 z64) /\ rw_cells asegs m' D [C8 (Z_to_bv 64 H); CB 24 (repeat (Z_to_bv 8 0) 24)]) c
       /\ rt_live RT Σ' = [(N, 32); (D, 32); (LK, 40); (SK, 56); (G, 16); (H, 8); (E, 904)] ++ rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ - 3 /\ rt_cg RT Σ' = rt_cg RT Σ
       /\ Forall (fun b => 0x10007fff8000 <= fst b /\ fst b mod 16 = 0 /\ fst b + snd b < USTACK_TOP) [(N, 32); (D, 32); (LK, 40); (SK, 56); (G, 16); (H, 8); (E, 904)]).

Theorem egsi_first_cps : egsi_first_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary
    k kd MK SA P pad top jm1 jm2 jp u r0 g0 oldcb
    fd_only pm_stable tp_val a0_val art_m inv_m callok_m room_m ctx_m chain_m graph_m nfr_m nlive_m credit_m env_m
    stop_m optd_m bonce_m bret_m monce_m mkey_m k_range tslot_m mk_live mk_al mkj1_m mksa_m mkj2_m
    sa_live sa_al sahdr_m p_live p_al pslot_m pj_m dkey_m kd_range kd_k tslotd_m ub_m w784_m w816_m w848_m ocb_m.
  subst tp a0. intros T c0 at0 finish_k.
  destruct callok_m as (stk_m & win_m & rtroom_m & sptop_m & spal_m).
  destruct optd_m as (od & optd_m & od_bit).
  pose proof (af_sp0_win RT AF Σ m art_m) as sp0_floor.
  destruct (af_client_consts RT AF Σ m art_m) as (_ & shadow_m & _ & _ & untouched_m).
  unfold RT_STACK in room_m, rtroom_m.
  assert (lo_heap : 0x10007fff8000 <= lo) by (unfold STACK_WIN in win_m; lia).
  assert (sp_cap : bv_unsigned sp <= 2 ^ 47) by (unfold USTACK_TOP in sptop_m; lia).
  assert (sp48 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  (* where the three thread-local blocks lie *)
  pose proof (af_live_range RT AF Σ m MK 72 art_m mk_live) as (mk_pos & mk_top & _).
  pose proof (af_live_range RT AF Σ m SA 32 art_m sa_live) as (sa_pos & sa_top & _).
  pose proof (af_live_range RT AF Σ m P 128 art_m p_live) as (p_pos & p_top & _).
  pose proof (afp_live_hi RT GOBJ AFP Σ m MK 72 art_m mk_live ltac:(lia)) as mk_heap.
  pose proof (afp_live_hi RT GOBJ AFP Σ m SA 32 art_m sa_live ltac:(lia)) as sa_heap.
  pose proof (afp_live_hi RT GOBJ AFP Σ m P 128 art_m p_live ltac:(lia)) as p_heap.
  assert (drop_other : forall (x y : Z * Z) l1 l2, In x (l1 ++ y :: l2) -> x <> y -> In x (l1 ++ l2)).
  { intros x y l1 l2 x_in x_ne. apply in_app_or in x_in. apply in_or_app.
    destruct x_in as [in_l1 | [same | in_l2]]; [left; exact in_l1 | congruence | right; exact in_l2]. }
  destruct (in_split _ _ sa_live) as (sl1 & sl2 & live_at_sa).
  assert (sa_mk : SA + 32 <= MK \/ MK + 72 <= SA).
  { apply (af_live_disj RT AF Σ m SA 32 MK 72 sl1 sl2 art_m live_at_sa).
    apply (drop_other _ (SA, 32)); [rewrite <- live_at_sa; exact mk_live | intro same; discriminate same]. }
  assert (sa_p : SA + 32 <= P \/ P + 128 <= SA).
  { apply (af_live_disj RT AF Σ m SA 32 P 128 sl1 sl2 art_m live_at_sa).
    apply (drop_other _ (SA, 32)); [rewrite <- live_at_sa; exact p_live | intro same; discriminate same]. }
  destruct (in_split _ _ p_live) as (pl1 & pl2 & live_at_p).
  assert (p_mk : P + 128 <= MK \/ MK + 72 <= P).
  { apply (af_live_disj RT AF Σ m P 128 MK 72 pl1 pl2 art_m live_at_p).
    apply (drop_other _ (P, 128)); [rewrite <- live_at_p; exact mk_live | intro same; discriminate same]. }
  clear sl1 sl2 live_at_sa pl1 pl2 live_at_p.
  (* moving a cell of the entry memory forward *)
  assert (keep : forall W mi a cs, rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) W m mi -> wmono asegs m mi ->
            rw_cells asegs m a cs ->
            (forall x, a <= x < a + Z.of_nat (cells_size cs) -> aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) x /\ outside W x) ->
            rw_cells asegs mi a cs).
  { intros W mi a cs pres_i wm_i cells_a cover. apply (rw_cells_agree asegs m mi a cs cells_a); [| exact wm_i].
    intros w w_in. destruct (cover _ w_in) as (is_cl & is_out). exact (pres_i w is_cl is_out). }
  assert (stat_cl : forall x, 0x5a9d08 <= x < 0x6694d8 \/ 0xb8f190 <= x < 0xba3e98 \/ 0xbc52a0 <= x < 0xbc57d0 ->
            aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) x).
  { intros x x_rng. right; left. apply client_static_intro. lia. }
  assert (live_cl : forall p n x, In (p, n) (rt_live RT Σ) -> p <= x < p + n -> aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) x).
  { intros p n x pn_in x_rng. right; right; left. exists p, n. split; [exact pn_in | exact x_rng]. }
  (* entry of ossl_err_get_state_int to its call of OPENSSL_init_crypto (base only) *)
  pose proof (gsi0_s0_walk ra sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                stk_m ltac:(lia) lo_heap sp_cap untouched_m shadow_m inv_m) as walk0.
  cl_lift walk0 at0 c1 at1.
  destruct (ASTA_unpack RT Σ _ _ c1 at1) as (ms1 & (m1 & -> & mu1 & wm1 & inv1 & frame1 & stk1) & here1). clear at1.
  pose proof (cl_seg_pres RT AF Σ m m1 (bv_unsigned sp) 48 [] art_m ltac:(lia) ltac:(lia) mu1) as pres1.
  pose proof (cl_seg_ART RT AF Σ m m1 (bv_unsigned sp) 48 [] art_m ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) mu1
                (fun x out_x => False_ind _ (out_x I)) wm1) as art1.
  assert (ic1 : rw_cells asegs m1 G_IC_STOPPED [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m1 G_IC_OPTSDONE [C8 od]
                /\ rw_cells asegs m1 G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m1 G_IC_BASE_RET [C4 (Z_to_bv 64 1)]).
  { unfold G_IC_STOPPED, G_IC_OPTSDONE, G_IC_BASE_ONCE, G_IC_BASE_RET in *.
    repeat split; (eapply (keep [] m1 _ _ pres1 wm1); [eassumption |]); intros x x_rng; cbn [cells_size csize Nat.add] in x_rng;
      (split; [apply stat_cl; lia | exact I]). }
  destruct ic1 as (stop1 & optd1 & bonce1 & bret1).
  assert (callok1 : call_ok RT Σ m1 (Z_to_bv 64 (bv_unsigned sp + -48)) lo) by (cl_call_ok sp48 stk1 win_m spal_m 3).
  apply (cps_realizes asegs _ _ T c1
           (C_ICB Σ PMc (Z_to_bv 64 SITE_gsi_icb) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp z64
              (Z_to_bv 64 OPT_BASE_ONLY) z64 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 2147450880) z64 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo od
              fd_only pm_stable eq_refl eq_refl art1 inv1 callok1 ltac:(rewrite sp48; unfold RT_STACK; lia) nfr_m ltac:(lia) stop1 optd1 bonce1 bret1) here1).
  intros c2 (Σ2 & at2 & lv2 & fr2 & sp02 & cr2 & cg2).
  destruct (ASTA_unpack RT Σ2 _ _ c2 at2) as (ms2 & (m2 & back2 & (art2 & inv2 & wm2 & stk2) & pres2 & _) & here2). clear at2.
  destruct back2 as (t0_2 & t1_2 & t2_2 & a1_2 & a2_2 & a3_2 & a4_2 & a5_2 & a6_2 & a7_2 & t3_2 & t4_2 & t5_2 & t6_2 & F_2 & fc_2 & ->).
  rewrite (ret_pc_even SITE_gsi_icb) in here2 by (unfold SITE_gsi_icb; first [lia | reflexivity]).
  rewrite sp48 in stk2, pres2.
  assert (in_live2 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ2)) by (rewrite lv2; exact (fun e e_in => e_in)).
  assert (pres2' : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [] m m2).
  { apply (pres_fp_trans _ _ _ _ m m1 m2 pres1). intros w is_cl _. apply pres2.
    apply (aclient_mono _ _ _ _ _ _ _ is_cl); [exact (fun e e_in => e_in) | exact (fun e e_in => e_in) | lia]. }
  pose proof (wmono_trans asegs _ _ _ wm1 wm2) as wm2'.
  assert (ag2 : agree_on (fun x => bv_unsigned sp - 48 <= x < USTACK_TOP) m1 m2).
  { intros w w_in. apply pres2. left. lia. }
  (* the master key state seen by the walk to OSSL_ERR_STATE_new *)
  assert (mo2 : rw_cells asegs m2 MK_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m2 MK_KEY [C4 (Z_to_bv 64 k)]
                /\ rw_cells asegs m2 (TSD_MAIN + 8 * k) [C8 (Z_to_bv 64 MK)]).
  { repeat split; (eapply (keep [] m2 _ _ pres2' wm2'); [eassumption |]); intros x x_rng; cbn [cells_size csize Nat.add] in x_rng;
      (split; [apply stat_cl; lia | exact I]). }
  destruct mo2 as (monce2 & mkey2 & tslot2).
  assert (blk2 : rw_cells asegs m2 (MK + 24) [C8 (Z_to_bv 64 SA)] /\ rw_cells asegs m2 SA (sa_hdr (Z_to_bv 64 1) pad top z64 (Z_to_bv 64 P))
                 /\ rw_cells asegs m2 P [C8 z64]).
  { split; [| split].
    - apply (keep [] m2 _ _ pres2' wm2' mksa_m). intros x x_rng. cbn [cells_size csize Nat.add] in x_rng.
      split; [apply (live_cl MK 72); [exact mk_live | lia] | exact I].
    - apply (keep [] m2 _ _ pres2' wm2' sahdr_m). intros x x_rng. unfold sa_hdr in x_rng. cbn [cells_size csize Nat.add] in x_rng.
      split; [apply (live_cl SA 32); [exact sa_live | lia] | exact I].
    - apply (keep [] m2 _ _ pres2' wm2' pslot_m). intros x x_rng. cbn [cells_size csize Nat.add] in x_rng.
      split; [apply (live_cl P 128); [exact p_live | lia] | exact I]. }
  destruct blk2 as (mksa2 & sahdr2 & pslot2).
  destruct (af_client_consts RT AF Σ2 m2 art2) as (_ & shadow2 & _ & _ & untouched2).
  (* back from OPENSSL_init_crypto: the empty slot is claimed, then OSSL_ERR_STATE_new is called *)
  pose proof (eg_w1 sp gp t0_2 t1_2 t2_2 a1_2 a2_2 a3_2 a4_2 a5_2 a6_2 a7_2 s2 s5 s6 s7 s8 s9 s10 s11 t3_2 t4_2 t5_2 t6_2 F_2 fc_2 m2 lo k MK SA P pad top
                stk2 ltac:(lia) lo_heap sp_cap untouched2 shadow2 (proj1 monce2) (proj1 mkey2) k_range
                (afp_gsh_byte RT GOBJ AFP Σ2 m2 MK_KEY 4 MK_KEY art2 GO_mkey ltac:(lia) ltac:(lia) ltac:(reflexivity))
                (proj1 (TSD Σ2 m2 art2)) (proj1 tslot2) mk_heap mk_al ltac:(unfold STACK_WIN in *; lia)
                (proj2 (af_acc_live RT AF Σ2 m2 MK 72 art2 (in_live2 _ mk_live))) (proj1 mksa2)
                sa_heap sa_al ltac:(unfold STACK_WIN in *; lia) (proj2 (af_acc_live RT AF Σ2 m2 SA 32 art2 (in_live2 _ sa_live))) sahdr2
                p_heap p_al ltac:(unfold STACK_WIN in *; lia) (proj2 (af_acc_live RT AF Σ2 m2 P 128 art2 (in_live2 _ p_live))) pslot2 sa_p inv2)
    as walk1.
  cl_lift walk1 here2 c3 at3.
  destruct (ASTA_unpack RT Σ2 _ _ c3 at3)
    as (ms3 & (t1_3 & a1_3 & a2_3 & a3_3 & a4_3 & a5_3 & a6_3 & top1 & m3 & -> & mu3 & wm3 & inv3 & stk3 & top1_val & sahdr3 & pslot3) & here3).
  clear at3.
  assert (art3 : ART RT Σ2 m3).
  { apply (af_frame RT AF Σ2 m2 m3 (bv_unsigned sp - 160) art2 ltac:(rewrite sp02; lia)); [| exact wm3].
    intros w not_cl. apply mu3. cbn [outside].
    assert (off_sa : ~ (SA + 8 <= bv_unsigned w < SA + 24)).
    { intros w_in. apply not_cl. right; right; left. exists SA, 32. split; [exact (in_live2 _ sa_live) | lia]. }
    assert (off_p : ~ (P <= bv_unsigned w < P + 8)).
    { intros w_in. apply not_cl. right; right; left. exists P, 128. split; [exact (in_live2 _ p_live) | lia]. }
    assert (off_stk : ~ (bv_unsigned sp - 160 <= bv_unsigned w < bv_unsigned sp - 48)).
    { intros w_in. apply not_cl. left. unfold USTACK_TOP in *. lia. }
    exact (conj off_stk (conj off_sa (conj off_p I))). }
  assert (pres3 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(SA + 8, SA + 24); (P, P + 8)] m m3).
  { intros w is_cl is_out. transitivity (m2 w); [| exact (pres2' w is_cl I)]. apply mu3.
    cbn [outside] in *. destruct is_out as (out_sa & out_p & _). split; [| split; [exact out_sa | split; [exact out_p | exact I]]].
    destruct (cl_split RT AF Σ m (bv_unsigned sp) 160 (bv_unsigned w) art_m ltac:(lia) ltac:(lia) is_cl); lia. }
  pose proof (wmono_trans asegs _ _ _ wm2' wm3) as wm3'.
  assert (ag3 : agree_on (fun x => bv_unsigned sp - 48 <= x < USTACK_TOP) m1 m3).
  { intros w w_in. transitivity (m2 w); [| exact (ag2 w w_in)]. apply mu3. cbn [outside]. repeat split; try exact I; lia. }
  pose proof (wmono_trans asegs _ _ _ wm2 wm3) as wm13.
  assert (env3 : cl_env m3 lb canary).
  { pose proof (cl_env_seg _ m m1 lb canary env_m mu1 ltac:(cl_fp_lia)) as env1.
    pose proof (cl_env_agree m1 m2 _ _ env1 (fun w w_cl => pres2 w (acl_static _ _ _ _ (cl_cell_static _ w_cl)))) as env2.
    exact (cl_env_seg _ m2 m3 lb canary env2 mu3 ltac:(cl_fp_lia)). }
  (* the call of OSSL_ERR_STATE_new *)
  assert (frame3 : rw_cells asegs m3 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m1 m3 _ _ frame1); [| exact wm13]. intros w w_in. cbn [cells_size csize Nat.add] in w_in.
    apply ag3. unfold USTACK_TOP in *. lia. }
  assert (link3 : rw_cells asegs m3 (bv_unsigned sp - 16) [C8 s0; C8 ra]).
  { pose proof (rw_cells_skip m3 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] frame3) as tail3.
    cbn [cells_size csize Nat.add] in tail3. replace (bv_unsigned sp - 16) with (bv_unsigned sp + -48 + Z.of_nat 32) by lia. exact tail3. }
  assert (top3 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m3).
  { intros w w_in. transitivity (m1 w); [apply ag3; lia | apply mu1; cbn [outside]; split; [lia | exact I]]. }
  destruct (cl_chain_call (rt_cg RT Σ) e_get_state e_OSSL_ERR_STATE_new SITE_eg_new m m3 ra s0 sp (Z_to_bv 64 (bv_unsigned sp + -48)) outer
              ctx_m (proj1 graph_m (SITE_eg_new, e_get_state) ltac:(unfold EG_SITES; cbn [app In]; repeat (first [left; reflexivity | right])))
              (proj2 graph_m (SITE_eg_new, e_OSSL_ERR_STATE_new) ltac:(unfold EG_CALLS; cbn [app In]; repeat (first [left; reflexivity | right])))
              chain_m top3 link3 ltac:(rewrite sp48; lia) ltac:(unfold USTACK_TOP in *; lia)) as (ctx3 & chain3).
  assert (ctx3' : cg_ctx (rt_cg RT Σ2) e_OSSL_ERR_STATE_new (bv_unsigned (Z_to_bv 64 SITE_eg_new) :: bv_unsigned ra :: outer))
    by (rewrite cg2, unsigned_lit by (unfold SITE_eg_new; lia); exact ctx3).
  assert (zalloc3 : In (bv_unsigned (Z_to_bv 64 SITE_eg_new), e_CRYPTO_zalloc) (cg_call (rt_cg RT Σ2))).
  { rewrite cg2, unsigned_lit by (unfold SITE_eg_new; lia). apply (proj2 graph_m). unfold EG_CALLS. cbn [app In].
    repeat (first [left; reflexivity | right]). }
  assert (graph3 : cg_has (rt_cg RT Σ2) [(SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)]
                     [(SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)]).
  { rewrite cg2. apply (cg_has_weaken _ _ _ _ _ graph_m); vm_compute; reflexivity. }
  assert (win2 : rt_sp0 RT Σ2 - STACK_WIN <= lo) by (rewrite sp02; exact win_m).
  assert (callok3 : call_ok RT Σ2 m3 (Z_to_bv 64 (bv_unsigned sp + -48)) lo) by (cl_call_ok sp48 stk3 win2 spal_m 3).
  apply (cps_realizes asegs _ _ T c3
           (C_NEW Σ2 PMc (Z_to_bv 64 SITE_eg_new) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 TP_A) t0_2 t1_3 t2_2 sp z64 (Z_to_bv 64 1)
              a1_3 a2_3 a3_3 a4_3 a5_3 a6_3 a7_2 z64 (Z_to_bv 64 2147450880) z64 s5 s6 s7 s8 s9 s10 s11 t3_2 t4_2 t5_2 t6_2 F_2 fc_2 m3 lo
              (bv_unsigned ra :: outer) lb canary
              fd_only pm_stable eq_refl art3 inv3 callok3 ltac:(rewrite sp48; unfold RT_STACK; lia) ctx3' chain3 zalloc3 graph3
              ltac:(rewrite lv2; lia) ltac:(change (mcost 904) with 0; lia) env3) here3).
  intros c4 (Σ3 & E & at4 & lv3 & fr3 & sp03 & cr3 & e_pos & e_al & e_top & cg3).
  destruct (ASTA_unpack RT Σ3 _ _ c4 at4) as (ms4 & (m4 & back4 & (art4 & inv4 & wm4 & stk4) & pres4 & env4 & wr4 & _ & zero4) & here4).
  clear at4.
  destruct back4 as (t0_4 & t1_4 & t2_4 & a1_4 & a2_4 & a3_4 & a4_4 & a5_4 & a6_4 & a7_4 & t3_4 & t4_4 & t5_4 & t6_4 & F_4 & fc_4 & ->).
  rewrite (ret_pc_even SITE_eg_new) in here4 by (unfold SITE_eg_new; first [lia | reflexivity]).
  rewrite sp48 in stk4, pres4.
  change (mcost 904) with 0 in cr3.
  assert (e_in3 : In (E, 904) (rt_live RT Σ3)) by (rewrite lv3; left; reflexivity).
  pose proof (afp_live_hi RT GOBJ AFP Σ3 m4 E 904 art4 e_in3 ltac:(lia)) as e_heap.
  pose proof (af_live_range RT AF Σ3 m4 E 904 art4 e_in3) as (_ & e_win & _). rewrite sp03, sp02 in e_win.
  assert (in_live3 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ3)) by (rewrite lv3, lv2; exact (fun e e_in => or_intror e_in)).
  assert (e_apart : forall p n, In (p, n) (rt_live RT Σ) -> E + 904 <= p \/ p + n <= E).
  { intros p n pn_in. apply (af_live_disj RT AF Σ3 m4 E 904 p n [] (rt_live RT Σ2) art4 lv3). rewrite lv2. exact pn_in. }
  assert (pres4' : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(SA + 8, SA + 24); (P, P + 8); (G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m4).
  { intros w is_cl is_out. cbn [outside] in is_out. destruct is_out as (out_sa & out_p & out_g & _).
    transitivity (m3 w).
    - apply pres4; [| cbn [outside]; split; [exact out_g | exact I]].
      apply (aclient_mono _ _ _ _ _ _ _ is_cl); [exact in_live2 | rewrite fr2; exact (fun e e_in => e_in) | lia].
    - apply pres3; [exact is_cl | cbn [outside]; split; [exact out_sa | split; [exact out_p | exact I]]]. }
  pose proof (wmono_trans asegs _ _ _ wm3' wm4) as wm4'.
  pose proof (wmono_trans asegs _ _ _ wm13 wm4) as wm14.
  assert (ag4 : agree_on (fun x => bv_unsigned sp - 48 <= x < USTACK_TOP) m1 m4).
  { intros w w_in. transitivity (m3 w); [| exact (ag3 w w_in)].
    apply pres4; [left; lia | cbn [outside]; unfold G_ALLOW_CUST; split; [lia | exact I]]. }
  (* OSSL_ERR_STATE_new returned a fresh state: arguments for ossl_init_thread_start *)
  pose proof (eg_w2 sp gp (Z_to_bv 64 TP_A) t0_4 t1_4 t2_4 a1_4 a2_4 a3_4 a4_4 a5_4 a6_4 a7_4 s5 s6 s7 s8 s9 s10 s11 t3_4 t4_4 t5_4 t6_4 F_4 fc_4 m4 E
                ltac:(unfold USTACK_TOP in *; lia) inv4) as walk2.
  cl_lift walk2 here4 c5 at5.
  destruct (ASTA_unpack RT Σ3 _ _ c5 at5) as (ms5 & -> & here5). clear at5.
  (* the call of ossl_init_thread_start *)
  assert (its4 : rw_cells asegs m4 0x5a9f20 [C4 (Z_to_bv 64 kd); C4 (Z_to_bv 64 0xffffffff)] /\ rw_cells asegs m4 (TSD_MAIN + 8 * kd) [C8 z64]
                 /\ rw_cells asegs m4 (TP_A + -150) [C1 u] /\ rw_cells asegs m4 0xb9f4a0 [C4 z64] /\ rw_cells asegs m4 0xb9f4c0 [C4 r0]
                 /\ rw_cells asegs m4 0xb9f4e0 [C8 g0] /\ rw_cells asegs m4 (TP_A + -96) [C8 oldcb]).
  { repeat split; (eapply (keep _ m4 _ _ pres4' wm4'); [eassumption |]); intros x x_rng; cbn [cells_size csize Nat.add] in x_rng;
      (split; [apply stat_cl; lia | cbn [outside]; unfold G_ALLOW_CUST; repeat split; try exact I; lia]). }
  destruct its4 as (dkey4 & tslotd4 & ub4 & w784_4 & w816_4 & w848_4 & ocb4).
  assert (frame4 : rw_cells asegs m4 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m1 m4 _ _ frame1); [| exact wm14]. intros w w_in. cbn [cells_size csize Nat.add] in w_in.
    apply ag4. unfold USTACK_TOP in *. lia. }
  assert (link4 : rw_cells asegs m4 (bv_unsigned sp - 16) [C8 s0; C8 ra]).
  { pose proof (rw_cells_skip m4 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] frame4) as tail4.
    cbn [cells_size csize Nat.add] in tail4. replace (bv_unsigned sp - 16) with (bv_unsigned sp + -48 + Z.of_nat 32) by lia. exact tail4. }
  assert (top4 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m4).
  { intros w w_in. transitivity (m1 w); [apply ag4; lia | apply mu1; cbn [outside]; split; [lia | exact I]]. }
  destruct (cl_chain_call (rt_cg RT Σ) e_get_state e_its SITE_eg_its m m4 ra s0 sp (Z_to_bv 64 (bv_unsigned sp + -48)) outer
              ctx_m (proj1 graph_m (SITE_eg_its, e_get_state) ltac:(unfold EG_SITES; cbn [app In]; repeat (first [left; reflexivity | right])))
              (proj2 graph_m (SITE_eg_its, e_its) ltac:(unfold EG_CALLS; cbn [app In]; repeat (first [left; reflexivity | right])))
              chain_m top4 link4 ltac:(rewrite sp48; lia) ltac:(unfold USTACK_TOP in *; lia)) as (ctx4 & chain4).
  assert (ctx4' : cg_ctx (rt_cg RT Σ3) e_its (bv_unsigned (Z_to_bv 64 SITE_eg_its) :: bv_unsigned ra :: outer))
    by (rewrite cg3, cg2, unsigned_lit by (unfold SITE_eg_its; lia); exact ctx4).
  assert (graph4 : cg_has (rt_cg RT Σ3) ITS_SITES ITS_CALLS).
  { rewrite cg3, cg2. apply (cg_has_weaken _ _ _ _ _ graph_m); vm_compute; reflexivity. }
  assert (win3 : rt_sp0 RT Σ3 - STACK_WIN <= lo) by (rewrite sp03, sp02; exact win_m).
  assert (callok4 : call_ok RT Σ3 m4 (Z_to_bv 64 (bv_unsigned sp + -48)) lo) by (cl_call_ok sp48 stk4 win3 spal_m 3).
  apply (cps_realizes asegs _ _ T c5
           (C_ITS Σ3 PMc (Z_to_bv 64 SITE_eg_its) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 TP_A) t0_4 t1_4 t2_4 sp (Z_to_bv 64 0) (Z_to_bv 64 0)
              (Z_to_bv 64 0) (Z_to_bv 64 ERR_DEL_THREAD_STATE) a3_4 a4_4 a5_4 a6_4 a7_4 (Z_to_bv 64 E) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 0)
              s5 s6 s7 s8 s9 s10 s11 t3_4 t4_4 t5_4 t6_4 F_4 fc_4 m4 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary kd u r0 g0 oldcb
              fd_only pm_stable eq_refl art4 inv4 callok4 ltac:(rewrite sp48; unfold RT_STACK; lia) ctx4' chain4 graph4
              ltac:(rewrite fr3, fr2; exact nfr_m) ltac:(rewrite lv3, lv2; cbn [length]; lia) ltac:(lia) env4
              dkey4 kd_range tslotd4 ub4 w784_4 w816_4 w848_4 ocb4) here5).
  intros c6 (Σ4 & N & H & G & SK & LK & D & u' & at6 & lv4 & fr4 & sp04 & cr4 & cg4 & fa4).
  destruct (ASTA_unpack RT Σ4 _ _ c6 at6)
    as (ms6 & (m6 & back6 & (art6 & inv6 & wm6 & stk6) & pres6 & env6 & tslotd6 & ub6 & w784_6 & w816_6 & w848_6 & ocb6
               & hcell6 & ncell6 & gcell6 & skcell6 & lkcell6 & dcell6) & here6).
  clear at6.
  destruct back6 as (t0_6 & t1_6 & t2_6 & a1_6 & a2_6 & a3_6 & a4_6 & a5_6 & a6_6 & a7_6 & t3_6 & t4_6 & t5_6 & t6_6 & F_6 & fc_6 & ->).
  rewrite (ret_pc_even SITE_eg_its) in here6 by (unfold SITE_eg_its; first [lia | reflexivity]).
  rewrite sp48 in stk6, pres6.
  assert (in_live4 : forall e, In e (rt_live RT Σ3) -> In e (rt_live RT Σ4)) by (rewrite lv4; intros e e_in; apply in_or_app; right; exact e_in).
  assert (pres6' : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (EG_W kd SA P) m m6).
  { intros w is_cl is_out. unfold EG_W in is_out. cbn [outside] in is_out. destruct is_out as (out_sa & out_p & out_g & out_mtl).
    transitivity (m4 w).
    - apply pres6; [| exact out_mtl].
      apply (aclient_mono _ _ _ _ _ _ _ is_cl); [exact in_live3 | rewrite fr3, fr2; exact (fun e e_in => e_in) | lia].
    - apply pres4'; [exact is_cl | cbn [outside]; split; [exact out_sa | split; [exact out_p | split; [exact out_g | exact I]]]]. }
  pose proof (wmono_trans asegs _ _ _ wm4' wm6) as wm6'.
  pose proof (wmono_trans asegs _ _ _ wm14 wm6) as wm16.
  assert (ag6 : agree_on (fun x => bv_unsigned sp - 48 <= x < USTACK_TOP) m1 m6).
  { intros w w_in. transitivity (m4 w); [| exact (ag4 w w_in)].
    apply pres6; [left; lia | unfold MTL_W, G_ALLOW_CUST; cbn [outside]; repeat split; try exact I; lia]. }
  (* the master key state seen by the walk to the second OPENSSL_init_crypto *)
  assert (mo6 : rw_cells asegs m6 MK_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m6 MK_KEY [C4 (Z_to_bv 64 k)]
                /\ rw_cells asegs m6 (TSD_MAIN + 8 * k) [C8 (Z_to_bv 64 MK)] /\ rw_cells asegs m6 (MK + 24) [C8 (Z_to_bv 64 SA)]).
  { repeat split; (eapply (keep _ m6 _ _ pres6' wm6'); [eassumption |]); intros x x_rng; cbn [cells_size csize Nat.add] in x_rng;
      (split; [first [apply stat_cl; lia | apply (live_cl MK 72); [exact mk_live | lia]] |
               unfold EG_W, MTL_W, G_ALLOW_CUST; cbn [outside]; repeat split; try exact I; lia]). }
  destruct mo6 as (monce6 & mkey6 & tslot6 & mksa6).
  assert (carry36 : forall a cs, rw_cells asegs m3 a cs -> (forall x, a <= x < a + Z.of_nat (cells_size cs) -> in_live (rt_live RT Σ) x) ->
            (forall x, a <= x < a + Z.of_nat (cells_size cs) -> 0x10007fff8000 <= x) -> rw_cells asegs m6 a cs).
  { intros a cs cells_a in_blk in_heap. apply (rw_cells_agree asegs m3 m6 a cs cells_a); [| exact (wmono_trans asegs _ _ _ wm4 wm6)].
    intros w w_in. pose proof (in_heap _ w_in) as w_heap. destruct (in_blk _ w_in) as (p & n & pn_in & w_pn). transitivity (m4 w).
    - apply pres6; [right; right; left; exists p, n; split; [exact (in_live3 _ pn_in) | exact w_pn] |].
      unfold MTL_W, G_ALLOW_CUST. cbn [outside]. repeat split; try exact I; lia.
    - apply pres4; [right; right; left; exists p, n; split; [exact (in_live2 _ pn_in) | exact w_pn] |].
      cbn [outside]. unfold G_ALLOW_CUST. split; [lia | exact I]. }
  assert (sahdr6 : rw_cells asegs m6 SA (sa_hdr (Z_to_bv 64 1) pad top1 (Z_to_bv 64 1) (Z_to_bv 64 P))).
  { apply (carry36 _ _ sahdr3); intros x x_rng; unfold sa_hdr in x_rng; cbn [cells_size csize Nat.add] in x_rng;
      [exists SA, 32; split; [exact sa_live | lia] | lia]. }
  assert (pslot6 : rw_cells asegs m6 P [C8 (Z_to_bv 64 (-1))]).
  { apply (carry36 _ _ pslot3); intros x x_rng; cbn [cells_size csize Nat.add] in x_rng; [exists P, 128; split; [exact p_live | lia] | lia]. }
  destruct (af_client_consts RT AF Σ4 m6 art6) as (_ & shadow6 & _ & _ & untouched6).
  assert (blk6 : forall p n, In (p, n) (rt_live RT Σ) -> acc asegs m6 p n).
  { intros p n pn_in. exact (proj2 (af_acc_live RT AF Σ4 m6 p n art6 (in_live4 _ (in_live3 _ pn_in)))). }
  (* back from ossl_init_thread_start: the new state is stored, then OPENSSL_init_crypto (load strings) is called *)
  pose proof (eg_w3 sp gp t0_6 t1_6 t2_6 a1_6 a2_6 a3_6 a4_6 a5_6 a6_6 a7_6 s5 s6 s7 s8 s9 s10 s11 t3_6 t4_6 t5_6 t6_6 F_6 fc_6 m6 lo k MK SA P E pad top1
                stk6 ltac:(lia) lo_heap sp_cap untouched6 shadow6 (proj1 monce6) (proj1 mkey6) k_range
                (afp_gsh_byte RT GOBJ AFP Σ4 m6 MK_KEY 4 MK_KEY art6 GO_mkey ltac:(lia) ltac:(lia) ltac:(reflexivity))
                (proj1 (TSD Σ4 m6 art6)) (proj1 tslot6) mk_heap mk_al ltac:(unfold STACK_WIN in *; lia) (blk6 _ _ mk_live) (proj1 mksa6)
                sa_heap sa_al ltac:(unfold STACK_WIN in *; lia) (blk6 _ _ sa_live) sahdr6
                p_heap p_al ltac:(unfold STACK_WIN in *; lia) (blk6 _ _ p_live) pslot6 sa_p ltac:(unfold USTACK_TOP in *; lia) inv6)
    as walk3.
  cl_lift walk3 here6 c7 at7.
  destruct (ASTA_unpack RT Σ4 _ _ c7 at7)
    as (ms7 & (t1_7 & a2_7 & a3_7 & top2 & m7 & -> & mu7 & wm7 & inv7 & stk7 & top2_val & sahdr7 & pslot7) & here7).
  clear at7.
  assert (win4 : rt_sp0 RT Σ4 - STACK_WIN <= lo) by (rewrite sp04, sp03, sp02; exact win_m).
  assert (art7 : ART RT Σ4 m7).
  { apply (af_frame RT AF Σ4 m6 m7 (bv_unsigned sp - 160) art6 ltac:(lia)); [| exact wm7].
    intros w not_cl. apply mu7. cbn [outside].
    assert (off_sa : ~ (SA + 8 <= bv_unsigned w < SA + 24)).
    { intros w_in. apply not_cl. right; right; left. exists SA, 32. split; [exact (in_live4 _ (in_live3 _ sa_live)) | lia]. }
    assert (off_p : ~ (P <= bv_unsigned w < P + 8)).
    { intros w_in. apply not_cl. right; right; left. exists P, 128. split; [exact (in_live4 _ (in_live3 _ p_live)) | lia]. }
    assert (off_stk : ~ (bv_unsigned sp - 160 <= bv_unsigned w < bv_unsigned sp - 48)).
    { intros w_in. apply not_cl. left. unfold USTACK_TOP in *. lia. }
    exact (conj off_stk (conj off_sa (conj off_p I))). }
  assert (pres7' : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (EG_W kd SA P) m m7).
  { intros w is_cl is_out. transitivity (m6 w); [| exact (pres6' w is_cl is_out)]. apply mu7.
    unfold EG_W in is_out. cbn [outside] in *. destruct is_out as (out_sa & out_p & _).
    split; [| split; [exact out_sa | split; [exact out_p | exact I]]].
    destruct (cl_split RT AF Σ m (bv_unsigned sp) 160 (bv_unsigned w) art_m ltac:(lia) ltac:(lia) is_cl); lia. }
  pose proof (wmono_trans asegs _ _ _ wm6' wm7) as wm7'.
  assert (ic7 : rw_cells asegs m7 G_IC_STOPPED [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m7 G_IC_OPTSDONE [C8 od]).
  { unfold G_IC_STOPPED, G_IC_OPTSDONE in *.
    split; (eapply (keep _ m7 _ _ pres7' wm7'); [eassumption |]); intros x x_rng; cbn [cells_size csize Nat.add] in x_rng;
      (split; [apply stat_cl; lia | unfold EG_W, MTL_W, G_ALLOW_CUST; cbn [outside]; repeat split; try exact I; lia]). }
  destruct ic7 as (stop7 & optd7).
  assert (callok7 : call_ok RT Σ4 m7 (Z_to_bv 64 (bv_unsigned sp + -48)) lo) by (cl_call_ok sp48 stk7 win4 spal_m 3).
  apply (cps_realizes asegs _ _ T c7
           (C_ICF Σ4 PMc (Z_to_bv 64 SITE_eg_icf) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 TP_A) t0_6 t1_7 t2_6 sp z64 (Z_to_bv 64 2) z64
              a2_7 a3_7 a4_6 a5_6 a6_6 a7_6 (Z_to_bv 64 E) (Z_to_bv 64 2147450880) z64 s5 s6 s7 s8 s9 s10 s11 t3_6 t4_6 t5_6 t6_6 F_6 fc_6 m7 lo od 2
              fd_only pm_stable eq_refl eq_refl ltac:(lia) od_bit art7 inv7 callok7 ltac:(rewrite sp48; unfold RT_STACK; lia)
              ltac:(rewrite fr4, fr3, fr2; exact nfr_m) ltac:(lia) stop7 optd7) here7).
  intros c8 (Σ5 & at8 & lv5 & fr5 & sp05 & cr5 & cg5).
  destruct (ASTA_unpack RT Σ5 _ _ c8 at8) as (ms8 & (m8 & back8 & (art8 & inv8 & wm8 & stk8) & pres8 & _ & _) & here8). clear at8.
  destruct back8 as (t0_8 & t1_8 & t2_8 & a1_8 & a2_8 & a3_8 & a4_8 & a5_8 & a6_8 & a7_8 & t3_8 & t4_8 & t5_8 & t6_8 & F_8 & fc_8 & ->).
  rewrite (ret_pc_even SITE_eg_icf) in here8 by (unfold SITE_eg_icf; first [lia | reflexivity]).
  rewrite sp48 in stk8, pres8.
  assert (ag8 : agree_on (fun x => bv_unsigned sp - 48 <= x < USTACK_TOP) m1 m8).
  { intros w w_in. transitivity (m7 w); [apply pres8; left; lia |]. transitivity (m6 w); [| exact (ag6 w w_in)].
    apply mu7. cbn [outside]. repeat split; try exact I; lia. }
  assert (frame8 : rw_cells asegs m8 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m1 m8 _ _ frame1); [| exact (wmono_trans asegs _ _ _ wm16 (wmono_trans asegs _ _ _ wm7 wm8))].
    intros w w_in. cbn [cells_size csize Nat.add] in w_in. apply ag8. unfold USTACK_TOP in *. lia. }
  (* back from OPENSSL_init_crypto: the frame is popped and the state is returned *)
  pose proof (eg_w4 ra sp gp (Z_to_bv 64 TP_A) t0_8 t1_8 t2_8 s0 s1 a1_8 a2_8 a3_8 a4_8 a5_8 a6_8 a7_8 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3_8 t4_8 t5_8 t6_8
                F_8 fc_8 m8 lo E stk8 ltac:(lia) lo_heap sp_cap frame8 inv8) as walk4.
  cl_lift walk4 here8 c9 at9.
  destruct (ASTA_unpack RT Σ5 _ _ c9 at9) as (ms9 & (m9 & -> & mu9 & wm9 & inv9 & stk9) & here9). clear at9.
  assert (art9 : ART RT Σ5 m9).
  { apply (af_frame RT AF Σ5 m8 m9 (bv_unsigned sp) art8 ltac:(rewrite sp05, sp04, sp03, sp02; lia)); [| exact wm9].
    intros w _. exact (mu9 w I). }
  assert (pres9 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (EG_W kd SA P) m m9).
  { intros w is_cl is_out. rewrite (mu9 w I). transitivity (m7 w); [| exact (pres7' w is_cl is_out)].
    apply pres8. apply (aclient_mono _ _ _ _ _ _ _ is_cl);
      [intros e e_in; exact (in_live4 _ (in_live3 _ e_in)) | rewrite fr4, fr3, fr2; exact (fun e e_in => e_in) | lia]. }
  pose proof (wmono_trans asegs _ _ _ wm7' (wmono_trans asegs _ _ _ wm8 wm9)) as wm9'.
  assert (env9 : cl_env m9 (Z_to_bv 8 1) canary).
  { pose proof (cl_env_seg _ m6 m7 _ canary env6 mu7 ltac:(cl_fp_lia)) as env7.
    pose proof (cl_env_agree m7 m8 _ _ env7 (fun w w_cl => pres8 w (acl_static _ _ _ _ (cl_cell_static _ w_cl)))) as env8.
    exact (cl_env_agree m8 m9 _ _ env8 (fun w _ => mu9 w I)). }
  (* what the later stages left in place *)
  assert (carry79 : forall a cs, rw_cells asegs m7 a cs ->
            (forall x, a <= x < a + Z.of_nat (cells_size cs) -> aclient (rt_live RT Σ4) (rt_frames RT Σ4) (bv_unsigned sp + -48) x) ->
            rw_cells asegs m9 a cs).
  { intros a cs cells_a cover. apply (rw_cells_agree asegs m7 m9 a cs cells_a); [| exact (wmono_trans asegs _ _ _ wm8 wm9)].
    intros w w_in. rewrite (mu9 w I). exact (pres8 w (cover _ w_in)). }
  assert (carry69 : forall a cs, rw_cells asegs m6 a cs ->
            (forall x, a <= x < a + Z.of_nat (cells_size cs) -> aclient (rt_live RT Σ4) (rt_frames RT Σ4) (bv_unsigned sp + -48) x /\
                       outside [(bv_unsigned sp - 160, bv_unsigned sp - 48); (SA + 8, SA + 24); (P, P + 8)] x) ->
            rw_cells asegs m9 a cs).
  { intros a cs cells_a cover. apply carry79; [| intros x x_in; exact (proj1 (cover _ x_in))].
    apply (rw_cells_agree asegs m6 m7 a cs cells_a); [| exact wm7]. intros w w_in. exact (mu7 w (proj2 (cover _ w_in))). }
  assert (fresh_apart : forall p n q l, In (p, n) [(N, 32); (D, 32); (LK, 40); (SK, 56); (G, 16); (H, 8); (E, 904)] ->
            In (q, l) (rt_live RT Σ) -> p + n <= q \/ q + l <= p).
  { intros p n q l pn_in ql_in. destruct (in_split _ _ ql_in) as (l1 & l2 & at_q).
    assert (live4_eq : rt_live RT Σ4 = ([(N, 32); (D, 32); (LK, 40); (SK, 56); (G, 16); (H, 8); (E, 904)] ++ l1) ++ (q, l) :: l2).
    { rewrite lv4, lv3, lv2, at_q. reflexivity. }
    destruct (af_live_disj RT AF Σ4 m6 q l p n _ _ art6 live4_eq ltac:(apply in_or_app; left; apply in_or_app; left; exact pn_in)); lia. }
  assert (fresh_live : forall p n, In (p, n) [(N, 32); (D, 32); (LK, 40); (SK, 56); (G, 16); (H, 8); (E, 904)] ->
            In (p, n) (rt_live RT Σ4) /\ p + n <= lo).
  { intros p n pn_in. assert (pn_in4 : In (p, n) (rt_live RT Σ4)).
    { rewrite lv4, lv3. clear - pn_in. cbn [In app] in *. tauto. }
    split; [exact pn_in4 |]. pose proof (af_live_range RT AF Σ4 m6 p n art6 pn_in4) as (_ & pn_win & _). lia. }
  assert (fresh_ok : forall p n x, In (p, n) [(N, 32); (D, 32); (LK, 40); (SK, 56); (G, 16); (H, 8); (E, 904)] -> p <= x < p + n ->
            aclient (rt_live RT Σ4) (rt_frames RT Σ4) (bv_unsigned sp + -48) x /\
            outside [(bv_unsigned sp - 160, bv_unsigned sp - 48); (SA + 8, SA + 24); (P, P + 8)] x).
  { intros p n x pn_in x_rng. destruct (fresh_live p n pn_in) as (pn_in4 & pn_lo).
    pose proof (fresh_apart p n SA 32 pn_in sa_live). pose proof (fresh_apart p n P 128 pn_in p_live).
    split; [right; right; left; exists p, n; split; [exact pn_in4 | exact x_rng] |].
    cbn [outside]. repeat split; try exact I; lia. }
  assert (stat_ok : forall x, 0x5a9d08 <= x < 0x6694d8 \/ 0xb8f190 <= x < 0xba3e98 \/ 0xbc52a0 <= x < 0xbc57d0 ->
            aclient (rt_live RT Σ4) (rt_frames RT Σ4) (bv_unsigned sp + -48) x /\
            outside [(bv_unsigned sp - 160, bv_unsigned sp - 48); (SA + 8, SA + 24); (P, P + 8)] x).
  { intros x x_rng. split; [right; left; apply client_static_intro; lia |]. cbn [outside]. repeat split; try exact I; lia. }
  assert (ecell6 : rw_cells asegs m6 E [CB 904 (repeat (Z_to_bv 8 0) 904)]).
  { assert (ecell4 : rw_cells asegs m4 E [CB 904 (repeat (Z_to_bv 8 0) 904)]).
    { split; [split; [cbn; split; [reflexivity | exact I] | exact zero4] | exact wr4]. }
    apply (rw_cells_agree asegs m4 m6 _ _ ecell4); [| exact wm6]. intros w w_in. cbn [cells_size csize Nat.add] in w_in.
    apply pres6; [right; right; left; exists E, 904; split; [exact e_in3 | lia] |].
    unfold MTL_W, G_ALLOW_CUST. cbn [outside]. repeat split; try exact I; lia. }
  assert (fresh9 : rw_cells asegs m9 E [CB 904 (repeat (Z_to_bv 8 0) 904)] /\ rw_cells asegs m9 H [C8 (Z_to_bv 64 N)]
                   /\ rw_cells asegs m9 N [C8 z64; C8 z64; C8 (Z_to_bv 64 ERR_DEL_THREAD_STATE); C8 z64]
                   /\ rw_cells asegs m9 G [C8 (Z_to_bv 64 SK); C8 (Z_to_bv 64 LK)]
                   /\ rw_cells asegs m9 SK (Fz_T_sk.sk_cells (Z_to_bv 64 1) z64 (Z_to_bv 64 D) (Z_to_bv 64 1) (Z_to_bv 64 4) z64 (Z_to_bv 64 TEV_CMP)
                                              (Z_to_bv 64 TEV_FREE) (Z_to_bv 64 TEV_COPY))
                   /\ rw_cells asegs m9 LK (mutex_cells z64 z64) /\ rw_cells asegs m9 D [C8 (Z_to_bv 64 H); CB 24 (repeat (Z_to_bv 8 0) 24)]).
  { assert (fresh_cell : forall p n a cs, In (p, n) [(N, 32); (D, 32); (LK, 40); (SK, 56); (G, 16); (H, 8); (E, 904)] ->
              rw_cells asegs m6 a cs -> p <= a -> a + Z.of_nat (cells_size cs) <= p + n -> rw_cells asegs m9 a cs).
    { intros p n a cs pn_in cells_a a_lo a_hi. apply (carry69 _ _ cells_a). intros x x_rng. apply (fresh_ok p n x pn_in). lia. }
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))));
      [ apply (fresh_cell E 904 _ _ ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ecell6)
      | apply (fresh_cell H 8 _ _ ltac:(cbn [In]; repeat (first [left; reflexivity | right])) hcell6)
      | apply (fresh_cell N 32 _ _ ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ncell6)
      | apply (fresh_cell G 16 _ _ ltac:(cbn [In]; repeat (first [left; reflexivity | right])) gcell6)
      | apply (fresh_cell SK 56 _ _ ltac:(cbn [In]; repeat (first [left; reflexivity | right])) skcell6)
      | apply (fresh_cell LK 40 _ _ ltac:(cbn [In]; repeat (first [left; reflexivity | right])) lkcell6)
      | apply (fresh_cell D 32 _ _ ltac:(cbn [In]; repeat (first [left; reflexivity | right])) dcell6) ];
      unfold Fz_T_sk.sk_cells, mutex_cells; cbn [cells_size csize Nat.add]; lia. }
  destruct fresh9 as (ecell9 & hcell9 & ncell9 & gcell9 & skcell9 & lkcell9 & dcell9).
  assert (its9 : rw_cells asegs m9 (TSD_MAIN + 8 * kd) [C8 (Z_to_bv 64 H)] /\ rw_cells asegs m9 (TP_A + -150) [C1 u']
                 /\ rw_cells asegs m9 0xb9f4a0 [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m9 0xb9f4c0 [C4 (Z_to_bv 64 1)]
                 /\ rw_cells asegs m9 0xb9f4e0 [C8 (Z_to_bv 64 G)] /\ rw_cells asegs m9 (TP_A + -96) [C8 oldcb]).
  { refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))); (eapply carry69; [eassumption |]); intros x x_rng;
      cbn [cells_size csize Nat.add] in x_rng; apply stat_ok; lia. }
  destruct its9 as (tslotd9 & ub9 & w784_9 & w816_9 & w848_9 & ocb9).
  assert (sahdr9 : rw_cells asegs m9 SA (sa_hdr (Z_to_bv 64 1) pad top2 (Z_to_bv 64 1) (Z_to_bv 64 P))).
  { apply (carry79 _ _ sahdr7). intros x x_rng. unfold sa_hdr in x_rng. cbn [cells_size csize Nat.add] in x_rng.
    right; right; left. exists SA, 32. split; [exact (in_live4 _ (in_live3 _ sa_live)) | lia]. }
  assert (pcells9 : rw_cells asegs m9 P [C8 (Z_to_bv 64 E); CB 120 jp]).
  { apply (rw_cells_join2 m9 P (C8 (Z_to_bv 64 E)) (CB 120 jp)).
    - apply (carry79 _ _ pslot7). intros x x_rng. cbn [cells_size csize Nat.add] in x_rng.
      right; right; left. exists P, 128. split; [exact (in_live4 _ (in_live3 _ p_live)) | lia].
    - apply (keep _ m9 _ _ pres9 wm9' pj_m). intros x x_rng. cbn [cells_size csize Nat.add] in x_rng.
      split; [apply (live_cl P 128); [exact p_live | lia] | unfold EG_W, MTL_W, G_ALLOW_CUST; cbn [outside]; repeat split; try exact I; lia]. }
  assert (mkcells9 : rw_cells asegs m9 MK [CB 24 jm1; C8 (Z_to_bv 64 SA); CB 40 jm2]).
  { assert (mk_part : forall a cs, rw_cells asegs m a cs -> MK <= a -> a + Z.of_nat (cells_size cs) <= MK + 72 -> rw_cells asegs m9 a cs).
    { intros a cs cells_a a_lo a_hi. apply (keep _ m9 _ _ pres9 wm9' cells_a). intros x x_rng.
      split; [apply (live_cl MK 72); [exact mk_live | lia] | unfold EG_W, MTL_W, G_ALLOW_CUST; cbn [outside]; repeat split; try exact I; lia]. }
    apply (proj2 (rw_cells_app m9 MK [CB 24 jm1] [C8 (Z_to_bv 64 SA); CB 40 jm2])). cbn [cells_size csize Nat.add].
    split; [apply (mk_part _ _ mkj1_m); cbn [cells_size csize Nat.add]; lia |].
    apply (rw_cells_join2 m9 (MK + Z.of_nat 24) (C8 (Z_to_bv 64 SA)) (CB 40 jm2)).
    - replace (MK + Z.of_nat 24) with (MK + 24) by lia. apply (mk_part _ _ mksa_m); cbn [cells_size csize Nat.add]; lia.
    - replace (MK + Z.of_nat 24 + Z.of_nat (csize (C8 (Z_to_bv 64 SA)))) with (MK + 32) by (cbn [csize]; lia).
      apply (mk_part _ _ mkj2_m); cbn [cells_size csize Nat.add]; lia. }
  apply finish_k. exists Σ5, E, N, H, G, SK, LK, D, u', top2.
  split.
  { apply (ASTA_conseq RT Σ5 PMc _ _ c9 here9). intros ms <-. exists m9.
    split; [exists t0_8, t1_8, t2_8, a1_8, a2_8, a3_8, a4_8, a5_8, a6_8, a7_8, t3_8, t4_8, t5_8, t6_8, F_8, fc_8; reflexivity |].
    split; [exact (conj art9 (conj inv9 (conj wm9' stk9))) |].
    split; [exact pres9 |]. split; [exact env9 |].
    split; [rewrite top2_val, top1_val; lia |].
    repeat (split; [eassumption |]). exact dcell9. }
  split; [rewrite lv5, lv4, lv3, lv2; reflexivity |].
  split; [rewrite fr5, fr4, fr3, fr2; reflexivity |].
  split; [rewrite sp05, sp04, sp03, sp02; reflexivity |].
  split; [lia |].
  split; [rewrite cg5, cg4, cg3, cg2; reflexivity |].
  change [(N, 32); (D, 32); (LK, 40); (SK, 56); (G, 16); (H, 8); (E, 904)] with ([(N, 32); (D, 32); (LK, 40); (SK, 56); (G, 16); (H, 8)] ++ [(E, 904)]).
  apply Forall_app. split; [exact fa4 |].
  constructor; [cbn [fst snd]; exact (conj e_heap (conj e_al e_top)) | constructor].
Qed.
End EgsiFirst.
