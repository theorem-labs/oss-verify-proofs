(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep FarCall.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit Fz_G_pkit.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Layout PLayout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_G_kit Fz_ckit Fz_env Fz_M_malloc Th_tsd Th_key Th_once Th_mutex Fz_T_lock Fz_T_master1 Fz_I3_gdcw Fz_I3_gdc Fz_I3_fxiw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).

Section Fxi.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_GDC : gdc_stmt RT.
(* [comment removed for export] *)
Hypothesis GO_dc : GOBJ 0xb9f580 328.

(* [comment removed for export] *)
Definition FXI_SITES : list (Z * Z) := (SITE_gx_gdc, e_gx) :: (SITE_fx_gx, e_fxi_ex) :: GDC_SITES.
Definition FXI_CALLS : list (Z * Z) := (SITE_gx_gdc, e_gdc) :: (SITE_fx_gx, e_gx) :: GDC_CALLS.

Definition fxi_stmt : Prop :=
  forall (Σ : rts RT) (PMc : Model -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word)
         (nk j : Z) (sh kold w r oldcb : word) (g1 : byte)
         (g2 g1_g2 g1_g3 g1_g4 g1_g5 g1_g6 g1_g7 g1_g8 g1_g9 g1_g10 g1_g11 g1_g12 g1_g13 g1_g14 g1_g15 g1_g16 g1_g17
          g1_g18 g1_g19 g1_g20 g1_g21 g1_g2_g2 g1_g5_od : word),
    a0 = Z_to_bv 64 0 -> a1 = Z_to_bv 64 (-1) -> tp = Z_to_bv 64 TP_A ->
    fdfs_only PMc -> mat_stable PMc ->
    ART RT Σ m -> mem_inv asegs m -> cl_env m lb canary ->
    Forall (fun blk : Z * Z => 0 < snd blk) (rt_live RT Σ) ->
    Z.of_nat (length (rt_live RT Σ)) + 124 <= LIVE_MAX ->
    (length (rt_frames RT Σ) + 1 < FRAMES_MAX)%nat ->
    GDC_COST <= rt_credit RT Σ ->
    call_ok RT Σ m sp lo -> lo + RT_STACK + 1312 <= bv_unsigned sp ->
    cg_ctx (rt_cg RT Σ) e_fxi_ex (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
    cg_has (rt_cg RT Σ) FXI_SITES FXI_CALLS ->
    rw_cells asegs m KEY_LOCK [C4 z64; C4 z64; C4 sh] ->
    rw_cells asegs m NEXT_KEY [C4 (Z_to_bv 64 nk)] ->
    (* nk is not negative, and nk is below 128 *)
    0 <= nk -> nk < 128 ->
    ro_cells asegs m (KEYS + 8 * nk) [C8 w] ->
    (j = nk /\ w = z64) \/ (j = (nk + 1) mod 128 /\ bv_unsigned w <> 0) -> 0 < j ->
    rw_cells asegs m (KEYS + 8 * j) [C8 z64] -> ro_cells asegs m (TSD_MAIN + 8 * j) [C8 z64] ->
    rw_cells asegs m 0xb9f720 [C4 kold] -> rw_cells asegs m 0xb9f740 [C4 z64] ->
    rw_cells asegs m 0xb9f760 [C4 r] -> rw_cells asegs m 0xb9f780 [C4 z64] ->
    rw_cells asegs m (TP_A + -96) [C8 oldcb] ->
    rw_cells asegs m 0xb9f200 [C1 (Z_to_bv 8 0)] -> rw_cells asegs m 0xb9f2a0 [C8 g1_g5_od] ->
    rw_cells asegs m 0xb9f2c0 [C4 (Z_to_bv 64 2)] -> rw_cells asegs m 0xb9f2e0 [C4 (Z_to_bv 64 1)] ->
    rw_cells asegs m 0xb9f560 [C1 g1] ->
    rw_cells asegs m 0xb9f580 [C8 g1_g2] -> rw_cells asegs m 0xb9f588 [C8 g1_g2_g2] ->
    rw_cells asegs m 0xb9f628 [C8 g1_g3] -> rw_cells asegs m 0xb9f630 [C8 g1_g4] -> rw_cells asegs m 0xb9f638 [C8 g1_g5] ->
    rw_cells asegs m 0xb9f640 [C8 g1_g6] -> rw_cells asegs m 0xb9f648 [C8 g1_g7] -> rw_cells asegs m 0xb9f650 [C8 g1_g8] ->
    rw_cells asegs m 0xb9f658 [C8 g1_g9] -> rw_cells asegs m 0xb9f660 [C8 g1_g10] -> rw_cells asegs m 0xb9f668 [C8 g1_g11] ->
    rw_cells asegs m 0xb9f670 [C8 g1_g12] -> rw_cells asegs m 0xb9f678 [C8 g1_g13] -> rw_cells asegs m 0xb9f680 [C8 g1_g14] ->
    rw_cells asegs m 0xb9f688 [C8 g1_g15] -> rw_cells asegs m 0xb9f690 [C8 g1_g16] -> rw_cells asegs m 0xb9f698 [C8 g1_g17] ->
    rw_cells asegs m 0xb9f6a0 [C8 g1_g18] -> rw_cells asegs m 0xb9f6a8 [C8 g1_g19] -> rw_cells asegs m 0xb9f6b0 [C8 g1_g20] ->
    rw_cells asegs m 0xb9f6b8 [C8 g1_g21] ->
    rw_cells asegs m 0xb9f7a0 [C4 g2] ->
    cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                                           F fc e_fxi m)))
      (fun c => exists (Σ' : rts RT) (lk xd : Z),
         ASTA RT Σ' PMc
           (fun ms => exists m' : mem,
              ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
              /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
              /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (GDC_W j) m m'
              /\ cl_env m' (Z_to_bv 8 1) canary
              /\ rw_cells asegs m' KEY_LOCK [C4 z64; C4 z64; C4 sh]
              /\ rw_cells asegs m' NEXT_KEY [C4 (Z_to_bv 64 j)]
              /\ rw_cells asegs m' (KEYS + 8 * j) [C8 (Z_to_bv 64 NODTOR)]
              /\ rw_cells asegs m' 0xb9f720 [C4 (Z_to_bv 64 j)]
              /\ rw_cells asegs m' 0xb9f740 [C4 (Z_to_bv 64 2)]
              /\ rw_cells asegs m' 0xb9f760 [C4 (Z_to_bv 64 1)]
              /\ rw_cells asegs m' 0xb9f780 [C4 (Z_to_bv 64 2)]
              /\ rw_cells asegs m' (TP_A + -96) [C8 oldcb]
              /\ rw_cells asegs m' 0xb9f560 [C1 (Z_to_bv 8 1)]
              /\ rw_cells asegs m' 0xb9f580 [C8 (Z_to_bv 64 lk)] /\ rw_cells asegs m' lk (mutex_cells z64 z64)
              /\ rw_cells asegs m' 0xb9f588 [C8 (Z_to_bv 64 xd)] /\ rw_cells asegs m' xd (mutex_cells z64 z64)
              /\ rw_cells asegs m' 0xb9f7a0 [C4 (Z_to_bv 64 1)])
           c
         /\ dc_blocks_ok RT Σ Σ' lk /\ dc_blocks_ok RT Σ Σ' xd /\ xd mod 16 = 0
         /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
         /\ rt_credit RT Σ' = rt_credit RT Σ - GDC_COST /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem fxi_cps : fxi_stmt.
Proof.
  unfold fxi_stmt.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo outer lb canary nk j sh kold w r oldcb g1 g2 g1_g2 g1_g3 g1_g4 g1_g5 g1_g6 g1_g7 g1_g8 g1_g9 g1_g10
    g1_g11 g1_g12 g1_g13 g1_g14 g1_g15 g1_g16 g1_g17 g1_g18 g1_g19 g1_g20 g1_g21 g1_g2_g2 g1_g5_od
    -> -> tp_main fds_only_pm stable_pm rt_m inv_m env_m sizes_pos live_room frame_room budget
    caller_ok depth_ok ctx_ex unwinds graph
    klock_m nextk_m nk_lo nk_hi slot_nk_m pick_j j_pos slot_j_m tsd_j_m
    kidx_m konce_m kret_m ctxonce_m cb_m
    rflag_m rod_m rtwo_m rone_m inited_m ctxlk_m ctxxd_m
    w628 w630 w638 w640 w648 w650 w658 w660 w668 w670 w678 w680 w688 w690 w698 w6a0 w6a8 w6b0 w6b8
    g2_m T c0 start finish.
  pose proof (conj nk_lo nk_hi) as nk_rng.
  pose proof caller_ok as (stk_m & lo_win & lo_rt & sp_top & sp_al).
  pose proof (af_sp0_win RT AF Σ m rt_m) as sp0_hi.
  unfold RT_STACK in lo_rt, depth_ok.
  assert (lo_hi : 17594333495296 <= lo) by (unfold STACK_WIN in lo_win; lia).
  assert (sp_cap : bv_unsigned sp <= 2 ^ 47) by (unfold USTACK_TOP in sp_top; lia).
  assert (j_rng : 0 <= j < 128).
  { destruct pick_j as [(j_nk & _) | (j_mod & _)]; [lia |].
    pose proof (Z.mod_pos_bound (nk + 1) 128 ltac:(lia)) as mod_rng. lia. }
  assert (sp80 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
  assert (sp64 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  (* from the entry to the call of e_gdc *)
  destruct (af_client_consts RT AF Σ m rt_m) as (_ & shb_m & _ & _ & ut_m).
  pose proof (fxi_w0 ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m lo stk_m lo_hi ltac:(lia) sp_cap ut_m shb_m inv_m) as walk_in.
  cl_lift walk_in start c1 at_c1.
  destruct (ASTA_unpack RT Σ _ _ c1 at_c1) as (st1 & reach1 & at1). clear at_c1.
  destruct reach1 as (j8 & m1 & -> & keep1 & grow1 & inv1 & gx_fr1 & ex_fr1 & stk1).
  assert (rt1 : ART RT Σ m1).
  { apply (cl_seg_ART RT AF Σ m m1 (bv_unsigned sp) 80 [] rt_m); try lia.
    - exact keep1.
    - intros x not_out. exfalso. exact (not_out I).
    - exact grow1. }
  assert (env1 : cl_env m1 lb canary) by (apply (cl_env_seg _ m m1 lb canary env_m keep1); cl_fp_lia).
  assert (call1 : call_ok RT Σ m1 (Z_to_bv 64 (bv_unsigned sp + -80)) lo).
  { unfold call_ok. rewrite sp80. split; [exact stk1 |]. split; [exact lo_win |]. unfold RT_STACK.
    split; [lia |]. split; [unfold USTACK_TOP in *; lia |].
    replace (bv_unsigned sp + -80) with (bv_unsigned sp + -5 * 16) by lia. rewrite Z_mod_plus_full. exact sp_al. }
  assert (depth1 : lo + RT_STACK + 1232 <= bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80))) by (rewrite sp80; unfold RT_STACK; lia).
  (* return-address chain at the call of e_gdc *)
  pose proof graph as (sites_fxi & calls_fxi). unfold FXI_SITES in sites_fxi. unfold FXI_CALLS in calls_fxi.
  assert (graph_gdc : cg_has (rt_cg RT Σ) GDC_SITES GDC_CALLS).
  { split; intros e e_in; [apply sites_fxi | apply calls_fxi]; right; right; exact e_in. }
  assert (site_ex : In (SITE_fx_gx, e_fxi_ex) (cg_site (rt_cg RT Σ))) by (apply sites_fxi; right; left; reflexivity).
  assert (call_ex : In (SITE_fx_gx, e_gx) (cg_call (rt_cg RT Σ))) by (apply calls_fxi; right; left; reflexivity).
  assert (site_gx : In (SITE_gx_gdc, e_gx) (cg_site (rt_cg RT Σ))) by (apply sites_fxi; left; reflexivity).
  assert (call_gx : In (SITE_gx_gdc, e_gdc) (cg_call (rt_cg RT Σ))) by (apply calls_fxi; left; reflexivity).
  assert (ra_slot1 : rw_cells asegs m1 (bv_unsigned sp - 16) [C8 s0; C8 ra]).
  { pose proof (rw_cells_skip m1 (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] ex_fr1) as upper.
    cbn [cells_size csize Nat.add] in upper. replace (bv_unsigned sp - 16) with (bv_unsigned sp + -64 + Z.of_nat 48) by lia. exact upper. }
  assert (stay1 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m1).
  { apply (agree_of_munch _ m m1 _ keep1). intros x x_in. cbn [outside]. split; [lia | exact I]. }
  destruct (cl_chain_call (rt_cg RT Σ) e_fxi_ex e_gx SITE_fx_gx m m1 ra s0 sp (Z_to_bv 64 (bv_unsigned sp + -64)) outer
              ctx_ex site_ex call_ex unwinds stay1 ra_slot1 ltac:(rewrite sp64; lia) sp_top) as (ctx_gx & chain_gx).
  assert (fx_lit : bv_unsigned (Z_to_bv 64 SITE_fx_gx) = SITE_fx_gx) by (apply unsigned_lit; unfold SITE_fx_gx; lia).
  assert (gx_lit : bv_unsigned (Z_to_bv 64 SITE_gx_gdc) = SITE_gx_gdc) by (apply unsigned_lit; unfold SITE_gx_gdc; lia).
  rewrite <- fx_lit in ctx_gx.
  assert (gx_link1 : rw_cells asegs m1 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) - 16) [C8 sp; C8 (Z_to_bv 64 SITE_fx_gx)]).
  { rewrite sp64. replace (bv_unsigned sp + -64 - 16) with (bv_unsigned sp + -80) by lia. exact gx_fr1. }
  destruct (cl_chain_call (rt_cg RT Σ) e_gx e_gdc SITE_gx_gdc m1 m1 (Z_to_bv 64 SITE_fx_gx) sp
              (Z_to_bv 64 (bv_unsigned sp + -64)) (Z_to_bv 64 (bv_unsigned sp + -80)) (bv_unsigned ra :: outer)
              ctx_gx site_gx call_gx chain_gx (agree_refl _ m1) gx_link1
              ltac:(rewrite sp80, sp64; lia) ltac:(rewrite sp64; unfold USTACK_TOP in *; lia)) as (ctx_gdc & chain_gdc).
  rewrite <- gx_lit in ctx_gdc.
  (* the callee, by its contract *)
  pose proof C_GDC as gdc_spec. unfold gdc_stmt in gdc_spec.
  apply (gdc_spec Σ PMc (Z_to_bv 64 SITE_gx_gdc) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2
           (Z_to_bv 64 (bv_unsigned sp + -64)) s1 (Z_to_bv 64 0) (Z_to_bv 64 g_shadow_memory_dynamic_address) (Z_to_bv 64 (-1))
           a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) (Z_to_bv 64 0) (Z_to_bv 64 SHB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m1 lo (bv_unsigned (Z_to_bv 64 SITE_fx_gx) :: bv_unsigned ra :: outer) lb canary nk j sh kold w r oldcb
           g1 g2 g1_g2 g1_g3 g1_g4 g1_g5 g1_g6 g1_g7 g1_g8 g1_g9 g1_g10 g1_g11 g1_g12 g1_g13 g1_g14 g1_g15 g1_g16 g1_g17
           g1_g18 g1_g19 g1_g20 g1_g21 g1_g2_g2 g1_g5_od);
    [ first
        [ exact at1
        | assumption
        | eapply (Fz_G_kit2.wg_keep_seg_nw _ m m1);
            [ eassumption | exact keep1
            | intros x x_in; cbn [cells_size csize Nat.add] in x_in; cbn [outside]; split; [lia | exact I] ]
        | eapply (wg_keep_seg_ro _ m m1);
            [ eassumption | exact keep1
            | intros x x_in; cbn [cells_size csize Nat.add] in x_in; cbn [outside]; split; [lia | exact I] ] ] ..
    | intros c2 back ].
  destruct back as (Σ' & lk & xd & at_back & blocks & xd_blocks & xd_al & frames_eq & sp0_eq & credit_eq & cg_eq).
  destruct (ASTA_unpack RT Σ' _ _ c2 at_back) as (st2 & ret2 & at2). clear at_back.
  destruct ret2 as (m2 & shape2 & after2 & kept2 & env2 & inited2 & ctxlk2 & ctxxd2 & lkmx2 & xdmx2
                    & kidx2 & konce2 & kret2 & ctxonce2 & g2one2 & cb2 & slotj2 & nextk2 & klock2).
  destruct shape2 as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & F2 & fc2 & ->).
  destruct after2 as (rt2 & inv2 & stk2).
  rewrite sp80 in stk2, kept2.
  rewrite (ret_pc_even SITE_gx_gdc) in at2 by (unfold SITE_gx_gdc; first [lia | reflexivity]).
  (* after the return: take and release the lock at 0xb9f588 *)
  destruct (af_client_consts RT AF Σ' m2 rt2) as (_ & shb2 & _ & _ & ut2).
  assert (gx_fr2 : rw_cells asegs m2 (bv_unsigned sp + -80) [C8 sp; C8 (Z_to_bv 64 SITE_fx_gx)]).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ gx_fr1). apply (agree_of_pres_fp _ _ _ _ m1 m2 _ kept2).
    intros x x_in. cbn [cells_size csize Nat.add] in x_in. split; [apply acl_stack; unfold USTACK_TOP in *; lia |].
    unfold GDC_W, G_ALLOW_CUST. cbn [outside]. repeat split; lia. }
  assert (ex_fr2 : rw_cells asegs m2 (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ ex_fr1). apply (agree_of_pres_fp _ _ _ _ m1 m2 _ kept2).
    intros x x_in. cbn [cells_size csize Nat.add] in x_in. split; [apply acl_stack; unfold USTACK_TOP in *; lia |].
    unfold GDC_W, G_ALLOW_CUST. cbn [outside]. repeat split; lia. }
  pose proof blocks as (news & live_split & _ & _ & lk_new).
  pose proof xd_blocks as (news_x & live_split_x & _ & _ & xd_new).
  assert (xd_live : In (xd, 40) (rt_live RT Σ')) by (rewrite live_split_x; apply in_or_app; left; exact xd_new).
  assert (gsh2 : ro_cells asegs m2 GSH_GLOBAL [C1 (Z_to_bv 8 0)])
    by exact (afp_gsh_byte RT GOBJ AFP Σ' m2 0xb9f580 328 0xb9f588 rt2 GO_dc ltac:(lia) ltac:(lia) eq_refl).
  assert (xd_hi : 17594333495296 <= xd) by exact (afp_live_hi RT GOBJ AFP Σ' m2 xd 40 rt2 xd_live ltac:(lia)).
  destruct (af_live_range RT AF Σ' m2 xd 40 rt2 xd_live) as (_ & xd_low & _).
  rewrite sp0_eq in xd_low.
  pose proof (fxi_w1 sp gp tp x0 x1 x2 s1 y1 y2 y3 y4 y5 y6 y7 s5 s6 s7 s8 s9 s10 s11 x3 x4 x5 x6 ra s0 s2 s3 s4
                F2 fc2 m2 lo xd j8 stk2 lo_hi ltac:(lia) sp_cap ut2 shb2 gx_fr2 ex_fr2 gsh2 ctxxd2 xdmx2 xd_hi
                ltac:(lia) xd_al inv2) as walk_out.
  cl_lift walk_out at2 c3 at_c3.
  apply finish. exists Σ', lk, xd.
  refine (conj _ (conj blocks (conj xd_blocks (conj xd_al (conj frames_eq (conj sp0_eq (conj credit_eq cg_eq))))))).
  apply (ASTA_conseq RT Σ' PMc _ _ c3 at_c3). intros st3 out3.
  destruct out3 as (z1 & z2 & z3 & z4 & z5 & m3 & -> & keep3 & grow3 & inv3 & xdmx3 & stk3).
  exists m3.
  (* the state at the return to the caller *)
  assert (keep3' : munch ([(xd + 4, xd + 8)] ++ [(bv_unsigned sp - 176, bv_unsigned sp)]) m2 m3).
  { intros a a_out. apply keep3. cbn [outside app] in a_out |- *. tauto. }
  assert (rt3 : ART RT Σ' m3).
  { apply (wg_seg_ART RT AF Σ' m2 m3 (bv_unsigned sp) 176 [(xd + 4, xd + 8)] rt2);
      [rewrite sp0_eq; lia | lia | exact keep3' | | exact grow3].
    intros x hit. right. exists xd, 40. split; [exact xd_live |]. cbn [outside] in hit. lia. }
  assert (pres3 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (GDC_W j) m m3).
  { apply (pres_fp_trans _ _ _ _ m m2 m3); [apply (pres_fp_trans _ _ _ _ m m1 m2) |].
    - apply (pres_fp_sub _ _ _ _ _ _ _ [] m m1 (cl_seg_pres RT AF Σ m m1 (bv_unsigned sp) 80 [] rt_m ltac:(lia) ltac:(lia) keep1)).
      intros x acl _. split; [exact acl | exact I].
    - apply (pres_fp_sub _ _ _ _ _ _ _ _ m1 m2 kept2). intros x acl away. split; [| exact away].
      apply (aclient_mono _ _ _ _ _ _ _ acl); [exact (fun e e_in => e_in) | exact (fun e e_in => e_in) | lia].
    - apply (wg_seg_pres RT AF _ _ Σ' m2 m3 (bv_unsigned sp) 176 [(xd + 4, xd + 8)] _ rt2 ltac:(rewrite sp0_eq; lia) ltac:(lia) keep3').
      + intros x acl. apply (aclient_mono _ _ _ _ _ _ _ acl); [| rewrite frames_eq; exact (fun e e_in => e_in) | lia].
        intros e e_in. rewrite live_split. apply in_or_app. right. exact e_in.
      + intros x acl _. cbn [outside]. split; [| exact I].
        pose proof (wg_newchunk_apart RT AF Σ Σ' m2 news_x xd 40 (bv_unsigned sp) x rt2 live_split_x xd_new frames_eq sp0_eq
                      ltac:(lia) ltac:(lia) acl) as off_block.
        lia. }
  assert (env3 : cl_env m3 (Z_to_bv 8 1) canary) by (apply (cl_env_seg _ m2 m3 _ canary env2 keep3); cl_fp_lia).
  assert (lkmx3 : rw_cells asegs m3 lk (mutex_cells z64 z64)).
  { destruct (Z.eq_dec lk xd) as [same | apart]; [rewrite same; exact xdmx3 |].
    assert (lk_live : In (lk, 40) (rt_live RT Σ')) by (rewrite live_split; apply in_or_app; left; exact lk_new).
    apply in_split in lk_live as (l1 & l2 & cut_eq).
    assert (xd_rest : In (xd, 40) (l1 ++ l2)).
    { pose proof xd_live as xd_in. rewrite cut_eq in xd_in.
      apply in_app_or in xd_in as [left_hit | [head_hit | right_hit]].
      - apply in_or_app. left. exact left_hit.
      - exfalso. injection head_hit as lk_xd. exact (apart lk_xd).
      - apply in_or_app. right. exact right_hit. }
    pose proof (wg_live_apart RT AF Σ' m2 l1 lk 40 l2 xd 40 rt2 cut_eq xd_rest) as gap.
    assert (lk_in : In (lk, 40) (rt_live RT Σ')) by (rewrite cut_eq; apply in_or_app; right; left; reflexivity).
    destruct (af_live_range RT AF Σ' m2 lk 40 rt2 lk_in) as (_ & lk_low & _). rewrite sp0_eq in lk_low.
    apply (Fz_G_kit2.wg_keep_seg_nw _ m2 m3 _ _ lkmx2 keep3).
    intros x x_in. cbn [mutex_cells cells_size csize Nat.add] in x_in. cbn [outside]. repeat split; lia. }
  split; [exists x0, x1, x2, z1, z2, z3, z4, z5, y6, y7, x3, x4, x5, x6, F2, fc2; reflexivity |].
  split; [exact (conj rt3 (conj inv3 stk3)) |].
  split; [exact pres3 |].
  split; [exact env3 |].
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj lkmx3 (conj _ (conj xdmx3 _))))))))))))).
  all: eapply (Fz_G_kit2.wg_keep_seg_nw _ m2 m3);
    [ eassumption | exact keep3
    | intros x x_in; cbn [cells_size csize Nat.add] in x_in; cbn [outside]; repeat split; lia ].
Qed.
End Fxi.
