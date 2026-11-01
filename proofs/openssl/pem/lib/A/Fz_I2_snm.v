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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout Th_mutex Th_mutex_init Th_cond I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_G_kit Fz_ckit Fz_M_malloc Fz_M_zalloc Fz_env Fz_M_locknew Fz_M_aligned Fz_M_aligned_array Fz_G_CRYPTO_calloc Fz_G_ossl_lib_ctx_get_concrete Fz_T_rcuw Fz_T_rcu Fz_I2_anl Fz_I2_htw Fz_I2_htnew Fz_G_OPENSSL_sk_new_null Fz_G_OPENSSL_sk_set_cmp_thunks Fz_G_OPENSSL_sk_set_copy_thunks Fz_G_OPENSSL_sk_set_thunks Fz_I2_nmw Fz_I2_namemap Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac tslia ::= wp_tslia.
Notation TP_A := (0xba3ef0)%Z (only parsing).
Local Ltac zgo p := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 p) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep; lfix
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [ifF | ifT | ubs_if] end).
Local Ltac zsh := cbv beta; try change (bv_unsigned (Z_to_bv 8 0)) with 0; try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0).

Definition e_stored_namemap_new : Z := 0x218168.
Definition SITE_snm_nm : Z := 0x21818c.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition snm_cells (ht lk sk : Z) : list cell :=
  [C1 (Z_to_bv 8 1); CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 ht); C8 (Z_to_bv 64 lk); C8 (Z_to_bv 64 sk); C8 (Z_to_bv 64 0)].

(* [comment removed for export] *)
Definition snm_w0_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem) (pad : list byte),
    ms = MS (mkR (Z_to_bv 64 SITE_snm_nm) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 0x7fff8000) a0
                 (Z_to_bv 64 g_shadow_memory_dynamic_address) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_namemap_new) fc None m' (seg_rom asegs)
    /\ rw_cells asegs m' (bv_unsigned sp + -32) [CB 8 pad; C8 s1; C8 s0; C8 ra]
    /\ stk asegs m' lo (bv_unsigned sp + -32)
    /\ mem_inv asegs m'
    /\ munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m'
    /\ wmono asegs m m'.

Lemma snm_w0 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 32 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] -> mem_inv asegs m ->
  evt asegs (snm_w0_post ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_stored_namemap_new) fc None m (seg_rom asegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    free_below room floor cap untouched shoff_cell inv0.
  assert (fp_shadow : sh_fp [(bv_unsigned sp + -32, bv_unsigned sp)]) by sh_fp_lia.
  assert (fp_img : ut_fp [(bv_unsigned sp + -32, bv_unsigned sp)]) by ut_fp_lia.
  generalize (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m); intro keeps.
  generalize (wmono_refl asegs m); intro grows.
  unfold e_stored_namemap_new. unfold g_shadow_memory_dynamic_address in shoff_cell.
  carve_frame 32%nat free_below.
  zgo 0x2181cc.
  apply evt_done. unfold snm_w0_post.
  refine (ex_intro _ _ (ex_intro _ _ (conj _ (conj FR (conj free_below (conj inv0 (conj keeps grows))))))).
  reflexivity.
Qed.

(* [comment removed for export] *)
Definition snm_w1_post (ra0 sp gp tp s0' s1' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (nm ht lk sk lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists m' : mem,
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 nm) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ rw_cells asegs m' nm (snm_cells ht lk sk)
    /\ acc asegs m' nm 40
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ mem_inv asegs m'
    /\ munch [(nm, nm + 1)] m m'
    /\ wmono asegs m m'.

Lemma snm_w1 : forall ra0 sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (s0' s1' : word)
    (F : bvmap 5 word) fc (m : mem) (nm ht lk sk lo : Z) (j : list byte),
  lo <= bv_unsigned sp - 32 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  0x10007fff8000 <= nm -> nm + 40 <= 2^47 -> nm mod 8 = 0 -> nm + 40 <= lo ->
  stk asegs m lo (bv_unsigned sp + -32) ->
  rw_cells asegs m (bv_unsigned sp + -32) [CB 8 j; C8 s1'; C8 s0'; C8 ra0] ->
  rw_cells asegs m nm [C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 ht); C8 (Z_to_bv 64 lk); C8 (Z_to_bv 64 sk); C8 (Z_to_bv 64 0)] ->
  acc asegs m nm 40 -> mem_inv asegs m ->
  evt asegs (snm_w1_post ra0 sp gp tp s0' s1' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc nm ht lk sk lo m)
    (MS (mkR (Z_to_bv 64 SITE_snm_nm) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 nm) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_snm_nm) fc None m (seg_rom asegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0' s1' F fc m nm ht lk sk lo j
    room floor cap nm_floor nm_cap nm_al nm_below below frame obj obj_acc inv0.
  assert (whole_stack : stk asegs m lo (bv_unsigned sp)).
  { generalize (stk_release asegs m lo _ _ below frame ltac:(lia)).
    cbn [cells_size csize Nat.add]. now replace (bv_unsigned sp + -32 + Z.of_nat 32) with (bv_unsigned sp) by lia. }
  pose proof (acc_shadow0 m nm 40 nm obj_acc nm_al ltac:(lia) ltac:(lia) ltac:(rewrite Z.sub_diag; lia)) as obj_shadow.
  assert (fp_img : ut_fp [(nm, nm + 1)]) by ut_fp_lia.
  assert (fp_shadow : sh_fp [(nm, nm + 1)]) by sh_fp_lia.
  generalize (wmono_refl asegs m); intro grows.
  generalize (munch_refl [(nm, nm + 1)] m); intro keeps.
  unfold SITE_snm_nm.
  zgo 0.
  apply evt_done. unfold snm_w1_post, snm_cells.
  eexists.
  refine (conj eq_refl (conj obj (conj (acc_munch_sh _ _ _ _ _ obj_acc keeps fp_shadow ltac:(lia) nm_cap)
            (conj whole_stack (conj inv0 (conj keeps grows)))))).
Qed.

Lemma NM_COST_nonneg : 0 <= NM_COST.
Proof.
  unfold NM_COST, HT_COST. pose proof (wg_mcost_nonneg 40). pose proof (wg_mcost_nonneg 96). pose proof (wg_mcost_nonneg 24).
  pose proof (wg_mcost_nonneg NB_BYTES). pose proof (wg_mcost_nonneg 264). pose proof (wg_mcost_nonneg 16). pose proof (wg_mcost_nonneg 56). lia.
Qed.

Section StoredNamemapNew.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_NM : namemap_new_stmt RT.

Definition SNM_SITES : list (Z * Z) := (SITE_snm_nm, e_stored_namemap_new) :: NM_SITES.
Definition SNM_CALLS : list (Z * Z) := (SITE_snm_nm, e_namemap_new) :: NM_CALLS.

(* [comment removed for export] *)
Definition stored_namemap_new_stmt : Prop :=
  forall (Σ : rts RT) (PMc : Model -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc ->
  bv_unsigned a0 <> 0 ->
  tp = Z_to_bv 64 TP_A ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  lo + RT_STACK + 800 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_stored_namemap_new (bv_unsigned ra :: outer) ->
  uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) SNM_SITES SNM_CALLS ->
  (length (rt_frames RT Σ) + 1 < FRAMES_MAX)%nat ->
  Z.of_nat (length (rt_live RT Σ)) + 8 < LIVE_MAX ->
  NM_COST <= rt_credit RT Σ ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_stored_namemap_new m)))
    (fun c => exists (Σ' : rts RT) (p lk h hlk md nb rl rq sk : Z),
       ASTA RT Σ' PMc
         (fun ms => exists m' : mem,
            ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
            /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
            /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
            /\ cl_env m' (Z_to_bv 8 1) canary
            /\ rw_cells asegs m' p (snm_cells h lk sk)
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

Theorem stored_namemap_new_cps : stored_namemap_new_stmt.
Proof.
  unfold stored_namemap_new_stmt.
  intros S0 PM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary
    fd_ok stable ctx_nz tp_val art0 inv0 cok0 depth0 ctx0 chain0 graph0 nfr0 nlive0 credit0 env0 T c start finish.
  subst tp.
  destruct cok0 as (stk0 & lo_win & lo_room & sp_top & sp_al).
  unfold RT_STACK, STACK_WIN, USTACK_TOP in lo_win, lo_room, sp_top, depth0.
  pose proof (af_sp0_win RT AF S0 m art0) as sp0_floor.
  destruct (af_client_consts RT AF S0 m art0) as (_ & shoff0 & _ & _ & ut0).
  assert (sp1_val : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  (* prologue up to the call of namemap_new *)
  pose proof (snm_w0 ra sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                stk0 ltac:(lia) ltac:(lia) ltac:(lia) ut0 shoff0 inv0) as walk0.
  cl_lift walk0 start c1 at1.
  destruct (ASTA_unpack RT S0 PM _ c1 at1) as (ms1 & (m1 & pad1 & -> & frame1 & stk1 & inv1 & keep1 & grow1) & at1'). clear at1.
  assert (above1 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m1).
  { apply (agree_of_munch _ m m1 _ keep1). intros x x_above. cbn [outside]. split; [lia | exact I]. }
  assert (art1 : ART RT S0 m1).
  { apply (af_frame RT AF S0 m m1 (bv_unsigned sp - 32) art0 ltac:(unfold STACK_WIN; lia)); [| exact grow1].
    intros a not_client. apply keep1. cbn [outside]. split; [| exact I].
    intros in_frame. apply not_client, acl_stack. unfold USTACK_TOP. lia. }
  assert (env1 : cl_env m1 lb canary).
  { apply (cl_env_agree m m1 _ _ env0). intros a a_cl. apply keep1. cbn [outside].
    pose proof (client_static_range _ (cl_cell_static _ a_cl)) as a_low. unfold SEGTOP_A in a_low. split; [lia | exact I]. }
  assert (link1 : rw_cells asegs m1 (bv_unsigned sp - 16) [C8 s0; C8 ra]).
  { pose proof (rw_cells_skip m1 (bv_unsigned sp + -32) [CB 8 pad1; C8 s1] [C8 s0; C8 ra] frame1) as upper.
    cbn [cells_size csize Nat.add] in upper. now replace (bv_unsigned sp - 16) with (bv_unsigned sp + -32 + Z.of_nat 16) by lia. }
  assert (site_in : In (SITE_snm_nm, e_stored_namemap_new) (cg_site (rt_cg RT S0)))
    by (apply (cg_has_site _ _ _ _ _ graph0); unfold SNM_SITES; left; reflexivity).
  assert (call_in : In (SITE_snm_nm, e_namemap_new) (cg_call (rt_cg RT S0)))
    by (apply (cg_has_call _ _ _ _ _ graph0); unfold SNM_CALLS; left; reflexivity).
  destruct (cl_chain_call (rt_cg RT S0) e_stored_namemap_new e_namemap_new SITE_snm_nm m m1 ra s0 sp
              (Z_to_bv 64 (bv_unsigned sp + -32)) outer ctx0 site_in call_in chain0 above1 link1
              ltac:(rewrite sp1_val; lia) ltac:(unfold USTACK_TOP; lia)) as (ctx1 & chain1).
  rewrite <- (unsigned_lit SITE_snm_nm) in ctx1 by (unfold SITE_snm_nm; lia).
  assert (cok1 : call_ok RT S0 m1 (Z_to_bv 64 (bv_unsigned sp + -32)) lo).
  { unfold call_ok. rewrite sp1_val. refine (conj stk1 _). unfold RT_STACK, STACK_WIN, USTACK_TOP. repeat split; lia. }
  assert (graph1 : cg_has (rt_cg RT S0) NM_SITES NM_CALLS)
    by (apply (cg_has_weaken _ _ _ _ _ graph0); vm_compute; reflexivity).
  (* the namemap itself *)
  refine (C_NM S0 PM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 lo (bv_unsigned ra :: outer) lb canary
            fd_ok stable ctx_nz eq_refl art1 inv1 cok1 ltac:(rewrite sp1_val; unfold RT_STACK; lia) ctx1 chain1 graph1
            nfr0 nlive0 credit0 env1 T c1 at1' _).
  intros c2 post2.
  destruct post2 as (S1 & p & lk & h & hlk & md & nb & rl & rq & sk & at2 & tail2).
  pose proof tail2 as (live1 & frames1 & sp01 & _ & p_pos & p_al & p_top & _).
  unfold USTACK_TOP in p_top.
  destruct (ASTA_unpack RT S1 PM _ c2 at2)
    as (ms2 & (m2 & ret2 & after2 & pres2 & env2 & nm2 & nm_acc2 & lk2 & lk_acc2 & h2 & h_acc2 & hlk2 & hlk_acc2 & md2 & md_acc2
               & nb2 & nb_acc2 & rl2 & rl48 & rl88 & rl128 & rl176 & rl216 & rl_acc2 & rq2 & rq_acc2 & sk2 & sk_acc2) & at2').
  clear at2.
  destruct ret2 as (t0r & t1r & t2r & a1r & a2r & a3r & a4r & a5r & a6r & a7r & t3r & t4r & t5r & t6r & F2 & fc2 & ->).
  destruct after2 as (art2 & inv2 & grow2 & stk2).
  rewrite (ret_pc_even SITE_snm_nm) in at2' by (unfold SITE_snm_nm; lia).
  rewrite sp1_val in stk2, pres2.
  assert (p_live : In (p, 40) (rt_live RT S1)) by (rewrite live1; do 8 right; left; reflexivity).
  pose proof (afp_live_hi RT GOBJ AFP S1 m2 p 40 art2 p_live ltac:(lia)) as p_high.
  pose proof (af_live_range RT AF S1 m2 p 40 art2 p_live) as (_ & p_under & _).
  rewrite sp01 in p_under. unfold STACK_WIN in p_under.
  assert (frame2 : rw_cells asegs m2 (bv_unsigned sp + -32) [CB 8 pad1; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m1 m2 _ _ frame1); [| exact grow2].
    apply (agree_of_pres_fp _ _ _ _ m1 m2 _ pres2). intros x x_in. cbn [cells_size csize Nat.add] in x_in.
    split; [apply acl_stack; unfold USTACK_TOP; lia | cbn [outside]; unfold G_ALLOW_CUST; split; [lia | exact I]]. }
  assert (nm_bytes : rw_cells asegs m2 p [C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 h); C8 (Z_to_bv 64 lk);
                                          C8 (Z_to_bv 64 sk); C8 (Z_to_bv 64 0)]).
  { destruct nm2 as ((nm_shape & nm_content) & nm_writable).
    refine (conj (conj _ nm_content) nm_writable). cbv. repeat constructor. }
  (* epilogue: mark the namemap stored, restore the frame, return *)
  pose proof (snm_w1 ra sp gp (Z_to_bv 64 TP_A) t0r t1r t2r a1r a2r a3r a4r a5r a6r a7r s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3r t4r t5r t6r s0 s1
                F2 fc2 m2 p h lk sk lo pad1
                ltac:(lia) ltac:(lia) ltac:(lia) p_high ltac:(lia) (wg_mod16_8 p p_al) ltac:(lia)
                stk2 frame2 nm_bytes nm_acc2 inv2) as walk1.
  cl_lift walk1 at2' c3 at3.
  destruct (ASTA_unpack RT S1 PM _ c3 at3) as (ms3 & (m3 & -> & nm3 & nm_acc3 & stk3 & inv3 & keep3 & grow3) & at3'). clear at3.
  assert (art3 : ART RT S1 m3).
  { apply (af_frame RT AF S1 m2 m3 (bv_unsigned sp) art2); [rewrite sp01; unfold STACK_WIN; lia | | exact grow3].
    intros a not_client. apply keep3. cbn [outside]. split; [| exact I].
    intros on_nm. apply not_client. apply (acl_live _ _ _ p 40); [exact p_live | lia]. }
  assert (env3 : cl_env m3 (Z_to_bv 8 1) canary).
  { apply (cl_env_agree m2 m3 _ _ env2). intros a a_cl. apply keep3. cbn [outside].
    pose proof (client_static_range _ (cl_cell_static _ a_cl)) as a_low. unfold SEGTOP_A in a_low. split; [lia | exact I]. }
  assert (pres_all : rt_pres_fp (rt_live RT S0) (rt_frames RT S0) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m3).
  { apply (pres_fp_trans _ _ _ _ m m2 m3); [apply (pres_fp_trans _ _ _ _ m m1 m2) |].
    - apply (pres_fp_of_munch _ _ _ _ _ m m1 keep1). intros x x_client _. cbn [outside]. split; [| exact I].
      destruct (cl_split RT AF S0 m (bv_unsigned sp) 32 x art0 ltac:(unfold STACK_WIN; lia) ltac:(lia) x_client); lia.
    - apply (pres_fp_sub _ _ _ _ _ _ _ _ m1 m2 pres2). intros x x_client x_out. split; [| exact x_out].
      apply (aclient_mono _ _ _ _ _ _ _ x_client (fun e e_in => e_in) (fun e e_in => e_in)). lia.
    - apply (pres_fp_of_munch _ _ _ _ _ m2 m3 keep3). intros x x_client _. cbn [outside]. split; [| exact I].
      intros on_nm.
      apply (wg_newchunk_apart RT AF S0 S1 m2 [(sk, 56); (rq, 16); (rl, 264); (nb, NB_BYTES); (md, 24); (hlk, 40); (h, 96); (lk, 40); (p, 40)]
               p 40 (bv_unsigned sp) x art2 live1 ltac:(do 8 right; left; reflexivity) frames1 sp01
               ltac:(unfold STACK_WIN; lia) ltac:(lia) x_client).
      lia. }
  (* the other new objects are apart from the byte the epilogue writes *)
  assert (keep_new : forall q n X k cs, rw_cells asegs m2 X cs -> Z.of_nat (cells_size cs) = k ->
            In (q, n) [(sk, 56); (rq, 16); (rl, 264); (nb, NB_BYTES); (md, 24); (hlk, 40); (h, 96); (lk, 40)] ->
            q <= X -> X + k <= q + n -> rw_cells asegs m3 X cs).
  { intros q n X k cs src size_k q_new X_lo X_hi.
    pose proof (af_live_disj RT AF S1 m2 p 40 q n [(sk, 56); (rq, 16); (rl, 264); (nb, NB_BYTES); (md, 24); (hlk, 40); (h, 96); (lk, 40)]
                  (rt_live RT S0) art2 live1 (in_or_app _ _ _ (or_introl q_new))) as apart.
    apply (rw_cells_agree asegs m2 m3 _ _ src); [| exact grow3].
    apply (agree_of_munch _ m2 m3 _ keep3). intros x x_in. cbn [outside]. split; [| exact I]. lia. }
  assert (acc_new : forall q n, In (q, n) (rt_live RT S1) -> acc asegs m3 q n)
    by (intros q n q_in; exact (proj2 (af_acc_live RT AF S1 m3 q n art3 q_in))).
  pose proof (keep_new lk 40 lk 40 _ lk2 eq_refl ltac:(do 7 right; left; reflexivity) ltac:(lia) ltac:(lia)) as lk3.
  pose proof (keep_new h 96 h 96 _ h2 eq_refl ltac:(do 6 right; left; reflexivity) ltac:(lia) ltac:(lia)) as h3.
  pose proof (keep_new hlk 40 hlk 40 _ hlk2 eq_refl ltac:(do 5 right; left; reflexivity) ltac:(lia) ltac:(lia)) as hlk3.
  pose proof (keep_new md 24 md 24 _ md2 eq_refl ltac:(do 4 right; left; reflexivity) ltac:(lia) ltac:(lia)) as md3.
  pose proof (keep_new nb NB_BYTES nb NB_BYTES _ nb2 eq_refl ltac:(do 3 right; left; reflexivity) ltac:(lia) ltac:(lia)) as nb3.
  pose proof (keep_new rl 264 rl 48 _ rl2 eq_refl ltac:(do 2 right; left; reflexivity) ltac:(lia) ltac:(lia)) as rl3.
  pose proof (keep_new rl 264 (rl + 48) 40 _ rl48 eq_refl ltac:(do 2 right; left; reflexivity) ltac:(lia) ltac:(lia)) as rl48'.
  pose proof (keep_new rl 264 (rl + 88) 40 _ rl88 eq_refl ltac:(do 2 right; left; reflexivity) ltac:(lia) ltac:(lia)) as rl88'.
  pose proof (keep_new rl 264 (rl + 128) 48 _ rl128 eq_refl ltac:(do 2 right; left; reflexivity) ltac:(lia) ltac:(lia)) as rl128'.
  pose proof (keep_new rl 264 (rl + 176) 40 _ rl176 eq_refl ltac:(do 2 right; left; reflexivity) ltac:(lia) ltac:(lia)) as rl176'.
  pose proof (keep_new rl 264 (rl + 216) 48 _ rl216 eq_refl ltac:(do 2 right; left; reflexivity) ltac:(lia) ltac:(lia)) as rl216'.
  pose proof (keep_new rq 16 rq 16 _ rq2 eq_refl ltac:(right; left; reflexivity) ltac:(lia) ltac:(lia)) as rq3.
  pose proof (keep_new sk 56 sk 56 _ sk2 eq_refl ltac:(left; reflexivity) ltac:(lia) ltac:(lia)) as sk3.
  clear lk2 h2 hlk2 md2 nb2 rl2 rl48 rl88 rl128 rl176 rl216 rq2 sk2 nm2 nm_bytes keep_new.
  apply finish. exists S1, p, lk, h, hlk, md, nb, rl, rq, sk. split; [| exact tail2].
  apply (ASTA_conseq RT S1 PM _ _ c3 at3'). intros ms <-. exists m3.
  split; [do 16 eexists; reflexivity |].
  split; [exact (conj art3 (conj inv3 (conj (wmono_trans _ _ _ _ grow1 (wmono_trans _ _ _ _ grow2 grow3)) stk3))) |].
  repeat (split; [solve [eassumption | apply acc_new; rewrite live1; repeat (first [left; reflexivity | right])] |]).
  apply acc_new. rewrite live1. left. reflexivity.
Qed.
End StoredNamemapNew.
