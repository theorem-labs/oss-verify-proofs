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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout Th_mutex Th_mutex_init Th_cond I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_G_kit Fz_ckit Fz_M_malloc Fz_M_zalloc Fz_env Fz_G_CRYPTO_calloc Fz_G_ossl_lib_ctx_get_concrete Fz_T_rcuw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Notation TP_A := (0xba3ef0)%Z (only parsing).

Section RcuLockNew.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis SM1 : stack_malloc_contract RT 1.
Hypothesis MSET : memset_icontract RT e_asan_memset.
Hypothesis C_CZ : crypto_zalloc_env_stmt RT.
Hypothesis C_CALLOC : CRYPTO_calloc_stmt RT.

Definition RCU_SITES : list (Z * Z) :=
  [(SITE_rcu_zalloc, e_rcu_lock_new); (SITE_rcu_calloc, e_rcu_lock_new); (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)].
Definition RCU_CALLS : list (Z * Z) :=
  [(SITE_rcu_zalloc, e_CRYPTO_zalloc); (SITE_rcu_calloc, e_CRYPTO_calloc); (SITE_rcu_calloc, e_CRYPTO_zalloc); (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)].

(* [comment removed for export] *)
Definition rcu_lock_new_stmt : Prop :=
  forall (Σ : rts RT) (PMc : Model -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 1 ->
  bv_unsigned a1 <> 0 ->
  tp = Z_to_bv 64 TP_A ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  lo + RT_STACK + 464 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_rcu_lock_new (bv_unsigned ra :: outer) ->
  uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) RCU_SITES RCU_CALLS ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat ->
  Z.of_nat (length (rt_live RT Σ)) + 1 < LIVE_MAX ->
  1 <= rt_credit RT Σ ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_rcu_lock_new m)))
    (fun c => exists (Σ' : rts RT) (p q : Z),
       ASTA RT Σ' PMc
         (fun ms => exists m' : mem,
            ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
            /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
            /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
            /\ cl_env m' (Z_to_bv 8 1) canary
            /\ rw_cells asegs m' p (rcu_head a1 q)
            /\ rw_cells asegs m' (p + 48) (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
            /\ rw_cells asegs m' (p + 88) (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
            /\ rw_cells asegs m' (p + 128) cond_cells
            /\ rw_cells asegs m' (p + 176) (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
            /\ rw_cells asegs m' (p + 216) cond_cells
            /\ acc asegs m' p 264
            /\ rw_cells asegs m' q [CB 16 (repeat (Z_to_bv 8 0) 16)]
            /\ acc asegs m' q 16) c
       /\ rt_live RT Σ' = (q, 16) :: (p, 264) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ
       /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - 1
       /\ 0 < p /\ p mod 16 = 0 /\ p + 264 < USTACK_TOP
       /\ 0 < q /\ q mod 16 = 0 /\ q + 16 < USTACK_TOP
       /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem rcu_lock_new_cps : rcu_lock_new_stmt.
Proof.
  unfold rcu_lock_new_stmt.
  intros S0 PM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary
    fdo mst nw_one ctx_nz tp_is art_e inv_e cok_e room_e cgx_e chain_e cgh_e nfr_e nlv_e cred_e env_e.
  subst a0 tp.
  intros T c start finish.
  destruct cok_e as (stk_e & win_e & rts_e & top_e & al_e).
  pose proof (af_sp0_win RT AF S0 m art_e) as sp0_e.
  pose proof (af_sp0_range RT AF S0 m art_e) as (_ & sp0_hi).
  pose proof (af_client_consts RT AF S0 m art_e) as (_ & shoff_e & _ & uar_e & ut_e).
  assert (pad_ex : exists pad, (pad = 0 \/ pad = 16) /\ bv_unsigned sp mod 32 = pad)
    by (exists (bv_unsigned sp mod 32); split; [clear - al_e; lia | reflexivity]).
  destruct pad_ex as (pad & pad_cases & pad_def).
  unfold RT_STACK, STACK_WIN, USTACK_TOP in *.
  assert (lo_big : 140735332483072 <= lo) by (clear - win_e sp0_e; lia).
  assert (u_spn : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -160 - pad)) = bv_unsigned sp + -160 - pad)
    by (apply unsigned_lit; clear - pad_cases top_e lo_big room_e; lia).
  (* entry segment: frame set-up, up to the fake-stack request *)
  pose proof (rcu_w0 ra sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pad
                pad_cases pad_def stk_e ltac:(clear - room_e; lia) ltac:(clear - lo_big; lia) ltac:(clear - top_e; lia) ut_e shoff_e uar_e inv_e) as walk.
  cl_lift walk start c1 at1.
  destruct (ASTA_unpack RT S0 PM _ c1 at1) as (ms1 & (a1x & a2x & junk0 & m1 & -> & mu1 & wm1 & inv1 & saved1 & gap1 & stk1) & at1'). clear at1.
  assert (art1 : ART RT S0 m1).
  { apply (af_frame RT AF S0 m m1 lo art_e win_e); [| exact wm1].
    intros a far. apply mu1. cbn [outside]. split; [| exact I]. intros inside.
    apply far, acl_stack. unfold USTACK_TOP. clear - inside room_e top_e. lia. }
  assert (cok1 : call_ok RT S0 m1 (Z_to_bv 64 (bv_unsigned sp + -160 - pad)) lo).
  { unfold call_ok. rewrite u_spn. split; [exact stk1|].
    unfold RT_STACK, STACK_WIN, USTACK_TOP. clear - win_e room_e top_e al_e pad_def pad_cases. repeat split; lia. }
  (* the fake frame *)
  refine (SM1 S0 PM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 lo fdo mst
            (or_intror (or_introl eq_refl)) eq_refl nfr_e cred_e art1 inv1 cok1 T c1 at1' _).
  intros c2 post2.
  destruct post2 as (S1 & fr & at2 & frm1 & liv1 & sp01 & crd1 & fr_pos & fr_al64 & fr_top & cg1).
  destruct (ASTA_unpack RT S1 PM _ c2 at2) as (ms2 & (m2 & ret2 & aft2 & pres2 & wf2 & wsh2) & at2'). clear at2.
  destruct ret2 as (t0b & t1b & t2b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & F2 & fc2 & ->).
  destruct aft2 as (art2 & inv2 & wm2 & stk2).
  rewrite (ret_pc_even SITE_rcu_smalloc) in at2' by (unfold SITE_rcu_smalloc; lia).
  rewrite u_spn in stk2, pres2.
  change (fs_size 1 - 8) with 120 in wf2. change (fs_size 1 / 8) with 16 in wsh2. unfold shad, SHB in wsh2.
  assert (fr_in1 : In (fr, 1%nat) (rt_frames RT S1)) by (rewrite frm1; left; reflexivity).
  pose proof (af_frames_range RT AF S1 m2 fr 1 art2 fr_in1) as (_ & fr_win & _ & fr_apart).
  pose proof (af_frames_hi RT AF S1 m2 fr 1 art2 fr_in1) as fr_hi.
  pose proof (af_frames_align RT AF S1 m2 fr 1 art2 fr_in1) as (_ & fr_seg).
  change (fs_size 1) with 128 in fr_win, fr_hi, fr_apart, fr_top. unfold SEGTOP_A in fr_seg. unfold STACK_WIN in fr_win.
  rewrite sp01 in fr_win.
  assert (saved2 : rw_cells asegs m2 (bv_unsigned sp + -160)
                     [CB 56 junk0; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m1 m2 _ _ saved1); [| exact wm2].
    apply (agree_of_pres _ _ _ _ _ _ pres2). intros x xin. cbn [cells_size csize Nat.add] in xin.
    apply acl_stack. unfold USTACK_TOP. clear - xin pad_cases top_e. lia. }
  assert (gap2 : stk asegs m2 (bv_unsigned sp + -160 - pad) (bv_unsigned sp + -160)).
  { apply (stk_agree asegs m1 m2 _ _ gap1); [| exact wm2].
    apply (agree_of_pres _ _ _ _ _ _ pres2). intros x xin.
    apply acl_stack. unfold USTACK_TOP. clear - xin pad_cases top_e. lia. }
  pose proof (af_client_consts RT AF S1 m2 art2) as (_ & _ & _ & _ & ut2).
  destruct (wr_at_rw_CB m2 fr 120 wf2 ltac:(lia)) as (fj2 & fcell2).
  destruct (wr_at_rw_CB m2 (fr / 8 + 2147450880) 16 wsh2 ltac:(lia)) as (sj2 & scell2).
  (* frame descriptor and shadow poisoning, up to the memset of the local *)
  pose proof (rcu_w1 ra sp gp (Z_to_bv 64 TP_A) t0b t1b t2b a1b a2b a3b a4b a5b a6b a7b s2 a1 (Z_to_bv 64 1) s5 s6 s7 s8 s9 s11 t3b t4b t5b t6b
                s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F2 fc2 m2 fr lo pad junk0 fj2 sj2
                pad_cases fr_pos ltac:(clear - fr_win sp0_hi; lia) ltac:(clear - fr_seg; lia) ltac:(clear - fr_hi; lia)
                ltac:(clear - lo_big room_e; lia) ltac:(clear - top_e; lia) ltac:(clear - fr_win win_e sp01 room_e; lia)
                ut2 saved2 fcell2 scell2 inv2) as walk.
  cl_lift walk at2' c3 at3.
  destruct (ASTA_unpack RT S1 PM _ c3 at3) as (ms3 & (a3c & junk3 & fj3 & sj3 & m3 & -> & mu3 & wm3 & inv3 & saved3 & fcell3 & scell3) & at3'). clear at3.
  assert (win1 : rt_sp0 RT S1 - STACK_WIN <= lo) by (rewrite sp01; exact win_e).
  assert (art3 : ART RT S1 m3).
  { apply (af_frame RT AF S1 m2 m3 lo art2 win1); [| exact wm3].
    intros a far. apply mu3. cbn [outside].
    split; [| split; [| split; [| exact I]]]; intros inside; apply far.
    - apply (acl_frame _ _ _ fr 1%nat); [exact fr_in1|]. change (fs_size 1) with 128. clear - inside. lia.
    - apply (acl_fshadow _ _ _ fr 1%nat); [exact fr_in1|]. unfold shad, SHB. change (fs_size 1) with 128. clear - inside. lia.
    - apply acl_stack. unfold USTACK_TOP. clear - inside room_e top_e. lia. }
  assert (stk3 : stk asegs m3 lo (bv_unsigned sp + -160 - pad)).
  { apply (stk_munch _ m2 m3 _ _ stk2 mu3 wm3). intros x xin. cbn [outside].
    clear - xin fr_win win_e lo_big sp0_hi pad_cases. repeat split; lia. }
  assert (gap3 : stk asegs m3 (bv_unsigned sp + -160 - pad) (bv_unsigned sp + -160)).
  { apply (stk_munch _ m2 m3 _ _ gap2 mu3 wm3). intros x xin. cbn [outside].
    clear - xin fr_win win_e lo_big room_e pad_cases sp0_hi. repeat split; lia. }
  pose proof (stk_release asegs m3 _ _ _ gap3 saved3 ltac:(clear - pad_cases; lia)) as full3.
  cbn [cells_size csize Nat.add] in full3.
  replace (bv_unsigned sp + -160 + Z.of_nat 160) with (bv_unsigned sp) in full3 by lia.
  assert (chk3 : checked_dst RT S1 m3 (Z_to_bv 64 (bv_unsigned sp + -160 - pad)) (bv_unsigned sp + -160 - pad + 40) 16).
  { unfold checked_dst. rewrite u_spn. split; [intros _; split | split].
    - apply (af_acc_stack RT AF S1 m3 _ _ art3); unfold STACK_WIN, USTACK_TOP; rewrite ?sp01; clear - win_e room_e top_e pad_cases; lia.
    - unfold rng_class. right; right; left. rewrite sp01. unfold STACK_WIN, USTACK_TOP. clear - win_e room_e top_e pad_cases. lia.
    - intros i irange. apply acl_stack. unfold USTACK_TOP. clear - irange top_e pad_cases. lia.
    - apply (stk_wr_at m3 _ _ _ _ full3); clear - pad_cases; lia. }
  assert (cok3 : call_ok RT S1 m3 (Z_to_bv 64 (bv_unsigned sp + -160 - pad)) lo).
  { unfold call_ok. rewrite u_spn, sp01. split; [exact stk3|].
    unfold RT_STACK, STACK_WIN, USTACK_TOP. clear - win_e room_e top_e al_e pad_def pad_cases. repeat split; lia. }
  (* clearing the 16-byte local *)
  refine (MSET S1 PM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3
            (bv_unsigned sp + -160 - pad + 40) 16 (Z_to_bv 8 0) lo fdo mst eq_refl eq_refl eq_refl
            ltac:(clear - lo_big top_e room_e pad_cases; lia) ltac:(lia) chk3 art3 inv3 cok3 T c3 at3' _).
  intros c4 post4. unfold icpt_post in post4.
  destruct (ASTA_unpack RT S1 PM _ c4 post4) as (ms4 & (m4 & ret4 & aft4 & pres4 & zero4) & at4'). clear post4.
  destruct ret4 as (t0c & t1c & t2c & a1c & a2c & a3d & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & F4 & fc4 & ->).
  destruct aft4 as (art4 & inv4 & wm4 & stk4).
  rewrite (ret_pc_even SITE_rcu_memset) in at4' by (unfold SITE_rcu_memset; lia).
  rewrite u_spn in stk4, pres4.
  assert (fcell4 : rw_cells asegs m4 fr [CB 120 fj3]).
  { apply (rw_cells_agree asegs m3 m4 _ _ fcell3); [| exact wm4].
    apply (agree_of_pres_ex _ _ _ _ _ _ _ _ pres4). intros x xin. cbn [cells_size csize] in xin. split.
    - apply (acl_frame _ _ _ fr 1%nat); [exact fr_in1|]. change (fs_size 1) with 128. clear - xin. lia.
    - clear - xin fr_win win_e room_e pad_cases. lia. }
  assert (scell4 : rw_cells asegs m4 (fr / 8 + 2147450880) [CB 16 sj3]).
  { apply (rw_cells_agree asegs m3 m4 _ _ scell3); [| exact wm4].
    apply (agree_of_pres_ex _ _ _ _ _ _ _ _ pres4). intros x xin. cbn [cells_size csize] in xin. split.
    - apply (acl_fshadow _ _ _ fr 1%nat); [exact fr_in1|]. unfold shad, SHB. change (fs_size 1) with 128. clear - xin. lia.
    - clear - xin fr_win win_e room_e pad_cases lo_big sp0_hi. lia. }
  (* the library context lookup, up to the lock allocation *)
  pose proof (rcu_w2 sp gp (Z_to_bv 64 TP_A) t0c t1c t2c (Z_to_bv 64 (bv_unsigned sp + -160 - pad + 40)) a1c a2c a3d a4c a5c a6c a7c a1 s5 s6 s7 s11
                t3c t4c t5c t6c F4 fc4 m4 fr lo pad fj3 sj3
                pad_cases ltac:(clear - room_e; lia) ltac:(clear - lo_big; lia) ltac:(clear - top_e; lia) fr_pos
                ltac:(clear - fr_win win_e; lia) ltac:(clear - fr_hi; lia) ctx_nz stk4 fcell4 scell4 inv4) as walk.
  cl_lift walk at4' c5 at5.
  destruct (ASTA_unpack RT S1 PM _ c5 at5)
    as (ms5 & (t0d & t1d & t2d & a3e & a4d & a5d & a6d & a7d & t3d & t4d & t5d & t6d & fj5 & sj5 & m5 & -> & mu5 & wm5 & inv5 & stk5 & fcell5 & scell5) & at5').
  clear at5.
  (* what the caller may rely on stays put *)
  assert (split_x : forall x, aclient (rt_live RT S0) (rt_frames RT S0) (bv_unsigned sp) x -> bv_unsigned sp <= x \/ x < lo).
  { intros x kx. destruct (aclient_split RT AF S0 m (bv_unsigned sp) x art_e kx) as [hi_x | lo_x]; [left; exact hi_x | right].
    unfold STACK_WIN in lo_x. clear - lo_x win_e. lia. }
  assert (apart_fr : forall x, aclient (rt_live RT S0) (rt_frames RT S0) (bv_unsigned sp) x ->
                     ~ (fr <= x < fr + 128) /\ ~ (fr / 8 + 2147450880 <= x < fr / 8 + 2147450880 + 16)).
  { intros x kx.
    destruct (newframe_apart RT AF S0 S1 m2 fr 1 (bv_unsigned sp) x art2 frm1 liv1 sp01 ltac:(unfold STACK_WIN; clear - win_e room_e; lia) kx)
      as (not_f & not_s).
    change (fs_size 1) with 128 in not_f, not_s. unfold shad, SHB in not_s. split; [exact not_f | clear - not_s; lia]. }
  assert (mono1 : forall x, aclient (rt_live RT S0) (rt_frames RT S0) (bv_unsigned sp) x ->
                  aclient (rt_live RT S1) (rt_frames RT S1) (bv_unsigned sp + -160 - pad) x).
  { intros x kx. apply (aclient_mono _ _ _ _ _ _ _ kx).
    - intros e e_in. rewrite liv1. exact e_in.
    - intros e e_in. rewrite frm1. right. exact e_in.
    - clear - pad_cases. lia. }
  assert (ag05 : agree_on (aclient (rt_live RT S0) (rt_frames RT S0) (bv_unsigned sp)) m m5).
  { apply (agree_trans _ m m4 m5); [apply (agree_trans _ m m3 m4); [apply (agree_trans _ m m2 m3); [apply (agree_trans _ m m1 m2)|]|]|].
    - apply (agree_of_munch _ m m1 _ mu1). intros x kx. cbn [outside].
      destruct (split_x x kx) as [hx | hx]; clear - hx room_e; (split; [lia | exact I]).
    - apply (agree_of_pres _ _ _ m1 m2 _ pres2). intros x kx.
      apply (aclient_mono _ _ _ _ _ _ _ kx); [tauto | tauto | clear - pad_cases; lia].
    - apply (agree_of_munch _ m2 m3 _ mu3). intros x kx. cbn [outside].
      destruct (apart_fr x kx) as (nf & ns). destruct (split_x x kx) as [hx | hx];
      clear - hx nf ns fr_win win_e room_e sp0_hi; repeat split; lia.
    - apply (agree_of_pres_ex _ _ _ _ _ m3 m4 _ pres4). intros x kx. split; [exact (mono1 x kx)|].
      destruct (split_x x kx) as [hx | hx]; clear - hx room_e pad_cases; lia.
    - apply (agree_of_munch _ m4 m5 _ mu5). intros x kx. cbn [outside].
      destruct (apart_fr x kx) as (nf & ns). destruct (split_x x kx) as [hx | hx];
      clear - hx nf ns room_e pad_cases; repeat split; lia. }
  assert (art5 : ART RT S1 m5).
  { apply (af_frame RT AF S1 m4 m5 lo art4 win1); [| exact wm5].
    intros a far. apply mu5. cbn [outside].
    split; [| split; [| split; [| exact I]]]; intros inside; apply far.
    - apply (acl_frame _ _ _ fr 1%nat); [exact fr_in1|]. change (fs_size 1) with 128. clear - inside. lia.
    - apply (acl_fshadow _ _ _ fr 1%nat); [exact fr_in1|]. unfold shad, SHB. change (fs_size 1) with 128. clear - inside. lia.
    - apply acl_stack. unfold USTACK_TOP. clear - inside room_e top_e pad_cases. lia. }
  pose proof (proj1 (rw_cells_app m3 (bv_unsigned sp + -160) [CB 56 junk3]
                       [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) saved3) as (_ & tail3).
  cbn [cells_size csize Nat.add] in tail3.
  replace (bv_unsigned sp + -160 + Z.of_nat 56) with (bv_unsigned sp + -104) in tail3 by lia.
  assert (tail5 : rw_cells asegs m5 (bv_unsigned sp + -104)
                    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply (wg_keep_seg _ m4 m5); [| exact mu5 | exact wm5 |].
    - apply (rw_cells_agree asegs m3 m4 _ _ tail3); [| exact wm4].
      apply (agree_of_pres_ex _ _ _ _ _ m3 m4 _ pres4). intros x xin. cbn [cells_size csize Nat.add] in xin. split.
      + apply acl_stack. unfold USTACK_TOP. clear - xin top_e pad_cases. lia.
      + clear - xin pad_cases. lia.
    - intros x xin. cbn [cells_size csize Nat.add] in xin. cbn [outside].
      clear - xin fr_win fr_pos win_e room_e pad_cases sp0_hi lo_big. repeat split; lia. }
  pose proof (rw_cells_skip m5 (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1]
                [C8 s0; C8 ra] tail5) as top5.
  cbn [cells_size csize Nat.add] in top5.
  replace (bv_unsigned sp + -104 + Z.of_nat 88) with (bv_unsigned sp - 16) in top5 by lia.
  assert (cgh1 : cg_has (rt_cg RT S1) RCU_SITES RCU_CALLS) by (rewrite cg1; exact cgh_e).
  assert (cgx1 : cg_ctx (rt_cg RT S1) e_rcu_lock_new (bv_unsigned ra :: outer)) by (rewrite cg1; exact cgx_e).
  destruct (cl_chain_call (rt_cg RT S1) e_rcu_lock_new e_CRYPTO_zalloc SITE_rcu_zalloc m m5 ra s0 sp
              (Z_to_bv 64 (bv_unsigned sp + -160 - pad)) outer cgx1
              (cg_has_site _ _ _ _ _ cgh1 ltac:(unfold RCU_SITES; left; reflexivity))
              (cg_has_call _ _ _ _ _ cgh1 ltac:(unfold RCU_CALLS; left; reflexivity))
              chain_e
              (agree_sub _ _ m m5 ag05 ltac:(intros x xr; apply acl_stack; exact xr))
              top5 ltac:(rewrite u_spn; clear - pad_cases; lia) ltac:(unfold USTACK_TOP; clear - top_e; lia)) as (cgx5 & chain5).
  rewrite <- (unsigned_lit SITE_rcu_zalloc) in cgx5 by (unfold SITE_rcu_zalloc; lia).
  assert (env5 : cl_env m5 lb canary).
  { apply (cl_env_agree m m5 _ _ env_e). intros a ca. apply ag05. apply acl_static. exact (cl_cell_static _ ca). }
  assert (cok5 : call_ok RT S1 m5 (Z_to_bv 64 (bv_unsigned sp + -160 - pad)) lo).
  { unfold call_ok. rewrite u_spn, sp01. split; [exact stk5|].
    unfold RT_STACK, STACK_WIN, USTACK_TOP. clear - win_e room_e top_e al_e pad_def pad_cases. repeat split; lia. }
  assert (cg_inner : cg_has (rt_cg RT S1) [(SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)]
                       [(SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)])
    by (apply (cg_has_weaken _ _ _ _ _ cgh1); vm_compute; reflexivity).
  (* the lock object *)
  refine (C_CZ S1 PM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 264 lo (bv_unsigned ra :: outer) lb canary
            fdo mst eq_refl eq_refl ltac:(lia) art5 inv5 cok5
            ltac:(rewrite u_spn; unfold RT_STACK; clear - room_e pad_cases; lia) cgx5 chain5
            cg_inner
            ltac:(rewrite liv1; clear - nlv_e; lia)
            ltac:(rewrite crd1; change (mcost 264) with 0; clear - cred_e; lia)
            env5 T c5 at5' _).
  intros c6 post6.
  destruct post6 as (S2 & p & at6 & liv2 & frm2 & sp02 & crd2 & p_pos & p_al & p_top & cg2).
  destruct (ASTA_unpack RT S2 PM _ c6 at6) as (ms6 & (m6 & ret6 & aft6 & pres6 & env6 & wp6 & accp6 & zp6) & at6'). clear at6.
  destruct ret6 as (t0e & t1e & t2e & a1e & a2e & a3f & a4e & a5e & a6e & a7e & t3e & t4e & t5e & t6e & F6 & fc6 & ->).
  destruct aft6 as (art6 & inv6 & wm6 & stk6).
  rewrite (ret_pc_even SITE_rcu_zalloc) in at6' by (unfold SITE_rcu_zalloc; lia).
  rewrite u_spn in stk6, pres6.
  assert (p_in2 : In (p, 264) (rt_live RT S2)) by (rewrite liv2; left; reflexivity).
  pose proof (afp_live_hi RT GOBJ AFP S2 m6 p 264 art6 p_in2 ltac:(lia)) as p_hi.
  pose proof (af_live_range RT AF S2 m6 p 264 art6 p_in2) as (_ & p_win & _).
  unfold STACK_WIN in p_win. rewrite sp02, sp01 in p_win.
  assert (fr_in2 : In (fr, 1%nat) (rt_frames RT S2)) by (rewrite frm2; exact fr_in1).
  pose proof (af_frames_range RT AF S2 m6 fr 1 art6 fr_in2) as (_ & _ & _ & fr_apart2).
  change (fs_size 1) with 128 in fr_apart2.
  pose proof (fr_apart2 p 264 p_in2) as fr_p.
  assert (gap4 : stk asegs m4 (bv_unsigned sp + -160 - pad) (bv_unsigned sp + -160)).
  { apply (stk_agree asegs m3 m4 _ _ gap3); [| exact wm4].
    apply (agree_of_pres_ex _ _ _ _ _ m3 m4 _ pres4). intros x xin. split.
    - apply acl_stack. unfold USTACK_TOP. clear - xin top_e pad_cases. lia.
    - clear - xin pad_cases. lia. }
  assert (gap5 : stk asegs m5 (bv_unsigned sp + -160 - pad) (bv_unsigned sp + -160)).
  { apply (stk_munch _ m4 m5 _ _ gap4 mu5 wm5). intros x xin. cbn [outside].
    clear - xin fr_win fr_pos win_e room_e pad_cases sp0_hi lo_big. repeat split; lia. }
  assert (ffar : forall x, fr <= x < fr + 120 \/ fr / 8 + 2147450880 <= x < fr / 8 + 2147450880 + 16 ->
                 aclient (rt_live RT S1) (rt_frames RT S1) (bv_unsigned sp + -160 - pad) x /\ outside [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] x).
  { intros x [xf | xs]; split.
    - apply (acl_frame _ _ _ fr 1%nat); [exact fr_in1|]. change (fs_size 1) with 128. clear - xf. lia.
    - cbn [outside]. unfold G_ALLOW_CUST. clear - xf fr_seg. split; [lia | exact I].
    - apply (acl_fshadow _ _ _ fr 1%nat); [exact fr_in1|]. unfold shad, SHB. change (fs_size 1) with 128. clear - xs. lia.
    - cbn [outside]. unfold G_ALLOW_CUST. clear - xs fr_pos. split; [lia | exact I]. }
  assert (sfar : forall x, bv_unsigned sp + -160 - pad <= x < bv_unsigned sp ->
                 aclient (rt_live RT S1) (rt_frames RT S1) (bv_unsigned sp + -160 - pad) x /\ outside [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] x).
  { intros x xin. split.
    - apply acl_stack. unfold USTACK_TOP. clear - xin top_e. lia.
    - cbn [outside]. unfold G_ALLOW_CUST. clear - xin lo_big room_e pad_cases. split; [lia | exact I]. }
  assert (gap6 : stk asegs m6 (bv_unsigned sp + -160 - pad) (bv_unsigned sp + -160)).
  { apply (stk_agree asegs m5 m6 _ _ gap5); [| exact wm6].
    apply (agree_of_pres_fp _ _ _ _ m5 m6 _ pres6). intros x xin. apply sfar. clear - xin pad_cases. lia. }
  assert (tail6 : rw_cells asegs m6 (bv_unsigned sp + -104)
                    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m5 m6 _ _ tail5); [| exact wm6].
    apply (agree_of_pres_fp _ _ _ _ m5 m6 _ pres6). intros x xin. cbn [cells_size csize Nat.add] in xin.
    apply sfar. clear - xin pad_cases. lia. }
  assert (fcell6 : rw_cells asegs m6 fr [CB 120 fj5]).
  { apply (rw_cells_agree asegs m5 m6 _ _ fcell5); [| exact wm6].
    apply (agree_of_pres_fp _ _ _ _ m5 m6 _ pres6). intros x xin. cbn [cells_size csize] in xin.
    apply ffar. left. clear - xin. lia. }
  assert (scell6 : rw_cells asegs m6 (fr / 8 + 2147450880) [CB 16 sj5]).
  { apply (rw_cells_agree asegs m5 m6 _ _ scell5); [| exact wm6].
    apply (agree_of_pres_fp _ _ _ _ m5 m6 _ pres6). intros x xin. cbn [cells_size csize] in xin.
    apply ffar. right. clear - xin. lia. }
  assert (head6 : wr_at asegs m6 (bv_unsigned sp + -160) 56).
  { apply (wr_at_wm m3 m6).
    - apply (stk_wr_at m3 _ _ _ _ full3); clear - pad_cases; lia.
    - exact (wmono_trans asegs m3 m4 m6 wm4 (wmono_trans asegs m4 m5 m6 wm5 wm6)). }
  destruct (wr_at_rw_CB m6 _ 56 head6 ltac:(lia)) as (junk6 & hcell6).
  assert (saved6 : rw_cells asegs m6 (bv_unsigned sp + -160)
                     ([CB 56 junk6] ++ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
  { apply (proj2 (rw_cells_app m6 _ _ _)). split; [exact hcell6|]. cbn [cells_size csize Nat.add].
    replace (bv_unsigned sp + -160 + Z.of_nat 56) with (bv_unsigned sp + -104) by lia. exact tail6. }
  cbn [app] in saved6.
  pose proof (wp_zero_rw_CB asegs m6 p 264 zp6 wp6 ltac:(lia)) as zcell6.
  pose proof (af_client_consts RT AF S2 m6 art6) as (_ & _ & _ & _ & ut6).
  pose proof (cl_env_ssp m6 _ _ ut6 env6) as ssp6.
  (* lock fields: context, the three mutexes and the two condition variables *)
  pose proof (rcu_w3 ra sp gp (Z_to_bv 64 TP_A) t0e t1e t2e a1e a2e a3f a4e a5e a6e a7e a1 s6 s7 s11 t3e t4e t5e t6e
                s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F6 fc6 m6 p fr lo pad junk6 fj5 canary
                pad_cases ltac:(clear - room_e; lia) ltac:(clear - lo_big; lia) ltac:(clear - top_e; lia) p_hi
                ltac:(clear - p_win win_e; lia) ltac:(clear - p_al; lia) fr_pos fr_seg ltac:(clear - fr_win win_e; lia)
                ltac:(clear - fr_hi; lia) ltac:(clear - fr_p; lia) stk6 saved6 fcell6 zcell6 accp6 ssp6 inv6) as walk.
  cl_lift walk at6' c7 at7.
  destruct (ASTA_unpack RT S2 PM _ c7 at7)
    as (ms7 & (t0f & t1f & t2f & a4f & a5f & a6f & a7f & t3f & t4f & t5f & t6f & junk7 & fj7 & m7 & -> & mu7 & wm7 & inv7 & stk7 & ssp7
               & saved7 & fcell7 & head7 & mtx1 & mtx2 & cnd1 & mtx3 & cnd2) & at7').
  clear at7.
  assert (win2 : rt_sp0 RT S2 - STACK_WIN <= lo) by (rewrite sp02, sp01; exact win_e).
  assert (art7 : ART RT S2 m7).
  { apply (af_frame RT AF S2 m6 m7 lo art6 win2); [| exact wm7].
    intros a far. apply mu7. cbn [outside].
    split; [| split; [| split; [| split; [| exact I]]]]; intros inside; apply far.
    - apply (acl_live _ _ _ p 264); [exact p_in2 | exact inside].
    - apply (acl_frame _ _ _ fr 1%nat); [exact fr_in2|]. change (fs_size 1) with 128. clear - inside. lia.
    - apply acl_stack. unfold USTACK_TOP. clear - inside room_e top_e pad_cases. lia.
    - apply acl_stack. unfold USTACK_TOP. clear - inside room_e top_e pad_cases. lia. }
  pose proof (rw_cells_skip m7 (bv_unsigned sp + -160) [CB 56 junk7; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1]
                [C8 s0; C8 ra] saved7) as top7.
  cbn [cells_size csize Nat.add] in top7.
  replace (bv_unsigned sp + -160 + Z.of_nat 144) with (bv_unsigned sp - 16) in top7 by lia.
  assert (ag57 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m5 m7).
  { apply (agree_trans _ m5 m6 m7).
    - apply (agree_of_pres_fp _ _ _ _ m5 m6 _ pres6). intros x xr. split.
      + apply acl_stack. unfold USTACK_TOP in *. clear - xr pad_cases. lia.
      + cbn [outside]. unfold G_ALLOW_CUST. clear - xr lo_big room_e. split; [lia | exact I].
    - apply (agree_of_munch _ m6 m7 _ mu7). intros x xr. cbn [outside]. unfold USTACK_TOP in xr.
      clear - xr p_win win_e fr_win room_e pad_cases. repeat split; lia. }
  assert (cgh2 : cg_has (rt_cg RT S2) RCU_SITES RCU_CALLS) by (rewrite cg2; exact cgh1).
  assert (cgx2 : cg_ctx (rt_cg RT S2) e_rcu_lock_new (bv_unsigned ra :: outer)) by (rewrite cg2; exact cgx1).
  destruct (cl_chain_call (rt_cg RT S2) e_rcu_lock_new e_CRYPTO_calloc SITE_rcu_calloc m m7 ra s0 sp
              (Z_to_bv 64 (bv_unsigned sp + -160 - pad)) outer cgx2
              (cg_has_site _ _ _ _ _ cgh2 ltac:(unfold RCU_SITES; right; left; reflexivity))
              (cg_has_call _ _ _ _ _ cgh2 ltac:(unfold RCU_CALLS; right; left; reflexivity))
              chain_e
              (agree_trans _ m m5 m7 (agree_sub _ _ m m5 ag05 ltac:(intros x xr; apply acl_stack; exact xr)) ag57)
              top7 ltac:(rewrite u_spn; clear - pad_cases; lia) ltac:(unfold USTACK_TOP; clear - top_e; lia)) as (cgx7 & chain7).
  rewrite <- (unsigned_lit SITE_rcu_calloc) in cgx7 by (unfold SITE_rcu_calloc; lia).
  assert (tail_z : In (bv_unsigned (Z_to_bv 64 SITE_rcu_calloc), e_CRYPTO_zalloc) (cg_call (rt_cg RT S2))).
  { rewrite unsigned_lit by (unfold SITE_rcu_calloc; lia).
    apply (cg_has_call _ _ _ _ _ cgh2). unfold RCU_CALLS. right; right; left. reflexivity. }
  assert (cg_inner2 : cg_has (rt_cg RT S2) [(SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)]
                        [(SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)])
    by (rewrite cg2; exact cg_inner).
  assert (env7 : cl_env m7 (Z_to_bv 8 1) canary).
  { apply (cl_env_agree m6 m7 _ _ env6). intros a ca. apply mu7.
    pose proof (client_static_range _ (cl_cell_static _ ca)) as a_rng. unfold SEGTOP_A in a_rng. cbn [outside].
    clear - a_rng p_hi fr_seg lo_big room_e pad_cases. repeat split; lia. }
  assert (cok7 : call_ok RT S2 m7 (Z_to_bv 64 (bv_unsigned sp + -160 - pad)) lo).
  { unfold call_ok. rewrite u_spn, sp02, sp01. split; [exact stk7|].
    unfold RT_STACK, STACK_WIN, USTACK_TOP. clear - win_e room_e top_e al_e pad_def pad_cases. repeat split; lia. }
  assert (u2 : bv_unsigned (Z_to_bv 64 2) = 2) by (apply unsigned_lit; lia).
  assert (u8 : bv_unsigned (Z_to_bv 64 8) = 8) by (apply unsigned_lit; lia).
  assert (sz_ok : 1 <= bv_unsigned (Z_to_bv 64 2) * bv_unsigned (Z_to_bv 64 8) <= 67108864) by (rewrite u2, u8; lia).
  assert (no_ovf : bv_eqb (Z_to_bv 64 ((bv_unsigned (Z_to_bv 64 2) * bv_unsigned (Z_to_bv 64 8)) ≫ 64)) (Z_to_bv 64 0) = true)
    by (rewrite u2, u8; vm_compute; reflexivity).
  assert (nlv7 : Z.of_nat (length (rt_live RT S2)) < LIVE_MAX)
    by (rewrite liv2, liv1; cbn [length]; clear - nlv_e; lia).
  assert (mc7 : mcost (bv_unsigned (Z_to_bv 64 2) * bv_unsigned (Z_to_bv 64 8)) <= rt_credit RT S2)
    by (rewrite u2, u8, crd2, crd1; replace (mcost (2 * 8)) with 0 by reflexivity; replace (mcost 264) with 0 by reflexivity;
        clear - cred_e; lia).
  (* the quiescent-point group *)
  refine (C_CALLOC S2 PM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m7 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary
            fdo mst eq_refl sz_ok no_ovf art7 inv7 cok7
            ltac:(rewrite u_spn; unfold RT_STACK; clear - room_e pad_cases; lia) cgx7 chain7 tail_z cg_inner2 nlv7 mc7
            env7 T c7 at7' _).
  intros c8 post8.
  destruct post8 as (S3 & q & at8 & liv3 & frm3 & sp03 & crd3 & q_pos & q_al & q_top & cg3).
  destruct (ASTA_unpack RT S3 PM _ c8 at8) as (ms8 & (m8 & ret8 & aft8 & pres8 & env8 & wq8 & accq8 & zq8) & at8'). clear at8.
  destruct ret8 as (t0g & t1g & t2g & a1g & a2g & a3g & a4g & a5g & a6g & a7g & t3g & t4g & t5g & t6g & F8 & fc8 & ->).
  destruct aft8 as (art8 & inv8 & wm8 & stk8).
  rewrite (ret_pc_even SITE_rcu_calloc) in at8' by (unfold SITE_rcu_calloc; lia).
  rewrite u_spn in stk8, pres8.
  rewrite u2, u8 in liv3, crd3, q_top, wq8, accq8, zq8. change (2 * 8) with 16 in liv3, crd3, q_top, wq8, accq8, zq8.
  assert (q_in3 : In (q, 16) (rt_live RT S3)) by (rewrite liv3; left; reflexivity).
  assert (p_in3 : In (p, 264) (rt_live RT S3)) by (rewrite liv3; right; exact p_in2).
  assert (fr_in3 : In (fr, 1%nat) (rt_frames RT S3)) by (rewrite frm3; exact fr_in2).
  pose proof (af_live_range RT AF S3 m8 q 16 art8 q_in3) as (_ & q_win & _).
  unfold STACK_WIN in q_win. rewrite sp03, sp02, sp01 in q_win.
  pose proof (afp_live_hi RT GOBJ AFP S3 m8 q 16 art8 q_in3 ltac:(lia)) as q_hi.
  pose proof (af_frames_range RT AF S3 m8 fr 1 art8 fr_in3) as (_ & _ & _ & fr_apart3).
  change (fs_size 1) with 128 in fr_apart3.
  pose proof (fr_apart3 q 16 q_in3) as fr_q.
  pose proof (wg_live_apart RT AF S3 m8 [] q 16 (rt_live RT S2) p 264 art8 liv3 p_in2) as q_p.
  assert (fnear8 : forall x, fr <= x < fr + 120 \/ fr / 8 + 2147450880 <= x < fr / 8 + 2147450880 + 16 \/ p <= x < p + 264 \/
                             bv_unsigned sp + -160 - pad <= x < bv_unsigned sp ->
                   aclient (rt_live RT S2) (rt_frames RT S2) (bv_unsigned sp + -160 - pad) x /\ outside [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] x).
  { intros x [xf | [xs | [xp | xk]]]; split; cbn [outside]; unfold G_ALLOW_CUST.
    - apply (acl_frame _ _ _ fr 1%nat); [exact fr_in2|]. change (fs_size 1) with 128. clear - xf. lia.
    - clear - xf fr_seg. split; [lia | exact I].
    - apply (acl_fshadow _ _ _ fr 1%nat); [exact fr_in2|]. unfold shad, SHB. change (fs_size 1) with 128. clear - xs. lia.
    - clear - xs fr_pos. split; [lia | exact I].
    - apply (acl_live _ _ _ p 264); [exact p_in2 | exact xp].
    - clear - xp p_hi. split; [lia | exact I].
    - apply acl_stack. unfold USTACK_TOP. clear - xk top_e. lia.
    - clear - xk lo_big room_e pad_cases. split; [lia | exact I]. }
  assert (head8 : rw_cells asegs m8 p (rcu_head_a a1)).
  { apply (rw_cells_agree asegs m7 m8 _ _ head7); [| exact wm8].
    apply (agree_of_pres_fp _ _ _ _ m7 m8 _ pres8). intros x xin. cbn [rcu_head_a cells_size csize Nat.add] in xin.
    apply fnear8. right; right; left. clear - xin. lia. }
  pose proof (af_acc_live RT AF S3 m8 p 264 art8 p_in3) as (_ & accp8).
  (* storing the group into the lock; failure branch not taken *)
  pose proof (rcu_w4 sp gp (Z_to_bv 64 TP_A) t0g t1g t2g a1g a2g a3g a4g a5g a6g a7g a1 t3g t4g t5g t6g F8 fc8 m8 p q fr lo pad
                ltac:(clear - room_e; lia) ltac:(clear - lo_big; lia) ltac:(clear - top_e; lia) p_hi
                ltac:(clear - p_win win_e; lia) ltac:(clear - p_al; lia) q_pos ltac:(clear - q_win win_e; lia) fr_pos
                ltac:(clear - fr_win win_e; lia) stk8 head8 accp8 inv8) as walk.
  cl_lift walk at8' c9 at9.
  destruct (ASTA_unpack RT S3 PM _ c9 at9) as (ms9 & (a1h & a2h & m9 & -> & mu9 & wm9 & inv9 & stk9 & head9) & at9'). clear at9.
  assert (win3 : rt_sp0 RT S3 - STACK_WIN <= lo) by (rewrite sp03, sp02, sp01; exact win_e).
  assert (art9 : ART RT S3 m9).
  { apply (af_frame RT AF S3 m8 m9 lo art8 win3); [| exact wm9].
    intros a far. apply mu9. cbn [outside]. split; [| exact I]. intros inside. apply far.
    apply (acl_live _ _ _ p 264); [exact p_in3 | clear - inside; lia]. }
  assert (fcell9 : rw_cells asegs m9 fr [CB 120 fj7]).
  { eapply (wg_keep_seg _ m8 m9); [| exact mu9 | exact wm9 |].
    - apply (rw_cells_agree asegs m7 m8 _ _ fcell7); [| exact wm8].
      apply (agree_of_pres_fp _ _ _ _ m7 m8 _ pres8). intros x xin. cbn [cells_size csize] in xin.
      apply fnear8. left. clear - xin. lia.
    - intros x xin. cbn [cells_size csize] in xin. cbn [outside]. clear - xin fr_p. split; [lia | exact I]. }
  assert (scell7 : rw_cells asegs m7 (fr / 8 + 2147450880) [CB 16 sj5]).
  { eapply (wg_keep_seg _ m6 m7); [exact scell6 | exact mu7 | exact wm7 |].
    intros x xin. cbn [cells_size csize] in xin. cbn [outside].
    clear - xin p_hi fr_hi fr_win fr_pos sp0_hi win_e lo_big room_e pad_cases. repeat split; lia. }
  assert (scell9 : rw_cells asegs m9 (fr / 8 + 2147450880) [CB 16 sj5]).
  { eapply (wg_keep_seg _ m8 m9); [| exact mu9 | exact wm9 |].
    - apply (rw_cells_agree asegs m7 m8 _ _ scell7); [| exact wm8].
      apply (agree_of_pres_fp _ _ _ _ m7 m8 _ pres8). intros x xin. cbn [cells_size csize] in xin.
      apply fnear8. right; left. clear - xin. lia.
    - intros x xin. cbn [cells_size csize] in xin. cbn [outside].
      clear - xin p_hi fr_win fr_pos sp0_hi win_e. split; [lia | exact I]. }
  (* fake frame retired *)
  pose proof (rcu_w5 sp gp (Z_to_bv 64 TP_A) t0g t1g t2g (Z_to_bv 64 q) a1h a2h a3g a4g a5g a6g a7g a1 t3g t4g t5g t6g F8 fc8 m9 p fr lo pad fj7 sj5
                ltac:(clear - room_e; lia) ltac:(clear - lo_big; lia) ltac:(clear - top_e; lia) fr_pos fr_seg
                ltac:(clear - fr_win win_e; lia) ltac:(clear - fr_hi; lia) stk9 fcell9 scell9 inv9) as walk.
  cl_lift walk at9' c10 at10.
  destruct (ASTA_unpack RT S3 PM _ c10 at10) as (ms10 & (a0i & fj10 & sj10 & m10 & -> & mu10 & wm10 & inv10 & stk10 & fcell10 & scell10) & at10').
  clear at10.
  assert (art10 : ART RT S3 m10).
  { apply (af_frame RT AF S3 m9 m10 lo art9 win3); [| exact wm10].
    intros a far. apply mu10. cbn [outside].
    split; [| split; [| exact I]]; intros inside; apply far.
    - apply (acl_frame _ _ _ fr 1%nat); [exact fr_in3|]. change (fs_size 1) with 128. clear - inside. lia.
    - apply (acl_fshadow _ _ _ fr 1%nat); [exact fr_in3|]. unfold shad, SHB. change (fs_size 1) with 128. clear - inside. lia. }
  assert (frs3 : rt_frames RT S3 = (fr, 1%nat) :: rt_frames RT S0) by (rewrite frm3, frm2; exact frm1).
  destruct (af_frame_release RT AF S3 m10 fr 1 (rt_frames RT S0) art10 frs3)
    as (S4 & fl & flag10 & fl_far & fl_pos & fl_win & fl_ptr & release).
  change (fs_size 1) with 128 in fl_ptr. replace (fr + 128 - 8) with (fr + 120) in fl_ptr by lia.
  unfold STACK_WIN in fl_win. rewrite sp03, sp02, sp01 in fl_win.
  assert (gap7 : stk asegs m7 (bv_unsigned sp + -160 - pad) (bv_unsigned sp + -160)).
  { apply (stk_munch _ m6 m7 _ _ gap6 mu7 wm7). intros x xin. cbn [outside].
    clear - xin p_win fr_win win_e room_e pad_cases. repeat split; lia. }
  assert (gap10 : stk asegs m10 (bv_unsigned sp + -160 - pad) (bv_unsigned sp + -160)).
  { eapply (stk_munch _ m9 m10); [| exact mu10 | exact wm10 |].
    - eapply (stk_munch _ m8 m9); [| exact mu9 | exact wm9 |].
      + apply (stk_agree asegs m7 m8 _ _ gap7); [| exact wm8].
        apply (agree_of_pres_fp _ _ _ _ m7 m8 _ pres8). intros x xin. apply fnear8. right; right; right. clear - xin pad_cases. lia.
      + intros x xin. cbn [outside]. clear - xin p_win win_e room_e pad_cases. split; [lia | exact I].
    - intros x xin. cbn [outside]. clear - xin fr_win fr_pos win_e room_e pad_cases sp0_hi lo_big. repeat split; lia. }
  assert (saved10 : rw_cells asegs m10 (bv_unsigned sp + -160)
                      [CB 56 junk7; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply (wg_keep_seg _ m9 m10); [| exact mu10 | exact wm10 |].
    - eapply (wg_keep_seg _ m8 m9); [| exact mu9 | exact wm9 |].
      + apply (rw_cells_agree asegs m7 m8 _ _ saved7); [| exact wm8].
        apply (agree_of_pres_fp _ _ _ _ m7 m8 _ pres8). intros x xin. cbn [cells_size csize Nat.add] in xin.
        apply fnear8. right; right; right. clear - xin pad_cases. lia.
      + intros x xin. cbn [cells_size csize Nat.add] in xin. cbn [outside]. clear - xin p_win win_e room_e. split; [lia | exact I].
    - intros x xin. cbn [cells_size csize Nat.add] in xin. cbn [outside].
      clear - xin fr_win fr_pos win_e room_e sp0_hi lo_big. repeat split; lia. }
  (* return: fake frame released, callee-saved registers restored *)
  pose proof (rcu_w6 ra sp gp (Z_to_bv 64 TP_A) t0g t1g t2g a0i a1h a2h a3g a4g a5g a6g a7g t3g t4g t5g t6g
                s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F8 fc8 m10 p fr fl lo pad junk7
                pad_cases ltac:(clear - room_e; lia) ltac:(clear - lo_big; lia) ltac:(clear - top_e; lia) fr_pos
                ltac:(clear - fr_win win_e; lia) fl_pos ltac:(clear - fl_win win_e; lia) stk10 gap10 saved10 fl_ptr flag10 inv10) as walk.
  cl_lift walk at10' c11 at11.
  destruct (ASTA_unpack RT S3 PM _ c11 at11) as (ms11 & (m11 & -> & mu11 & wm11 & inv11 & stk11 & flag11) & at11'). clear at11.
  destruct (release m11 mu11 wm11 flag11) as (art11 & frm4 & liv4 & sp04 & crd4 & al4 & artm4 & cg4).
  (* the caller's view of memory *)
  assert (fl_not : forall x, aclient (rt_live RT S3) (rt_frames RT S3) USTACK_TOP x -> x <> fl).
  { intros x kx x_fl. subst x. exact (fl_far kx). }
  assert (lift3 : forall x, aclient (rt_live RT S0) (rt_frames RT S0) (bv_unsigned sp) x -> x < lo ->
                  aclient (rt_live RT S3) (rt_frames RT S3) USTACK_TOP x).
  { intros x kx xlo. unfold aclient in kx |- *. destruct kx as [st | [cs | [lv | [ff | fs]]]].
    - clear - st xlo room_e. lia.
    - right; left; exact cs.
    - right; right; left. destruct lv as (pp & nn & pin & prng). exists pp, nn. split; [| exact prng].
      rewrite liv3, liv2, liv1. right; right; exact pin.
    - right; right; right; left. destruct ff as (ff & kk & fin & frng). exists ff, kk. split; [| exact frng].
      rewrite frs3. right; exact fin.
    - right; right; right; right. destruct fs as (ff & kk & fin & frng). exists ff, kk. split; [| exact frng].
      rewrite frs3. right; exact fin. }
  assert (apart_p : forall x, aclient (rt_live RT S0) (rt_frames RT S0) (bv_unsigned sp) x -> ~ (p <= x < p + 264)).
  { intros x kx. destruct (split_x x kx) as [hx | hx]; [clear - hx p_win win_e room_e; lia|].
    apply (newchunk_apart RT AF S1 S2 m6 p 264 (bv_unsigned sp + -160 - pad) x art6 liv2 frm2 sp02
             ltac:(rewrite sp01; unfold STACK_WIN; clear - win_e room_e pad_cases; lia) ltac:(lia) (mono1 x kx)). }
  assert (mono2 : forall x, aclient (rt_live RT S0) (rt_frames RT S0) (bv_unsigned sp) x ->
                  aclient (rt_live RT S2) (rt_frames RT S2) (bv_unsigned sp + -160 - pad) x).
  { intros x kx. apply (aclient_mono _ _ _ _ _ _ _ kx).
    - intros e e_in. rewrite liv2, liv1. right. exact e_in.
    - intros e e_in. rewrite frm2, frm1. right. exact e_in.
    - clear - pad_cases. lia. }
  assert (agK : agree_on (fun x => aclient (rt_live RT S0) (rt_frames RT S0) (bv_unsigned sp) x
                                   /\ outside [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] x) m5 m11).
  { apply (agree_trans _ m5 m10 m11); [apply (agree_trans _ m5 m9 m10); [apply (agree_trans _ m5 m8 m9);
      [apply (agree_trans _ m5 m7 m8); [apply (agree_trans _ m5 m6 m7)|]|]|]|].
    - apply (agree_of_pres_fp _ _ _ _ m5 m6 _ pres6). intros x (kx & ox). exact (conj (mono1 x kx) ox).
    - apply (agree_of_munch _ m6 m7 _ mu7). intros x (kx & _). cbn [outside].
      pose proof (apart_p x kx) as np. destruct (apart_fr x kx) as (nf & _). destruct (split_x x kx) as [hx | hx];
      clear - hx np nf room_e pad_cases; repeat split; lia.
    - apply (agree_of_pres_fp _ _ _ _ m7 m8 _ pres8). intros x (kx & ox). exact (conj (mono2 x kx) ox).
    - apply (agree_of_munch _ m8 m9 _ mu9). intros x (kx & _). cbn [outside].
      pose proof (apart_p x kx) as np. clear - np. split; [lia | exact I].
    - apply (agree_of_munch _ m9 m10 _ mu10). intros x (kx & _). cbn [outside].
      destruct (apart_fr x kx) as (nf & ns). clear - nf ns. repeat split; lia.
    - apply (agree_of_munch _ m10 m11 _ mu11). intros x (kx & _). cbn [outside]. split; [| exact I].
      destruct (split_x x kx) as [hx | hx]; [clear - hx fl_win win_e room_e; lia|].
      pose proof (fl_not x (lift3 x kx hx)) as nfl. clear - nfl. lia. }
  assert (presF : rt_pres_fp (rt_live RT S0) (rt_frames RT S0) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m11).
  { intros a ka oa. rewrite (agK a (conj ka oa)). exact (ag05 a ka). }
  assert (wm_all : wmono asegs m m11).
  { apply (wmono_trans asegs m m1 m11 wm1), (wmono_trans asegs m1 m2 m11 wm2), (wmono_trans asegs m2 m3 m11 wm3),
      (wmono_trans asegs m3 m4 m11 wm4), (wmono_trans asegs m4 m5 m11 wm5), (wmono_trans asegs m5 m6 m11 wm6),
      (wmono_trans asegs m6 m7 m11 wm7), (wmono_trans asegs m7 m8 m11 wm8), (wmono_trans asegs m8 m9 m11 wm9),
      (wmono_trans asegs m9 m10 m11 wm10). exact wm11. }
  assert (wm_7 : wmono asegs m7 m11).
  { apply (wmono_trans asegs m7 m8 m11 wm8), (wmono_trans asegs m8 m9 m11 wm9), (wmono_trans asegs m9 m10 m11 wm10). exact wm11. }
  assert (env11 : cl_env m11 (Z_to_bv 8 1) canary).
  { apply (cl_env_agree m8 m11 _ _ env8). intros a ca.
    pose proof (cl_cell_static _ ca) as a_st. pose proof (client_static_range _ a_st) as a_rng. unfold SEGTOP_A in a_rng.
    assert (o9 : outside [(p, p + 48)] (bv_unsigned a)) by (cbn [outside]; clear - a_rng p_hi; split; [lia | exact I]).
    assert (o10 : outside [(fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] (bv_unsigned a))
      by (cbn [outside]; clear - a_rng fr_seg fr_pos; repeat split; lia).
    assert (o11 : outside [(fl, fl + 1)] (bv_unsigned a)).
    { cbn [outside]. split; [| exact I]. intros on_fl.
      apply (fl_not (bv_unsigned a)); [apply acl_static; exact a_st | clear - on_fl; lia]. }
    rewrite (mu11 a o11), (mu10 a o10), (mu9 a o9). reflexivity. }
  assert (agL : agree_on (fun x => p <= x < p + 264) m9 m11).
  { apply (agree_trans _ m9 m10 m11).
    - apply (agree_of_munch _ m9 m10 _ mu10). intros x xin. cbn [outside].
      clear - xin fr_p p_hi fr_win fr_pos sp0_hi win_e. repeat split; lia.
    - apply (agree_of_munch _ m10 m11 _ mu11). intros x xin. cbn [outside]. split; [| exact I].
      pose proof (fl_not x (acl_live _ _ _ p 264 x p_in3 xin)) as nfl. clear - nfl. lia. }
  assert (agM : agree_on (fun x => p + 48 <= x < p + 264) m7 m9).
  { apply (agree_trans _ m7 m8 m9).
    - apply (agree_of_pres_fp _ _ _ _ m7 m8 _ pres8). intros x xin. apply fnear8. right; right; left. clear - xin. lia.
    - apply (agree_of_munch _ m8 m9 _ mu9). intros x xin. cbn [outside]. clear - xin. split; [lia | exact I]. }
  assert (agQ : agree_on (fun x => q <= x < q + 16) m8 m11).
  { apply (agree_trans _ m8 m10 m11); [apply (agree_trans _ m8 m9 m10)|].
    - apply (agree_of_munch _ m8 m9 _ mu9). intros x xin. cbn [outside]. clear - xin q_p. split; [lia | exact I].
    - apply (agree_of_munch _ m9 m10 _ mu10). intros x xin. cbn [outside].
      clear - xin fr_q q_hi fr_win fr_pos sp0_hi win_e. repeat split; lia.
    - apply (agree_of_munch _ m10 m11 _ mu11). intros x xin. cbn [outside]. split; [| exact I].
      pose proof (fl_not x (acl_live _ _ _ q 16 x q_in3 xin)) as nfl. clear - nfl. lia. }
  assert (agML : agree_on (fun x => p + 48 <= x < p + 264) m7 m11).
  { apply (agree_trans _ m7 m9 m11 agM). apply (agree_sub _ _ m9 m11 agL). intros x xin. clear - xin. lia. }
  assert (wm_9 : wmono asegs m9 m11) by exact (wmono_trans asegs m9 m10 m11 wm10 wm11).
  assert (wm_8 : wmono asegs m8 m11) by exact (wmono_trans asegs m8 m9 m11 wm9 wm_9).
  assert (p_in4 : In (p, 264) (rt_live RT S4)) by (rewrite liv4; exact p_in3).
  assert (q_in4 : In (q, 16) (rt_live RT S4)) by (rewrite liv4; exact q_in3).
  pose proof (wp_zero_rw_CB asegs m8 q 16 zq8 wq8 ltac:(lia)) as zcellq8.
  apply finish. exists S4, p, q. split.
  - apply (ASTA_conseq RT S4 PM _ _ c11 (ASTA_switch RT S3 S4 PM _ c11 at11' al4 artm4)).
    intros ms <-. exists m11.
    split; [do 16 eexists; reflexivity|].
    split; [split; [exact art11 | split; [exact inv11 | split; [exact wm_all | exact stk11]]]|].
    split; [exact presF|]. split; [exact env11|].
    split.
    { apply (rw_cells_agree asegs m9 m11 _ _ head9); [| exact wm_9].
      apply (agree_sub _ _ m9 m11 agL). intros x xin. cbn [rcu_head cells_size csize Nat.add] in xin. clear - xin. lia. }
    split.
    { apply (rw_cells_agree asegs m7 m11 _ _ mtx1); [| exact wm_7].
      apply (agree_sub _ _ m7 m11 agML). intros x xin. cbn [mutex_cells cells_size csize Nat.add] in xin. clear - xin. lia. }
    split.
    { apply (rw_cells_agree asegs m7 m11 _ _ mtx2); [| exact wm_7].
      apply (agree_sub _ _ m7 m11 agML). intros x xin. cbn [mutex_cells cells_size csize Nat.add] in xin. clear - xin. lia. }
    split.
    { apply (rw_cells_agree asegs m7 m11 _ _ cnd1); [| exact wm_7].
      apply (agree_sub _ _ m7 m11 agML). intros x xin. cbn [cond_cells cells_size csize Nat.add] in xin. clear - xin. lia. }
    split.
    { apply (rw_cells_agree asegs m7 m11 _ _ mtx3); [| exact wm_7].
      apply (agree_sub _ _ m7 m11 agML). intros x xin. cbn [mutex_cells cells_size csize Nat.add] in xin. clear - xin. lia. }
    split.
    { apply (rw_cells_agree asegs m7 m11 _ _ cnd2); [| exact wm_7].
      apply (agree_sub _ _ m7 m11 agML). intros x xin. cbn [cond_cells cells_size csize Nat.add] in xin. clear - xin. lia. }
    split; [exact (proj2 (af_acc_live RT AF S4 m11 p 264 art11 p_in4))|].
    split.
    { apply (rw_cells_agree asegs m8 m11 _ _ zcellq8); [| exact wm_8].
      apply (agree_sub _ _ m8 m11 agQ). intros x xin. cbn [cells_size csize] in xin. clear - xin. lia. }
    exact (proj2 (af_acc_live RT AF S4 m11 q 16 art11 q_in4)).
  - rewrite liv4, liv3, liv2, liv1, frm4, sp04, sp03, sp02, sp01, crd4, crd3, crd2, crd1, cg4, cg3, cg2, cg1.
    replace (mcost 16) with 0 by reflexivity. replace (mcost 264) with 0 by reflexivity.
    unfold USTACK_TOP in p_top, q_top.
    repeat split; try reflexivity; lia.
Qed.
End RcuLockNew.
