(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_Rep ECH_KitH ECH_LibState ECH_LibFrame ECH_C0_stmt ECH_C0_locks ECH_C1_stmt ECH_C1_malloc ECH_C1_free ECH_C2_stmt ECH_C2_small ECH_C5_stmt ECH_C5_small ECH_C3_stmt ECH_C3_ready ECH_C3_newex ECH_UbKit.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition GG_RA : Z := 0xe75b4.     (* [comment removed for export] *)
Definition NX_RA : Z := 0xeb3d8.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition nx_frame (j : list byte) (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [CB 88 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  (* [comment removed for export] *)
  Lemma gg_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 GG_RA) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 sp s1
                       (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_get_default_context) fc None m1 (seg_rom usegs)
          /\ munch [(bv_unsigned sp + -16, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (bv_unsigned sp + -16)
          /\ rw_cells usegs m1 (bv_unsigned sp + -16) [C8 s0; C8 ra])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_ossl_lib_ctx_get_ex_data_global) fc None m (seg_rom usegs)).
  Proof.
    intros until lo. intros ST CEIL LO MI. unfold P_ossl_lib_ctx_get_ex_data_global, P_get_default_context, GG_RA.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. try if_lit.
    carve_frame 16%nat ST.
    do 5 step. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma gg_seg2 :
    forall (sp gp tp t0 t1 t2 s0x a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      rw_cells usegs m (bv_unsigned sp + -16) [C8 s0; C8 ra] -> mem_inv usegs m ->
      evt usegs (fun ms' => exists a1',
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A_defctx_global) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 GG_RA) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0x s1 (Z_to_bv 64 A_defctx) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 GG_RA)) fc None m (seg_rom usegs)).
  Proof.
    intros until m. intros FR MI. unfold GG_RA, A_defctx, A_defctx_global, A_defctx.
    replace (ret_pc (Z_to_bv 64 0xe75b4)) with (Z_to_bv 64 0xe75b4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR.
    (* [comment removed for export] *)
    st1. st1. step. step. try if_lit. step. step. try if_lit. step. step.
    apply evt_done. eexists. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma nx_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (obj ad lo : Z),
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 192 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1 j,
          ms' = MS (mkR (Z_to_bv 64 NX_RA) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp (Z_to_bv 64 ad)
                       (Z_to_bv 64 0) (Z_to_bv 64 CRYPTO_EX_INDEX_BIO) (Z_to_bv 64 obj) (Z_to_bv 64 ad) a4 a5 a6 a7
                       (Z_to_bv 64 obj) (Z_to_bv 64 0) (Z_to_bv 64 CRYPTO_EX_INDEX_BIO) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_ossl_lib_ctx_get_ex_data_global) fc None m1 (seg_rom usegs)
          /\ munch [(bv_unsigned sp + -192, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (bv_unsigned sp + -192)
          /\ rw_cells usegs m1 (bv_unsigned sp + -192) (nx_frame j s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 CRYPTO_EX_INDEX_BIO) (Z_to_bv 64 obj) (Z_to_bv 64 ad) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_CRYPTO_new_ex_data) fc None m (seg_rom usegs)).
  Proof.
    intros until lo. intros ST CEIL LO MI. unfold P_CRYPTO_new_ex_data, P_ossl_lib_ctx_get_ex_data_global, NX_RA, CRYPTO_EX_INDEX_BIO.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -192, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    (* [comment removed for export] *)
    carve_frame 16%nat ST. do 3 st1. step. step. step. step. step. do 2 st1. step.
    release_frame FR ST (bv_unsigned sp). step.
    (* [comment removed for export] *)
    carve_frame 192%nat ST. do 14 st1. step. step. step. step. step. step.
    finish. exact FR.
  Qed.
End S.

Section S2.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  (* [comment removed for export] *)
  Lemma nx_seg2 :
    forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 vra : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (x : ctxinfo) (obj ad c0 k0 lo : Z) (j : list byte),
      let b := cx_exlock x in
      tp = Z_to_bv 64 RATP ->
      0 < ad -> ad mod 8 = 0 ->   (* [comment removed for export] *)
      rw_cells usegs m ad [C8 (wz c0); C8 (wz k0)] -> (ad + 16 <= lo \/ bv_unsigned sp <= ad) -> off_image ad 16 ->
      CTX_statics m x -> EXLOCK LB m b -> (ad + 16 <= blk_addr b \/ blk_addr b + MUTEX_SIZE <= ad) ->
      rw_cells usegs m (bv_unsigned sp + -192) (nx_frame j v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 vra) ->
      stk usegs m lo (bv_unsigned sp + -192) -> hceil <= lo -> lo <= bv_unsigned sp - 192 - NEWEX_INNER -> mem_inv usegs m ->
      IMPL_mem m -> GOT_mem m -> bv_unsigned vra mod 2 = 0 ->
      evt usegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
          ms' = MS (mkR vra sp gp tp t0' t1' t2' v0 v1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7'
                       v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 t3' t4' t5' t6')
                   F (ret_pc vra) fc None m' (seg_rom usegs)
          /\ munch ((lo, bv_unsigned sp) :: (ad, ad + 16) :: mutex_foot (blk_addr b)) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
          /\ stk usegs m' lo (bv_unsigned sp)
          /\ CTX_statics m' x /\ EXLOCK LB m' b /\ rw_cells usegs m' ad [C8 (wz 0); C8 (wz 0)] /\ IMPL_mem m' /\ GOT_mem m')
        (MS (mkR (Z_to_bv 64 NX_RA) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp (Z_to_bv 64 ad) (Z_to_bv 64 A_defctx_global)
                 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 obj) (Z_to_bv 64 0) (Z_to_bv 64 CRYPTO_EX_INDEX_BIO) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 NX_RA)) fc None m (seg_rom usegs)).
  Proof.
    intros until j. cbv zeta. intros TP ADP ADAL AD ADLO OFF CS EX SEP FR ST CEIL LO MI IM GM RAE.
    unfold NX_RA, NEWEX_INNER, GETANDLOCK_STACK, FR_get_and_lock, CRWLOCK_STACK, CUNLOCK_STACK,
      FR_mutex_unlock, FR_pthread_mutex_unlock, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock, CRYPTO_EX_INDEX_BIO in *. hcb.
    replace (ret_pc (Z_to_bv 64 0xeb3d8)) with (Z_to_bv 64 0xeb3d8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR. pose proof (word_range vra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl ((lo, bv_unsigned sp) :: (ad, ad + 16) :: mutex_foot (blk_addr (cx_exlock x))) m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold mutex_foot in MU.
    pose proof CS as CS0. unfold CTX_statics in CS. destruct CS as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12).
    pose proof EX as EX0. destruct EX as (XI & XZ & XR & XM). unfold MUTEX, MUTEX_SIZE in *. unfold rblock_range in XR.
    destruct (cx_exlock x) as [[xp xa] xn] eqn:Hx. cbn [blk_addr blk_size fst snd] in *.
    pose proof (rw_cells_bound _ _ _ _ XM) as XB. cbn [cells_size csize Nat.add length] in XB.
    pose proof (rw_cells_bound _ _ _ _ AD) as ADB. cbn [cells_size csize Nat.add length] in ADB.
    unfold off_image, IMG_LO, IMG_HI in OFF.
    unfold IMPL_mem, GOT_mem, A_malloc_impl, A_got_CRYPTO_malloc, P_CRYPTO_malloc, P_CRYPTO_realloc, P_CRYPTO_free in IM, GM.
    unfold nx_frame in FR.
    unfold_ctx_addrs.
    unfold A_defctx_global, A_defctx in *.
    (* [comment removed for export] *)
    step. try if_false. step. step. step. step.
    eapply evt_cut.
    { pose proof getandlock_spec as Q; hnf in Q; eapply Q with (lo := lo) (x := x) (LB := LB) (rd := 1); clear Q; cbv zeta;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia;
        try (unfold GETANDLOCK_STACK, FR_get_and_lock, CRWLOCK_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock; lia).
      rewrite Hx. unfold EXLOCK. cbn [blk_addr blk_size fst snd]. split; [exact XI|]. split; [exact XZ|]. split; [unfold rblock_range, MUTEX_SIZE; lia| exact XM]. }
    intros ms_ PO_; rewrite Hx in PO_; cbn [blk_addr fst snd] in PO_; unfold mutex_foot in PO_; revert ms_ PO_.
    land MU WM.
    match goal with K : MUTEX _ _ _ |- _ => unfold MUTEX, MUTEX_HELD in K; rename K into XM end.
    (* [comment removed for export] *)
    unfold A_defctx_exmeth_bio in *.
    step. if_lit. step. ub_dead_by (clear - ADP). step. step. ubal_by ADAL. step. if_lit. step. st1. st1. step. try if_lit. st1. step.
    eapply evt_cut.
    { pose proof sk_num_null_spec as Q; hnf in Q; eapply Q with (lo := lo); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia. }
    land MU WM.
    (* [comment removed for export] *)
    step. step. try if_lit. step. step. step. try if_lit. st1. step.
    eapply evt_cut.
    { pose proof cunlock_spec as Q; hnf in Q; eapply Q with (lo := lo) (M := xa) (lk := 16); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia;
        try (unfold MUTEX_SIZE, CUNLOCK_STACK, FR_mutex_unlock, FR_pthread_mutex_unlock, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock in *; lia). }
    land MU WM.
    match goal with K : MUTEX _ _ _ |- _ => unfold MUTEX in K; rename K into XM end.
    (* [comment removed for export] *)
    step. try if_lit. step. try if_lit. step. step. step.
    if_cases K0; zify_cond K0; [kill K0|]; clear K0. step. step. step. step. step.
    eapply evt_cut.
    { pose proof cfree_null_evt_spec as Q; hnf in Q; eapply Q with (lo := lo); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia;
        first [ unfold IMPL_mem, A_malloc_impl, P_CRYPTO_malloc, P_CRYPTO_realloc, P_CRYPTO_free, wz; exact IM
              | unfold GOT_mem, A_got_CRYPTO_malloc, P_CRYPTO_malloc, P_CRYPTO_realloc, P_CRYPTO_free, wz; exact GM ]. }
    land MU WM.
    (* [comment removed for export] *)
    step. step. do 13 st1. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
    all: try (unfold IMPL_mem, GOT_mem, A_malloc_impl, A_got_CRYPTO_malloc, P_CRYPTO_malloc, P_CRYPTO_realloc, P_CRYPTO_free, wz; assumption).
    - unfold CTX_statics; rewrite Hx; cbn [blk_addr fst snd]; ctx_statics_back.
    - unfold EXLOCK. cbn [blk_addr blk_size fst snd]. split; [exact XI|]. split; [exact XZ|]. split; [unfold rblock_range, MUTEX_SIZE; lia| exact XM].
  Qed.
End S2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac ctx_x_windows :=
  repeat (first [ apply Forall_nil
                | apply Forall_ctxph_foot
                | (unfold CTX_X, A_destructor_key, A_defctx_inited, A_tevent_once, A_base_inited, A_in_init_config_key, A_load_strings_once, A_optsdone_lock,
                     A_td_cancelbuf, A_keys, A_next_key, A_key_lock; cbn [app]; apply Forall_cons; [cbn [fst snd]; lia|]) ]).

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HX : heap_sr_hyps_x H.
  (* [comment removed for export] *)
  Hypothesis CERTA : getdefctx_fresh_stmt H.
  Let HH : heap_sr_hyps H := proj1 HX.

  (* [comment removed for export] *)
  Lemma magree_lib_of_stack_munch : forall s LB m0 m m' W,
    hs_RHEAP H s LB m0 -> munch W m m' -> wmono usegs m m' -> Forall (fun iv : Z * Z => hceil <= fst iv) W -> magree (lib_addr LB) m m'.
  Proof.
    intros s LB m0 m m' W HP MU WM FW. hcb. eapply magree_of_munch; [exact MU| exact WM|].
    intros a Ha HL.
    assert (AB : a < hceil).
    { destruct HL as [HL|(b & Hb & Hr)].
      - unfold LIBX, LIBX0 in HL. cbn [rin_ivs fst snd] in HL. lia.
      - pose proof (HH_blocks_below H HH _ _ _ HP b Hb). lia. }
    clear MU WM HL. induction W as [|[lo hi] W IH]; [exact I|]. cbn. split; [| apply IH; exact (Forall_inv_tail FW)].
    pose proof (Forall_inv FW) as K. cbn in K. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma getdefctx_spec : getdefctx_stmt H.
  Proof.
    unfold getdefctx_stmt, getdefctx_stmt_at. intros [|x]; [exact CERTA|].
    unfold getdefctx_stmt_for. intros until errv.
    intros A0 HP KREL BUD BUDC BUDB AUX SPB SPA ST CEIL LO ERR MI TP MF IM GM RL CPH RAE.
    cbn [CTXPH] in CPH. destruct CPH as [CS CB]. cbn [ctxph_stack] in LO.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    eapply (sr_evt_krel H HH); [exact KREL| eapply getdefctx_ready_spec with (lo := lo) (x := x); [exact TP| exact CS| exact ST| exact CEIL| exact LO| exact MI| exact RAE]|].
    intros ms1 PO. unfold c3_post in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & -> & MU1 & WM1 & MI1 & ST1 & CS1).
    pose proof (magree_lib_of_stack_munch _ _ _ _ _ _ HP MU1 WM1 ltac:(apply Forall_cons; [cbn; lia| apply Forall_nil])) as AG1.
    apply (sr_done H HH). unfold getdefctx_post. cbn [cfg_ms cfg_model].
    exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m1, errv, s, (@nil block), x. cbn [app].
    split; [reflexivity|]. split; [exact KREL|]. split; [apply (mpres_refl H HH)|]. split; [exact MI1|]. split; [exact ST1|].
    split; [eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1| subst tp; rewrite errno_RATP; unfold RERRNO; cbn; lia]|].
    split. { eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]. unfold RAUXV_CELL. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    split. { eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    split; [cbn; split; reflexivity|].
    split; [split; [exact CS1| eapply CTX_blocks_frame; [exact CB| exact AG1]]|].
    split; [intros; discriminate|].
    split; [eapply MEMFLAG_across; [exact MU1| exact WM1| unfold A_mem_inited; cbn; lia| exact MF]|].
    split; [eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]|].
    split; [eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]|].
    split; [eapply relro_lib_munch; [exact RL| exact MU1| apply Forall_cons; [unfold RELRO_LO, RELRO_HI; cbn; lia| apply Forall_nil]]|].
    eapply xpres_of_munch; [exact MU1| exact WM1| | exact HB]. apply Forall_cons; [left; cbn; lia| apply Forall_nil].
  Qed.

  (* [comment removed for export] *)
  Lemma getglobal_spec : getglobal_stmt H.
  Proof.
    unfold getglobal_stmt, getdefctx_stmt_at. intros ph. unfold getdefctx_stmt_for. intros until errv.
    intros A0 HP KREL BUD BUDC BUDB AUX SPB SPA ST CEIL LO ERR MI TP MF IM GM RL CPH RAE. subst a0.
    unfold GETGLOBAL_STACK, FR_ossl_lib_ctx_get_ex_data_global in LO.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    assert (STK0 : 0 <= ctxph_stack ph).
    { destruct ph; cbn [ctxph_stack]; unfold CTXINIT_STACK, RREALLOC_STACK, RMALLOC_STACK, GETDEFCTX_STACK, CGETLOCAL_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock, FR_get_default_context; lia. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply gg_seg1 with (lo := lo); [exact ST| exact CEIL| lia| exact MI]|].
    intros ms1 (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    pose proof (magree_lib_of_stack_munch _ _ _ _ _ _ HP MU1 WM1 ltac:(apply Forall_cons; [cbn; lia| apply Forall_nil])) as AG1.
    assert (XP1 : xpres LB (bv_unsigned sp) (ctxph_foot ph) m m1).
    { eapply xpres_of_munch; [exact MU1| exact WM1| | exact HB]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    (* [comment removed for export] *)
    pose proof getdefctx_spec as GD. unfold getdefctx_stmt, getdefctx_stmt_at, getdefctx_stmt_for in GD.
    eapply (sr_seq H HH).
    { eapply (GD ph) with (lo := lo) (B := B) (LB := LB) (s := s); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact KREL| exact BUD| exact BUDC| exact BUDB| exact ST1| exact CEIL| exact MI1| exact TP].
      all: lazymatch goal with
           | |- hs_RHEAP _ _ _ _ => eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]; apply Forall_cons; [left; cbn; lia| apply Forall_nil]
           | |- hs_rauxv_ok _ _ _ => eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]; unfold RAUXV_CELL; apply Forall_cons; [cbn; lia| apply Forall_nil]
           | |- bv_unsigned _ <= _ => lia
           | |- _ mod 16 = 0 => clear - SPA SPR LO STK0; lia
           | |- _ <= bv_unsigned _ - _ => lia
           | |- rw_cells _ _ _ _ => eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1| subst tp; rewrite errno_RATP; unfold RERRNO; cbn; lia]
           | |- MEMFLAG _ _ => eapply MEMFLAG_across; [exact MU1| exact WM1| unfold A_mem_inited; cbn; lia| exact MF]
           | |- IMPL_mem _ => eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]
           | |- GOT_mem _ => eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]
           | |- ECH_LibState.relro_lib _ => eapply relro_lib_munch; [exact RL| exact MU1| apply Forall_cons; [unfold RELRO_LO, RELRO_HI; cbn; lia| apply Forall_nil]]
           | |- CTXPH _ _ _ => eapply CTXPH_frame; [exact CPH| exact AG1]
           | |- _ mod 2 = 0 => unfold GG_RA; rewrite unsigned_lit by lia; reflexivity
           | |- _ => try lia
           end. }
    clear GD. intros [ms2 mo2] PO. unfold getdefctx_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & s2' & LBN & x &
                    -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & HEAP2 & DELTA & CPH2 & KEYS & MF2 & IM2 & GM2 & RL2 & XP2).
    rewrite (unsigned_lit (bv_unsigned sp + -16)) in ST2, XP2 by lia.
    assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -16) [C8 s0; C8 ra]).
    { eapply xpres_rw_cells'; [exact XP2| exact FR1| left; cbn; lia|]. ctx_x_windows. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL2| eapply gg_seg2; [exact FR2| exact MI2]|].
    intros ms3 (a1' & ->).
    apply (sr_done H HH). unfold getdefctx_post. cbn [cfg_ms cfg_model].
    exists u0, u1, u2, a1', b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, errv2, s2', LBN, x.
    split; [reflexivity|]. split; [exact KREL2|]. split; [exact MP2|]. split; [exact MI2|].
    split. { pose proof (stk_release usegs m2 lo _ _ ST2 FR2 ltac:(lia)) as ST3. cbn [cells_size csize Nat.add] in ST3.
             replace (bv_unsigned sp + -16 + Z.of_nat 16) with (bv_unsigned sp) in ST3 by lia. exact ST3. }
    split; [exact ERR2|]. split; [exact AUX2|]. split; [exact HEAP2|]. split; [exact DELTA|]. split; [exact CPH2|]. split; [exact KEYS|].
    split; [exact MF2|]. split; [exact IM2|]. split; [exact GM2|]. split; [exact RL2|].
    eapply xpres_trans; [exact XP1| eapply xpres_weaken; [exact XP2| lia| auto| auto]].
  Qed.

  (* [comment removed for export] *)
  Lemma cnewex_spec : cnewex_stmt H.
  Proof.
    unfold cnewex_stmt. intros until errv.
    intros A0 A1 A2 ADP ADAL AD XR OFF ADB SEPR HP KREL BUD BUDC BUDB AUX SPB SPA ST CEIL LO ERR MI TP MF IM GM RL CPH RAE. subst a0 a1 a2.
    unfold CNEWEX_STACK, FR_CRYPTO_new_ex_data, FR_ossl_crypto_new_ex_data_ex, NEWEX_INNER, GETANDLOCK_STACK, FR_get_and_lock, CRWLOCK_STACK,
      CUNLOCK_STACK, FR_mutex_unlock, FR_pthread_mutex_unlock, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock in LO.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    destruct XR as [CR CX]. pose proof (rw_cells_bound _ _ _ _ AD) as ADR. cbn [cells_size csize Nat.add] in ADR.
    pose proof (rclient_range_off_frame _ (HH_RHEAP_block_range H HH) _ _ _ _ _ _ lo HP CR CEIL ltac:(lia)) as ADF.
    pose proof (rclient_range_off_errno _ (HH_RHEAP_block_range H HH) _ _ _ _ _ _ HP CR ltac:(lia) ltac:(lia)) as ADE.
    pose proof (rclient_range_off_auxv _ (HH_RHEAP_block_range H HH) _ _ _ _ _ _ HP CR ltac:(lia) ltac:(lia)) as ADA.
    unfold off_image, IMG_LO, IMG_HI in OFF.
    assert (STK0 : 0 <= ctxph_stack ph).
    { destruct ph; cbn [ctxph_stack]; unfold CTXINIT_STACK, RREALLOC_STACK, RMALLOC_STACK, GETDEFCTX_STACK, CGETLOCAL_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock, FR_get_default_context; lia. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply nx_seg1 with (lo := lo); [exact ST| exact CEIL| lia| exact MI]|].
    intros ms1 (m1 & j & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    pose proof (magree_lib_of_stack_munch _ _ _ _ _ _ HP MU1 WM1 ltac:(apply Forall_cons; [cbn; lia| apply Forall_nil])) as AG1.
    assert (XP1 : xpres LB (bv_unsigned sp) ((ad, ad + 16) :: ctxph_foot ph) m m1).
    { eapply xpres_of_munch; [exact MU1| exact WM1| | exact HB]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    apply (rw_cells_transport usegs _ m m1 _ _ AD) in MU1 as AD1; [| exact WM1| cbn; lia].
    (* [comment removed for export] *)
    pose proof getglobal_spec as GG. unfold getglobal_stmt, getdefctx_stmt_at, getdefctx_stmt_for in GG.
    eapply (sr_seq H HH).
    { eapply (GG ph) with (lo := lo) (B := B) (LB := LB) (s := s); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact KREL| exact BUD| exact BUDC| exact BUDB| exact ST1| exact CEIL| exact MI1| exact TP].
      all: lazymatch goal with
           | |- hs_RHEAP _ _ _ _ => eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]; apply Forall_cons; [left; cbn; lia| apply Forall_nil]
           | |- hs_rauxv_ok _ _ _ => eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]; unfold RAUXV_CELL; apply Forall_cons; [cbn; lia| apply Forall_nil]
           | |- _ mod 16 = 0 => clear - SPA SPR LO STK0; lia
           | |- rw_cells _ _ _ _ => eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1| subst tp; rewrite errno_RATP; unfold RERRNO; cbn; lia]
           | |- MEMFLAG _ _ => eapply MEMFLAG_across; [exact MU1| exact WM1| unfold A_mem_inited; cbn; lia| exact MF]
           | |- IMPL_mem _ => eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]
           | |- GOT_mem _ => eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]
           | |- ECH_LibState.relro_lib _ => eapply relro_lib_munch; [exact RL| exact MU1| apply Forall_cons; [unfold RELRO_LO, RELRO_HI; cbn; lia| apply Forall_nil]]
           | |- CTXPH _ _ _ => eapply CTXPH_frame; [exact CPH| exact AG1]
           | |- _ mod 2 = 0 => unfold NX_RA; rewrite unsigned_lit by lia; reflexivity
           | |- _ => try lia; try (unfold GETGLOBAL_STACK, FR_ossl_lib_ctx_get_ex_data_global in *; lia)
           end. }
    clear GG. intros [ms2 mo2] PO. unfold getdefctx_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & s2' & LBN & x &
                    -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & HEAP2 & DELTA & CPH2 & KEYS & MF2 & IM2 & GM2 & RL2 & XP2).
    rewrite (unsigned_lit (bv_unsigned sp + -192)) in ST2, XP2 by lia. subst tp. rewrite errno_RATP in ERR2.
    cbn [CTXPH] in CPH2. destruct CPH2 as (CS2 & EX2 & OI2).
    assert (HB2 := HH_blocks_below H HH _ _ _ HEAP2).
    assert (SUBN : forall b, In b LB -> In b (LBN ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
    assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -192) (nx_frame j s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)).
    { eapply xpres_rw_cells'; [exact XP2| exact FR1| left; cbn; lia|]. ctx_x_windows. }
    assert (AD2 : rw_cells usegs m2 ad [C8 (wz c0); C8 (wz k0)]).
    { eapply xpres_rw_cells'; [exact XP2| exact AD1| | apply Forall_ctxph_foot; exact CX].
      destruct CR as [K|[K|(bb & Hbb & K1 & K2)]]; [left; lia| right; left; exact K| right; right; exists bb; auto]. }
    (* [comment removed for export] *)
    pose proof EX2 as EX2'. destruct EX2' as (BIN & BSZ & BRR & BMX). pose proof BRR as (B1 & _ & _ & B4 & B5). unfold MUTEX_SIZE in B4, B5, BSZ.
    assert (SEP : ad + 16 <= blk_addr (cx_exlock x) \/ blk_addr (cx_exlock x) + MUTEX_SIZE <= ad).
    { destruct ph as [|x0].
      - (* [comment removed for export] *)
        cbn [ctxph_delta] in DELTA. destruct DELTA as (_ & _ & _ & BNEW & _).
        unfold MUTEX_SIZE. destruct CR as [K|[K|(bb & Hbb & K1 & K2)]]; [lia| lia|].
        assert (NE : blk_id bb <> blk_id (cx_exlock x)).
        { eapply nodup_ids_app_ne with (l1 := LB) (l2 := LBN); [| exact Hbb| exact BNEW].
          eapply Permutation_NoDup; [apply Permutation_map; apply Permutation_app_comm| exact (HH_RHEAP_blocks_nodup H HH _ _ _ HEAP2)]. }
        pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ bb (cx_exlock x) HEAP2 (SUBN _ Hbb) BIN NE) as D. rewrite BSZ in D. lia.
      - cbn [ctxph_delta] in DELTA. destruct DELTA as [-> ->]. exact (SEPR x0 eq_refl). }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL2| eapply nx_seg2 with (lo := lo) (LB := LBN ++ LB) (x := x);
      try first [exact ADP| exact ADAL| exact AD2| exact CS2| exact EX2| exact SEP| exact ADF| exact FR2| exact ST2| exact CEIL| exact MI2| exact IM2| exact GM2| exact RAE];
      try reflexivity; try (unfold off_image, IMG_LO, IMG_HI; lia);
      try (unfold NEWEX_INNER, GETANDLOCK_STACK, FR_get_and_lock, CRWLOCK_STACK, CUNLOCK_STACK, FR_mutex_unlock, FR_pthread_mutex_unlock, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock; lia)|].
    intros ms3 PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & MU3 & WM3 & MI3 & ST3 & CS3 & EX3 & AD3 & IM3 & GM3).
    unfold mutex_foot in MU3.
    apply (sr_done H HH). unfold cnewex_post. cbn [cfg_ms cfg_model].
    exists v0, v1, v2, c1, c2, c3, c4, c5, c6, c7, v3, v4, v5, v6, m3, errv2, s2', LBN, x.
    split; [reflexivity|]. split; [exact KREL2|]. split; [exact MP2|]. split; [exact MI3|]. split; [exact ST3|].
    split. { rewrite errno_RATP. eapply rw_cells_transport; [exact ERR2| exact MU3| exact WM3|]. unfold RERRNO in *. cbn. lia. }
    split. { eapply (HH_rauxv_frame H HH); [exact AUX2| exact MU3| exact WM3|]. unfold RAUXV_CELL in *.
             apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    split. { eapply (HH_RHEAP_frame H HH); [exact HEAP2| exact MU3| exact WM3|].
             apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
             - apply (rclient_range_write_ok _ (bv_unsigned sp)); [| lia]. destruct CR as [K|[K|(bb & Hbb & K1 & K2)]]; [left; exact K| right; left; exact K| right; right; exists bb; auto].
             - right; right. exists (cx_exlock x). split; [exact BIN| cbn; lia]. }
    split; [exact DELTA|].
    split; [split; [exact CS3| split; [exact EX3| exact OI2]]|].
    split. { intros E. specialize (KEYS E). destruct KEYS as (K1 & K2 & K3). unfold CTX_keys.
             unfold A_next_key, A_key_lock, A_td_cancelbuf in *.
             assert (CXF : forall A n, In (A, A + n) [(A_next_key, A_key_lock + 8); (A_td_cancelbuf, A_td_cancelbuf + 16)] -> True) by auto.
             split; [| split]; (eapply rw_cells_transport; [eassumption| exact MU3| exact WM3|]);
               unfold A_next_key, A_key_lock, A_td_cancelbuf; cbn; lia. }
    split; [exact AD3|].
    split; [eapply MEMFLAG_across; [exact MU3| exact WM3| unfold A_mem_inited; cbn; lia| exact MF2]|].
    split; [exact IM3|]. split; [exact GM3|].
    split; [eapply relro_lib_munch; [exact RL2| exact MU3|]; unfold RELRO_LO, RELRO_HI; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil|].
    eapply xpres_trans; [exact XP1|].
    eapply xpres_trans; [eapply xpres_weaken; [exact XP2| lia| auto| intros q Hq; right; exact Hq]|].
    eapply xpres_of_munch_eq; [exact MU3| exact WM3|].
    intros q Hq [QC QX0]. cbn [outside].
    assert (QX : ~ (ad <= q < ad + 16)) by (intros K; apply QX0; left; exact K).
    destruct (Z.eq_dec 0 0) as [_|NE0]; [| lia].
    assert (QB : q < lo \/ bv_unsigned sp <= q).
    { destruct QC as [K|[[K _]|(bb & Hbb & Hr)]]; [right; exact K| left; lia| left]. pose proof (HB bb Hbb). lia. }
    destruct (Z_lt_dec q (blk_addr (cx_exlock x) + 4)) as [L1|L1]; [left; cbn in QX |- *; repeat split; lia|].
    destruct (Z_lt_dec q (blk_addr (cx_exlock x) + 8)) as [L2|L2]; [| left; cbn in QX |- *; repeat split; lia].
    right. unfold EXLOCK, MUTEX in EX2, EX3. destruct EX2 as (_ & _ & _ & XM2). destruct EX3 as (_ & _ & _ & XM3).
    eapply (rw_cells_same_raw m2 m3); [exact XM2| exact XM3| cbn; lia| cbn; lia].
  Qed.
End W.
