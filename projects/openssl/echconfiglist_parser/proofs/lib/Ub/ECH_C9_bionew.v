(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface F_memcpy ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_KitH ECH_Rep ECH_LibState ECH_LibStateMF ECH_LibFrame ECH_C0_stmt ECH_C2_stmt ECH_C1_stmt ECH_C1_malloc ECH_C3_stmt ECH_C3_newex ECH_C3_phase ECH_C6_stmt ECH_C7_stmt ECH_C7_read ECH_C7_new ECH_C8_stmt ECH_C8_small ECH_C9_stmt ECH_C9_new ECH_UbKit.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HX : heap_sr_hyps_x H.
  Let HH : heap_sr_hyps H := proj1 HX.
  Let PERM : RHEAP_perm_law H := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HX))))).

  Local Ltac errno_across ERR MU WM :=
    eapply (rw_cells_transport usegs _ _ _ _ _ ERR MU WM); unfold RERRNO; hcb; cbn; lia.
  Local Ltac static_tac := right; left; unfold A_b64_method, O_METH_BREAD, A_next_key, A_key_lock, A_td_cancelbuf, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK; cbn; lia.
  Local Ltac ustk := unfold BIONEW_B64_STACK, B64NEW_STACK, ENCNEW_STACK, CZALLOC_STACK, CMALLOC_STACK, CNEWEX_READY_STACK, NEWEX_INNER, GETANDLOCK_STACK, GETDEFCTX_STACK,
      FR_BIO_new, FR_BIO_new_ex, FR_b64_new, FR_EVP_ENCODE_CTX_new, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, RMALLOC_STACK, FR_CRYPTO_new_ex_data, FR_ossl_crypto_new_ex_data_ex,
      FR_ossl_lib_ctx_get_ex_data_global, FR_get_default_context, FR_get_and_lock, CRWLOCK_STACK, CUNLOCK_STACK, FR_mutex_unlock, FR_pthread_mutex_unlock,
      FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock, CGETLOCAL_STACK.
  Local Ltac ustk_in H0 := unfold BIONEW_B64_STACK, B64NEW_STACK, ENCNEW_STACK, CZALLOC_STACK, CMALLOC_STACK, CNEWEX_READY_STACK, NEWEX_INNER, GETANDLOCK_STACK, GETDEFCTX_STACK,
      FR_BIO_new, FR_BIO_new_ex, FR_b64_new, FR_EVP_ENCODE_CTX_new, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, RMALLOC_STACK, FR_CRYPTO_new_ex_data, FR_ossl_crypto_new_ex_data_ex,
      FR_ossl_lib_ctx_get_ex_data_global, FR_get_default_context, FR_get_and_lock, CRWLOCK_STACK, CUNLOCK_STACK, FR_mutex_unlock, FR_pthread_mutex_unlock,
      FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock, CGETLOCAL_STACK in H0.
  Local Ltac mf_windows := unfold memflag_foot, A_mem_inited, A_b64_method; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil.

  (* [comment removed for export] *)
  Lemma magree_lib_of_xpres_bn : forall LB SP X m m',
    xpres LB SP X m m' -> magree (fun a => lib_addr LB a /\ ~ rin_ivs X a) m m'.
  Proof.
    intros LB SP X m m' XP a Ha [HL HXa]. apply XP; [exact Ha|]. split; [| exact HXa].
    destruct HL as [HL|HBk]; [| right; right; exact HBk].
    right; left. unfold LIBX, LIBX0 in HL. cbn [rin_ivs fst snd] in HL. unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK. lia.
  Qed.
  Lemma relro_lib_xpres_bn : forall LB SP X m m',
    ECH_LibState.relro_lib m -> xpres LB SP X m m' -> (forall a, RELRO_LO <= a < RELRO_HI -> ~ rin_ivs X a) -> ECH_LibState.relro_lib m'.
  Proof.
    intros LB SP X m m' RL XP NX a Ha Hn. destruct (XP a) as [E _].
    - unfold RELRO_LO, RELRO_HI in Ha. lia.
    - split; [| apply NX; exact Ha]. right; left. unfold ralloc_static, RELRO_LO, RELRO_HI, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK in *. lia.
    - rewrite E. apply RL; assumption.
  Qed.
  Lemma magree_lib_of_block_munch_bn : forall s LB m0 m m' p A n,
    hs_RHEAP H s ((p, A, n) :: LB) m0 -> rblock_range A n -> munch [(A, A + n)] m m' -> wmono usegs m m' -> magree (lib_addr LB) m m'.
  Proof.
    intros s LB m0 m m' p A n HP BR MU WM. hcb. eapply magree_of_munch; [exact MU| exact WM|].
    intros a Ha HL. cbn. split; [| exact I].
    destruct HL as [HL|HBk].
    - unfold LIBX, LIBX0 in HL. cbn [rin_ivs fst snd] in HL. destruct BR as (_ & _ & NN & _ & BI). lia.
    - pose proof (HH_fresh_outside H HH _ _ _ _ _ _ hceil a HP (Z.le_refl hceil) ltac:(right; right; exact HBk)). lia.
  Qed.
  Lemma CTXPH_mono_bn : forall L L' (SUB : forall b, In b L -> In b L') m ph, CTXPH L m ph -> CTXPH L' m ph.
  Proof.
    intros L L' SUB m [|x0] C; cbn [CTXPH] in *; [exact C|]. destruct C as [CS [EX (po & pi & O1 & O2)]].
    split; [exact CS|]. split; [| exists po, pi; split; apply SUB; assumption].
    destruct EX as (E1 & E2 & E3 & E4). split; [apply SUB; exact E1|]. split; [exact E2|]. split; [exact E3| exact E4].
  Qed.

  Lemma bionew_b64_spec : bionew_b64_stmt H.
  Proof.
    unfold bionew_b64_stmt. intros until errv.
    intros A0 HP KREL BUD BUDC BUDB AUX SPB ST CEIL LO ERR MI TP MF IM GM METH RL CPH RAE.
    ustk_in LO.
    unfold B64F_BYTES, BIO_SIZE, B64CTX_SIZE in BUD.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (HB := HH_blocks_below H HH _ _ _ HP). subst tp. rewrite errno_RATP in ERR.
    cbn [CTXPH] in CPH. destruct CPH as [CS [EX OI]]. pose proof EX as (XIN & XSZ & XRR & XM).
    destruct (cx_exlock x) as [[xq xa] xn] eqn:EXB. cbn [blk_addr blk_size blk_id fst snd] in XIN, XSZ, XRR, XM. unfold MUTEX_SIZE in XSZ. subst xn.
    pose proof XRR as (XP1 & _ & _ & XH & XI). unfold MUTEX_SIZE in XH, XI. hide XI.
    unfold METH_b64, O_METH_BREAD in METH.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply bn_seg1 with (lo := lo); [exact A0| exact ST| exact CEIL| lia| exact MI]|].
    intros ms1 (m1 & j1 & -> & MU1 & WM1 & MI1 & ST1 & F01).
    pose proof (magree_lib_of_stack_munch H HX _ _ _ _ _ _ HP MU1 WM1 ltac:(apply Forall_cons; [cbn; lia| apply Forall_nil])) as AG1.
    assert (XP01 : xpres LB (bv_unsigned sp) memflag_foot m m1).
    { eapply xpres_of_munch; [exact MU1| exact WM1| | exact HB]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    apply (rw_cells_transport usegs _ m m1 _ _ METH) in MU1 as METH1; [| exact WM1| unfold A_b64_method; cbn; lia].
    assert (CS1 : CTX_statics m1 x) by (eapply (CTX_statics_frame LB); [exact CS| exact AG1]).
    assert (EX1 : EXLOCK LB m1 (xq, xa, 40)) by (eapply EXLOCK_frame; [exact EX| exact AG1]).
    (* [comment removed for export] *)
    pose proof (czalloc_spec H HH) as CZ. unfold czalloc_stmt, czalloc_stmt_gen in CZ.
    eapply (sr_seq H HH).
    { eapply CZ with (lo := lo) (B := B) (LB := LB) (s := s) (v := v) (num := 128) (size := 1); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact KREL| exact ST1| exact CEIL| exact MI1].
      all: lazymatch goal with
           | |- hs_RHEAP _ _ _ _ => eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]; apply Forall_cons; [left; cbn; lia| apply Forall_nil]
           | |- lb_big _ + _ <= _ => rewrite big1_small by (unfold BIGB; lia); lia
           | |- hs_rauxv_ok _ _ _ => eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]; unfold RAUXV_CELL; apply Forall_cons; [cbn; lia| apply Forall_nil]
           | |- rw_cells _ _ _ _ => rewrite errno_RATP; errno_across ERR MU1 WM1
           | |- MEMFLAG _ _ => eapply MEMFLAG_across; [exact MU1| exact WM1| unfold A_mem_inited; cbn; lia| exact MF]
           | |- IMPL_mem _ => eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]
           | |- GOT_mem _ => eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]
           | |- _ => try (ustk; lia); try lia
           end.
      all: match goal with |- ?G => idtac "CZ1-LEFT:" G end. }
    clear CZ. intros [ms2 mo2] PO. unfold czalloc_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A & p1 & s2' &
                    -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & XP2 & BR1 & HEAP2 & BLK2 & MF2 & IM2 & GM2).
    rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST2, XP2 by lia. rewrite errno_RATP in ERR2. change (128 * 1) with 128 in BR1, HEAP2, BLK2.
    pose proof BR1 as (AP & AAL & _ & AH & AI).
    set (LB1 := (p1, A, 128) :: LB) in *.
    assert (SUB01 : forall b, In b LB -> In b LB1) by (intros b Hb; right; exact Hb).
    assert (HB1 := HH_blocks_below H HH _ _ _ HEAP2).
    assert (F02 : rw_cells usegs m2 (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2); [exact F01| left; cbn; lia| mf_windows]. }
    assert (METH2 : rw_cells usegs m2 (A_b64_method + 32)
      [C8 (wz P_bread_conv); C8 (wz P_b64_read); C8 (wz P_b64_puts); C8 (wz 0); C8 (wz P_b64_ctrl); C8 (wz P_b64_new); C8 (wz P_b64_free); C8 (wz P_b64_callback_ctrl)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2); [exact METH1| static_tac| mf_windows]. }
    assert (RL2 : ECH_LibState.relro_lib m2).
    { eapply relro_lib_xpres_bn; [| exact XP2|]. { eapply relro_lib_munch; [exact RL| exact MU1|]. apply Forall_cons; [unfold RELRO_LO, RELRO_HI; cbn; lia| apply Forall_nil]. }
      intros a Ha. unfold memflag_foot, A_mem_inited, RELRO_LO, RELRO_HI in *. cbn. lia. }
    pose proof (magree_lib_of_xpres_bn _ _ _ _ _ XP2) as AG2.
    assert (CS2 : CTX_statics m2 x).
    { eapply (CTX_statics_frame_mf LB); [exact CS1|]. eapply magree_mono; [exact AG2|]. intros a [HL HF]. split; [exact HL|]. unfold memflag_foot. cbn. unfold A_mem_inited in *. lia. }
    assert (EX2 : EXLOCK LB1 m2 (xq, xa, 40)).
    { assert (K : EXLOCK LB m2 (xq, xa, 40)).
      { eapply EXLOCK_frame_mf; [exact EX1|]. eapply magree_mono; [exact AG2|]. intros a [HL HF]. split; [exact HL|]. unfold memflag_foot. cbn. unfold A_mem_inited in *. lia. }
      destruct K as (K1 & K2). split; [apply SUB01; exact K1| exact K2]. }
    (* [comment removed for export] *)
    pose proof (HH_fresh_disjoint_client H HH _ _ _ _ _ _ (bv_unsigned sp) xa 40 HEAP2 ltac:(right; right; exists (xq, xa, 40); split; [exact XIN| cbn; lia]) ltac:(lia) ltac:(lia)) as DJ_A_x. hide DJ_A_x.
    apply bio_zero_recut in BLK2.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL2| eapply bn_seg2; [exact AP| exact AH| exact AAL| exact BLK2| exact MI2]|].
    intros ms3 (m3 & -> & MU3 & WM3 & MI3 & BA3).
    unfold BIO_SIZE in MU3.
    apply (stk_transport_disjoint usegs _ m2 m3 _ _ ST2) in MU3 as ST3; [| exact WM3| cbn; lia].
    apply (rw_cells_transport usegs _ m2 m3 _ _ F02) in MU3 as F03; [| exact WM3| cbn; lia].
    apply (rw_cells_transport usegs _ m2 m3 _ _ METH2) in MU3 as METH3; [| exact WM3| unfold A_b64_method; cbn; lia].
    apply (rw_cells_transport usegs _ m2 m3 _ _ ERR2) in MU3 as ERR3; [| exact WM3| unfold RERRNO; cbn; lia].
    assert (AUX3 : hs_rauxv_ok H m3 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX2| exact MU3| exact WM3|]. unfold RAUXV_CELL. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    assert (HEAP3 : hs_RHEAP H s2' LB1 m3).
    { eapply (HH_RHEAP_frame H HH); [exact HEAP2| exact MU3| exact WM3|]. apply Forall_cons; [| apply Forall_nil].
      right; right. exists (p1, A, 128). split; [left; reflexivity| cbn; lia]. }
    assert (MF3 : MEMFLAG m3 1) by (eapply MEMFLAG_across; [exact MU3| exact WM3| unfold A_mem_inited; cbn; lia| exact MF2]).
    assert (IM3 : IMPL_mem m3) by (eapply IMPL_across; [exact MU3| exact WM3| unfold A_malloc_impl; cbn; lia| exact IM2]).
    assert (GM3 : GOT_mem m3) by (eapply GOT_across; [exact MU3| exact WM3| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM2]).
    assert (RL3 : ECH_LibState.relro_lib m3).
    { eapply relro_lib_munch; [exact RL2| exact MU3|]. apply Forall_cons; [unfold RELRO_LO, RELRO_HI; cbn; lia| apply Forall_nil]. }
    pose proof (magree_lib_of_block_munch_bn _ _ _ _ _ _ _ _ HEAP2 BR1 MU3 WM3) as AG3.
    assert (CS3 : CTX_statics m3 x) by (eapply (CTX_statics_frame LB); [exact CS2| exact AG3]).
    assert (EX3 : EXLOCK LB1 m3 (xq, xa, 40)).
    { destruct EX2 as [K1 K2]. assert (K : EXLOCK LB m2 (xq, xa, 40)) by (split; [exact XIN| exact K2]).
      pose proof (EXLOCK_frame _ _ _ _ K AG3) as [_ K3]. split; [exact K1| exact K3]. }
    assert (XP23 : xpres LB (bv_unsigned sp) memflag_foot m2 m3).
    { eapply (xpres_of_munch_fresh H HH); [exact HEAP2| lia| exact MU3| exact WM3|]. apply Forall_cons; [right; left; cbn; lia| apply Forall_nil]. }
    destruct (bio_cells_split_ex _ _ _ BA3) as [BA3a EXD3].
    (* [comment removed for export] *)
    pose proof (@cnewex_ready_spec HCEIL) as CNX. unfold cnewex_ready_stmt in CNX. cbv zeta in CNX.
    eapply (sr_evt_krel H HH).
    { exact KREL2. }
    { eapply CNX with (lo := lo) (LB := LB1) (x := x) (obj := A) (ad := A + O_BIO_EXDATA) (c0 := 0) (k0 := 0); rewrite ?EXB; cbn [blk_addr blk_size fst snd];
        unfold O_BIO_EXDATA; rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact CS3| exact EX3| exact ST3| exact CEIL| exact MI3| exact IM3| exact GM3].
      all: lazymatch goal with
           | |- rw_cells _ _ _ _ => unfold O_BIO_EXDATA in EXD3; exact EXD3
           | |- off_image _ _ => unfold off_image, IMG_LO, IMG_HI; lia
           | |- _ \/ _ => unhide DJ_A_x; unfold MUTEX_SIZE; lia
           | |- _ mod 2 = 0 => unfold NEX_RA2; rewrite unsigned_lit by lia; reflexivity
           | |- _ => try (ustk; lia); try lia
           end.
      all: match goal with |- ?G => idtac "CNX-LEFT:" G end. }
    clear CNX. intros ms4 PO. unfold c3_post in PO.
    destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m4 & -> & -> & MU4 & WM4 & MI4 & ST4 & CS4 & EX4 & EXD4).
    rewrite (unsigned_lit (bv_unsigned sp + -48)) in MU4, ST4 by lia. rewrite EXB in MU4. cbn [blk_addr fst snd] in MU4. unfold mutex_foot, O_BIO_EXDATA in MU4.
    assert (HEAP4 : hs_RHEAP H s2' LB1 m4).
    { eapply (HH_RHEAP_frame H HH); [exact HEAP3| exact MU4| exact WM4|].
      apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; right; exists (p1, A, 128); split; [left; reflexivity| cbn; lia]|].
      apply Forall_cons; [right; right; exists (xq, xa, 40); split; [right; exact XIN| cbn; lia]| apply Forall_nil]. }
    unhide XI.
    assert (AUX4 : hs_rauxv_ok H m4 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX3| exact MU4| exact WM4|]. unfold RAUXV_CELL. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
    apply (rw_cells_transport usegs _ m3 m4 _ _ ERR3) in MU4 as ERR4; [| exact WM4| unfold RERRNO; cbn; lia].
    assert (MF4 : MEMFLAG m4 1) by (eapply MEMFLAG_across; [exact MU4| exact WM4| unfold A_mem_inited; cbn; lia| exact MF3]).
    assert (IM4 : IMPL_mem m4) by (eapply IMPL_across; [exact MU4| exact WM4| unfold A_malloc_impl; cbn; lia| exact IM3]).
    assert (GM4 : GOT_mem m4) by (eapply GOT_across; [exact MU4| exact WM4| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM3]).
    apply (rw_cells_transport usegs _ m3 m4 _ _ METH3) in MU4 as METH4; [| exact WM4| unfold A_b64_method; cbn; lia].
    apply (rw_cells_transport usegs _ m3 m4 _ _ F03) in MU4 as F04; [| exact WM4| cbn; lia].
    unhide DJ_A_x. apply (rw_cells_transport usegs _ m3 m4 _ _ BA3a) in MU4 as BA4a; [| exact WM4| cbn; lia]. hide DJ_A_x.
    assert (RL4 : ECH_LibState.relro_lib m4).
    { eapply relro_lib_munch; [exact RL3| exact MU4|]. unfold RELRO_LO, RELRO_HI. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
    hide XI.
    pose proof (bio_cells_join_ex _ _ _ BA4a EXD4) as BA4.
    assert (XP34 : xpres LB (bv_unsigned sp) memflag_foot m3 m4).
    { eapply xpres_of_munch_eq; [exact MU4| exact WM4|].
      intros q Hq [QC QX]. cbn [outside].
      assert (CASE : (xa + 4 <= q < xa + 8) \/ ~ (xa + 4 <= q < xa + 8)) by lia.
      destruct CASE as [INX|OUTX].
      - right. unfold EXLOCK, MUTEX in EX3, EX4. rewrite EXB in EX4. cbn [blk_addr blk_size fst snd] in EX3, EX4.
        destruct EX3 as (_ & _ & _ & XM3). destruct EX4 as (_ & _ & _ & XM4).
        unhide XI. eapply (rw_cells_same_raw m3 m4); [exact XM3| exact XM4| cbn; lia| cbn; lia].
      - left. pose proof (HH_fresh_outside H HH _ _ _ _ _ _ (bv_unsigned sp) q HEAP2 ltac:(lia) QC) as QA.
        destruct QC as [K|[[[K1 K2] _]|(b & Hb & Hr)]]; [repeat split; lia| repeat split; lia|].
        pose proof (HB b Hb) as BLO. repeat split; lia. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL2| eapply bn_seg3 with (lo := lo); rewrite ?unsigned_lit by lia;
      first [exact AP| unfold BIO_SIZE; exact AH| unfold METH_b64, O_METH_BREAD; exact METH4| exact ST4| exact CEIL| lia| exact MI4]|].
    intros ms5 (m5 & j2 & -> & MU5 & WM5 & MI5 & ST5 & F25 & METH5).
    rewrite !(unsigned_lit (bv_unsigned sp + -48)) in MU5, ST5, F25 |- * by lia.
    replace (bv_unsigned sp + -48 + -48) with (bv_unsigned sp + -96) in MU5, ST5, F25 |- * by lia.
    apply (rw_cells_transport usegs _ m4 m5 _ _ F04) in MU5 as F05; [| exact WM5| cbn; lia].
    apply (rw_cells_transport usegs _ m4 m5 _ _ BA4) in MU5 as BA5; [| exact WM5| cbn; lia].
    apply (rw_cells_transport usegs _ m4 m5 _ _ ERR4) in MU5 as ERR5; [| exact WM5| unfold RERRNO; cbn; lia].
    assert (HEAP5 : hs_RHEAP H s2' LB1 m5).
    { eapply (HH_RHEAP_frame H HH); [exact HEAP4| exact MU5| exact WM5|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (AUX5 : hs_rauxv_ok H m5 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX4| exact MU5| exact WM5|]. unfold RAUXV_CELL. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    assert (MF5 : MEMFLAG m5 1) by (eapply MEMFLAG_across; [exact MU5| exact WM5| unfold A_mem_inited; cbn; lia| exact MF4]).
    assert (IM5 : IMPL_mem m5) by (eapply IMPL_across; [exact MU5| exact WM5| unfold A_malloc_impl; cbn; lia| exact IM4]).
    assert (GM5 : GOT_mem m5) by (eapply GOT_across; [exact MU5| exact WM5| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM4]).
    assert (RL5 : ECH_LibState.relro_lib m5).
    { eapply relro_lib_munch; [exact RL4| exact MU5|]. apply Forall_cons; [unfold RELRO_LO, RELRO_HI; cbn; lia| apply Forall_nil]. }
    pose proof (magree_lib_of_stack_munch H HX _ _ _ _ _ _ HEAP4 MU5 WM5 ltac:(apply Forall_cons; [cbn; lia| apply Forall_nil])) as AG5.
    assert (CS5 : CTX_statics m5 x) by (eapply (CTX_statics_frame LB1); [exact CS4| exact AG5]).
    assert (EX5 : EXLOCK LB1 m5 (xq, xa, 40)) by (rewrite EXB in EX4; eapply EXLOCK_frame; [exact EX4| exact AG5]).
    assert (XP45 : xpres LB (bv_unsigned sp) memflag_foot m4 m5).
    { eapply xpres_of_munch; [exact MU5| exact WM5| | exact HB]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    (* [comment removed for export] *)
    pose proof (czalloc_spec H HH) as CZ. unfold czalloc_stmt, czalloc_stmt_gen in CZ.
    eapply (sr_seq H HH).
    { eapply CZ with (lo := lo) (B := B) (LB := LB1) (s := s2') (v := 1) (num := 2584) (size := 1); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact HEAP5| exact KREL2| exact AUX5| exact ST5| exact CEIL| exact MI5| exact MF5| exact IM5| exact GM5].
      all: lazymatch goal with
           | |- lb_bytes _ + _ <= _ => unfold LB1; rewrite lb_bytes_cons; cbn [blk_size snd]; lia
           | |- Z.of_nat (length _) + _ <= _ => unfold LB1; cbn [length]; lia
           | |- lb_big _ + _ <= _ => unfold LB1; rewrite lb_big_cons; cbn [blk_size snd]; rewrite (big1_small 128) by (unfold BIGB; lia); change (big1 (2584 * 1)) with 1; lia
           | |- rw_cells _ _ _ _ => rewrite errno_RATP; exact ERR5
           | |- _ => try (ustk; lia); try lia
           end.
      all: match goal with |- ?G => idtac "CZ2-LEFT:" G end. }
    clear CZ. intros [ms6 mo6] PO. unfold czalloc_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m6 & errv6 & C & p2 & s6' &
                    -> & KREL6 & MP6 & MI6 & ST6 & ERR6 & AUX6 & XP6 & BR2 & HEAP6 & BLK6 & MF6 & IM6 & GM6).
    rewrite (unsigned_lit (bv_unsigned sp + -96)) in ST6, XP6 by lia. rewrite errno_RATP in ERR6. change (2584 * 1) with 2584 in BR2, HEAP6, BLK6.
    pose proof BR2 as (CP & CAL & _ & CH & CI). hide CI.
    set (LB2 := (p2, C, 2584) :: LB1) in *.
    assert (SUB12 : forall b, In b LB1 -> In b LB2) by (intros b Hb; right; exact Hb).
    assert (AIN2 : In (p1, A, 128) LB2) by (apply SUB12; left; reflexivity).
    assert (HB2 := HH_blocks_below H HH _ _ _ HEAP6).
    assert (F06 : rw_cells usegs m6 (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP6); [exact F05| left; cbn; lia| mf_windows]. }
    assert (F26 : rw_cells usegs m6 (bv_unsigned sp + -96) [CB 8 j2; C8 (Z_to_bv 64 (A + O_BIO_EXDATA)); C8 (Z_to_bv 64 A_b64_method); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (bv_unsigned sp)); C8 (Z_to_bv 64 NEX_RA3)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP6); [exact F25| left; cbn; lia| mf_windows]. }
    assert (METH6 : rw_cells usegs m6 (A_b64_method + 32)
      [C8 (wz P_bread_conv); C8 (wz P_b64_read); C8 (wz P_b64_puts); C8 (wz 0); C8 (wz P_b64_ctrl); C8 (wz P_b64_new); C8 (wz P_b64_free); C8 (wz P_b64_callback_ctrl)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP6); [unfold METH_b64, O_METH_BREAD in METH5; exact METH5| static_tac| mf_windows]. }
    assert (BA6 : rw_cells usegs m6 A (bio_cells bio_hdr1_b64)).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP6); [exact BA5| right; right; exists (p1, A, 128); split; [left; reflexivity| cbn; lia]| mf_windows]. }
    assert (RL6 : ECH_LibState.relro_lib m6).
    { eapply relro_lib_xpres_bn; [exact RL5| exact XP6|]. intros a Ha. unfold memflag_foot, A_mem_inited, RELRO_LO, RELRO_HI in *. cbn. lia. }
    pose proof (magree_lib_of_xpres_bn _ _ _ _ _ XP6) as AG6.
    assert (CS6 : CTX_statics m6 x).
    { eapply (CTX_statics_frame_mf LB1); [exact CS5|]. eapply magree_mono; [exact AG6|]. intros a [HL HF]. split; [exact HL|]. unfold memflag_foot. cbn. unfold A_mem_inited in *. lia. }
    assert (EX6 : EXLOCK LB2 m6 (xq, xa, 40)).
    { assert (K : EXLOCK LB1 m6 (xq, xa, 40)).
      { eapply EXLOCK_frame_mf; [exact EX5|]. eapply magree_mono; [exact AG6|]. intros a [HL HF]. split; [exact HL|]. unfold memflag_foot. cbn. unfold A_mem_inited in *. lia. }
      destruct K as (K1 & K2). split; [apply SUB12; exact K1| exact K2]. }
    pose proof (HH_fresh_disjoint_client H HH _ _ _ _ _ _ (bv_unsigned sp) xa 40 HEAP6 ltac:(right; right; exists (xq, xa, 40); split; [right; exact XIN| cbn; lia]) ltac:(lia) ltac:(lia)) as DJ_C_x. hide DJ_C_x.
    pose proof (HH_fresh_disjoint_client H HH _ _ _ _ _ _ (bv_unsigned sp) A 128 HEAP6 ltac:(right; right; exists (p1, A, 128); split; [left; reflexivity| cbn; lia]) ltac:(lia) ltac:(lia)) as DJ_C_A. hide DJ_C_A.
    apply b64ctx_zero_recut in BLK6.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL6| eapply bn_seg4; [exact CP| exact CAL| unfold B64CTX_SIZE; exact CH| exact BLK6| exact MI6]|].
    intros ms7 (m7 & -> & MU7 & WM7 & MI7 & BC7).
    unfold B64CTX_SIZE in MU7.
    apply (stk_transport_disjoint usegs _ m6 m7 _ _ ST6) in MU7 as ST7; [| exact WM7| cbn; lia].
    apply (rw_cells_transport usegs _ m6 m7 _ _ F06) in MU7 as F07; [| exact WM7| cbn; lia].
    apply (rw_cells_transport usegs _ m6 m7 _ _ F26) in MU7 as F27; [| exact WM7| cbn; lia].
    apply (rw_cells_transport usegs _ m6 m7 _ _ ERR6) in MU7 as ERR7; [| exact WM7| unhide CI; unfold RERRNO; cbn; lia].
    unhide DJ_C_A. apply (rw_cells_transport usegs _ m6 m7 _ _ BA6) in MU7 as BA7; [| exact WM7| cbn; lia]. hide DJ_C_A.
    assert (METH7 : rw_cells usegs m7 (A_b64_method + 32)
      [C8 (wz P_bread_conv); C8 (wz P_b64_read); C8 (wz P_b64_puts); C8 (wz 0); C8 (wz P_b64_ctrl); C8 (wz P_b64_new); C8 (wz P_b64_free); C8 (wz P_b64_callback_ctrl)]).
    { eapply rw_cells_transport; [exact METH6| exact MU7| exact WM7| unhide CI; unfold A_b64_method; cbn; lia]. }
    assert (AUX7 : hs_rauxv_ok H m7 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX6| exact MU7| exact WM7|]. unhide CI. unfold RAUXV_CELL. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    assert (HEAP7 : hs_RHEAP H s6' LB2 m7).
    { eapply (HH_RHEAP_frame H HH); [exact HEAP6| exact MU7| exact WM7|]. apply Forall_cons; [| apply Forall_nil].
      right; right. exists (p2, C, 2584). split; [left; reflexivity| cbn; lia]. }
    assert (MF7 : MEMFLAG m7 1) by (eapply MEMFLAG_across; [exact MU7| exact WM7| unhide CI; unfold A_mem_inited; cbn; lia| exact MF6]).
    assert (IM7 : IMPL_mem m7) by (eapply IMPL_across; [exact MU7| exact WM7| unhide CI; unfold A_malloc_impl; cbn; lia| exact IM6]).
    assert (GM7 : GOT_mem m7) by (eapply GOT_across; [exact MU7| exact WM7| unhide CI; unfold A_got_CRYPTO_malloc; cbn; lia| exact GM6]).
    assert (RL7 : ECH_LibState.relro_lib m7).
    { eapply relro_lib_munch; [exact RL6| exact MU7|]. unhide CI. apply Forall_cons; [unfold RELRO_LO, RELRO_HI; cbn; lia| apply Forall_nil]. }
    pose proof (magree_lib_of_block_munch_bn _ _ _ _ _ _ _ _ HEAP6 BR2 MU7 WM7) as AG7.
    assert (CS7 : CTX_statics m7 x) by (eapply (CTX_statics_frame LB1); [exact CS6| exact AG7]).
    assert (EX7 : EXLOCK LB2 m7 (xq, xa, 40)).
    { destruct EX6 as [K1 K2]. assert (K : EXLOCK LB1 m6 (xq, xa, 40)) by (split; [right; exact XIN| exact K2]).
      pose proof (EXLOCK_frame _ _ _ _ K AG7) as [_ K3]. split; [exact K1| exact K3]. }
    assert (XP67 : xpres LB1 (bv_unsigned sp) memflag_foot m6 m7).
    { eapply (xpres_of_munch_fresh H HH); [exact HEAP6| lia| exact MU7| exact WM7|]. apply Forall_cons; [right; left; cbn; lia| apply Forall_nil]. }
    (* [comment removed for export] *)
    pose proof (encnew_spec H HH) as EN. unfold encnew_stmt in EN.
    eapply (sr_seq H HH).
    { eapply EN with (lo := lo) (B := B) (LB := LB2) (s := s6') (v := 1); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact HEAP7| exact KREL6| exact AUX7| exact ST7| exact CEIL| exact MI7| exact MF7| exact IM7| exact GM7].
      all: lazymatch goal with
           | |- lb_bytes _ + _ <= _ => unfold LB2, LB1; rewrite !lb_bytes_cons; cbn [blk_size snd]; unfold ENCCTX_SIZE; lia
           | |- Z.of_nat (length _) + _ <= _ => unfold LB2, LB1; cbn [length]; lia
           | |- lb_big _ <= _ => unfold LB2, LB1; rewrite !lb_big_cons; cbn [blk_size snd]; rewrite (big1_small 128) by (unfold BIGB; lia); change (big1 2584) with 1; lia
           | |- rw_cells _ _ _ _ => rewrite errno_RATP; exact ERR7
           | |- _ mod 2 = 0 => unfold B64N_RA2; rewrite unsigned_lit by lia; reflexivity
           | |- context [FR_EVP_ENCODE_CTX_new] => unfold ENCNEW_STACK, FR_EVP_ENCODE_CTX_new, CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, RMALLOC_STACK; lia
           | |- context [ENCNEW_STACK] => unfold ENCNEW_STACK, FR_EVP_ENCODE_CTX_new, CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, RMALLOC_STACK; lia
           | |- _ => try (ustk; lia); try lia
           end.
      all: match goal with |- ?G => idtac "EN-LEFT:" G end. }
    clear EN. intros [ms8 mo8] PO. unfold encnew_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (x0 & x1 & x2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & x3 & x4 & x5 & x6 & m8 & errv8 & E & p3 & s8' &
                    -> & KREL8 & MP8 & MI8 & ST8 & ERR8 & AUX8 & XP8 & HEAP8 & ENC8 & MF8 & IM8 & GM8).
    rewrite (unsigned_lit (bv_unsigned sp + -96)) in ST8, XP8 by lia. rewrite errno_RATP in ERR8. unfold ENCCTX_SIZE in HEAP8.
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HEAP8 ltac:(left; reflexivity)) as BR3. cbn [blk_addr blk_size fst snd] in BR3.
    pose proof BR3 as (EP & _ & _ & EH & EI). hide EI.
    assert (HB3 := HH_blocks_below H HH _ _ _ HEAP8).
    assert (F08 : rw_cells usegs m8 (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP8); [exact F07| left; cbn; lia| mf_windows]. }
    assert (F28 : rw_cells usegs m8 (bv_unsigned sp + -96) [CB 8 j2; C8 (Z_to_bv 64 (A + O_BIO_EXDATA)); C8 (Z_to_bv 64 A_b64_method); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (bv_unsigned sp)); C8 (Z_to_bv 64 NEX_RA3)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP8); [exact F27| left; cbn; lia| mf_windows]. }
    assert (METH8 : rw_cells usegs m8 (A_b64_method + 32)
      [C8 (wz P_bread_conv); C8 (wz P_b64_read); C8 (wz P_b64_puts); C8 (wz 0); C8 (wz P_b64_ctrl); C8 (wz P_b64_new); C8 (wz P_b64_free); C8 (wz P_b64_callback_ctrl)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP8); [exact METH7| static_tac| mf_windows]. }
    assert (BA8 : rw_cells usegs m8 A (bio_cells bio_hdr1_b64)).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP8); [exact BA7| right; right; exists (p1, A, 128); split; [exact AIN2| cbn; lia]| mf_windows]. }
    unhide CI.
    assert (BC8 : rw_cells usegs m8 C b64ctx_cs_cells).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP8); [exact BC7| right; right; exists (p2, C, 2584); split; [left; reflexivity| cbn; lia]| mf_windows]. }
    hide CI.
    assert (RL8 : ECH_LibState.relro_lib m8).
    { eapply relro_lib_xpres_bn; [exact RL7| exact XP8|]. intros a Ha. unfold memflag_foot, A_mem_inited, RELRO_LO, RELRO_HI in *. cbn. lia. }
    pose proof (magree_lib_of_xpres_bn _ _ _ _ _ XP8) as AG8.
    assert (CS8 : CTX_statics m8 x).
    { eapply (CTX_statics_frame_mf LB2); [exact CS7|]. eapply magree_mono; [exact AG8|]. intros a [HL HF]. split; [exact HL|]. unfold memflag_foot. cbn. unfold A_mem_inited in *. lia. }
    assert (EX8 : EXLOCK LB2 m8 (xq, xa, 40)).
    { eapply EXLOCK_frame_mf; [exact EX7|]. eapply magree_mono; [exact AG8|]. intros a [HL HF]. split; [exact HL|]. unfold memflag_foot. cbn. unfold A_mem_inited in *. lia. }
    pose proof (HH_fresh_disjoint_client H HH _ _ _ _ _ _ (bv_unsigned sp) xa 40 HEAP8 ltac:(right; right; exists (xq, xa, 40); split; [right; right; exact XIN| cbn; lia]) ltac:(lia) ltac:(lia)) as DJ_E_x. hide DJ_E_x.
    pose proof (HH_fresh_disjoint_client H HH _ _ _ _ _ _ (bv_unsigned sp) A 128 HEAP8 ltac:(right; right; exists (p1, A, 128); split; [right; left; reflexivity| cbn; lia]) ltac:(lia) ltac:(lia)) as DJ_E_A. hide DJ_E_A.
    pose proof (HH_fresh_disjoint_client H HH _ _ _ _ _ _ (bv_unsigned sp) C 2584 HEAP8 ltac:(right; right; exists (p2, C, 2584); split; [left; reflexivity| cbn; lia]) ltac:(lia) ltac:(lia)) as DJ_E_C. hide DJ_E_C.
    (* [comment removed for export] *)
    rewrite Z_to_bv_bv_unsigned in F28.
    unfold O_BIO_EXDATA in F28. unhide DJ_C_A.
    eapply (sr_evt_krel H HH); [exact KREL8| eapply bn_seg5 with (lo := lo) (i1 := p1) (i2 := p2) (i3 := p3); rewrite ?unsigned_lit by lia;
      first [exact BR1| exact BR2| exact EP| unfold ENCCTX_SIZE; exact EH| exact BA8| exact BC8| unfold METH_b64, O_METH_BREAD; exact METH8| exact F08| exact F28| exact ST8| exact CEIL| exact MI8| exact RAE
            | unfold BIO_SIZE, B64CTX_SIZE; lia| lia]|].
    intros ms9 PO.
    destruct PO as (y0 & y1 & y2 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & y3 & y4 & y5 & y6 & m9 & -> & MU9 & WM9 & MI9 & ST9 & BA9 & BC9 & METH9).
    unfold BIO_SIZE, B64CTX_SIZE in MU9. hide DJ_C_A.
    unhide CI.
    apply (rw_cells_transport usegs _ m8 m9 _ _ ERR8) in MU9 as ERR9; [| exact WM9| unfold RERRNO; cbn; lia].
    assert (AUX9 : hs_rauxv_ok H m9 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX8| exact MU9| exact WM9|]. unfold RAUXV_CELL. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
    assert (MF9 : MEMFLAG m9 1) by (eapply MEMFLAG_across; [exact MU9| exact WM9| unfold A_mem_inited; cbn; lia| exact MF8]).
    assert (IM9 : IMPL_mem m9) by (eapply IMPL_across; [exact MU9| exact WM9| unfold A_malloc_impl; cbn; lia| exact IM8]).
    assert (GM9 : GOT_mem m9) by (eapply GOT_across; [exact MU9| exact WM9| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM8]).
    assert (RL9 : ECH_LibState.relro_lib m9).
    { eapply relro_lib_munch; [exact RL8| exact MU9|]. unfold RELRO_LO, RELRO_HI. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
    assert (HEAP9 : hs_RHEAP H s8' ((p3, E, 92) :: LB2) m9).
    { eapply (HH_RHEAP_frame H HH); [exact HEAP8| exact MU9| exact WM9|].
      apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; right; exists (p1, A, 128); split; [right; exact AIN2| cbn; lia]|].
      apply Forall_cons; [right; right; exists (p2, C, 2584); split; [right; left; reflexivity| cbn; lia]| apply Forall_nil]. }
    assert (AG9 : magree (lib_addr [(xq, xa, 40)]) m8 m9).
    { unhide DJ_A_x. unhide DJ_C_x. eapply magree_of_munch; [exact MU9| exact WM9|]. intros q Hq HL. cbn.
      destruct HL as [HL|(b & [<-|[]] & Hr)].
      - unfold LIBX, LIBX0 in HL. cbn [rin_ivs fst snd] in HL. repeat split; lia.
      - cbn [blk_addr blk_size fst snd] in Hr. repeat split; lia. }
    assert (CS9 : CTX_statics m9 x) by (eapply (CTX_statics_frame [(xq, xa, 40)]); [exact CS8| exact AG9]).
    assert (EXM9 : MUTEX m9 xa 0).
    { destruct EX8 as (_ & K2). assert (K : EXLOCK [(xq, xa, 40)] m8 (xq, xa, 40)) by (split; [left; reflexivity| exact K2]).
      pose proof (EXLOCK_frame _ _ _ _ K AG9) as (_ & _ & _ & K3). exact K3. }
    hide CI.
    (* [comment removed for export] *)
    apply (sr_done H HH). unfold bionew_b64_post. cbn [cfg_ms cfg_model].
    exists y0, y1, y2, f1, f2, f3, f4, f5, f6, f7, y3, y4, y5, y6, m9, errv8, s8', A, (bn_R C E p1 p2 p3).
    cbn [bf_ctx bf_enc bf_id bf_cid bf_eid bf_flags bf_retry bf_nread bf_next bf_prev bn_R blocks_B64F app].
    split; [reflexivity|]. split; [exact KREL8|].
    split; [eapply (mpres_trans H HH); [exact MP2| eapply (mpres_trans H HH); [exact MP6| exact MP8]]|].
    split; [exact MI9|]. split; [exact ST9|]. split; [rewrite errno_RATP; exact ERR9|]. split; [exact AUX9|].
    split.
    { (* [comment removed for export] *)
      eapply PERM; [exact HEAP9|]. unfold LB2, LB1, BIO_SIZE, B64CTX_SIZE.
      lazymatch goal with |- Permutation ?l _ => change (Permutation l ([(p1, A, 128); (p2, C, 2584)] ++ (p3, E, 92) :: LB)) end.
      apply Permutation_cons_app. cbn. apply perm_swap. }
    split.
    { (* [comment removed for export] *)
      cbn [CTXPH]. split; [exact CS9|]. split.
      - rewrite EXB. destruct EX8 as (_ & K2 & K3 & _). split; [| split; [exact K2| split; [exact K3| exact EXM9]]].
        right; right; right. exact XIN.
      - destruct OI as (po & pi & O1 & O2). exists po, pi. split; right; right; right; assumption. }
    split; [exact BA9|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exists (zeros 2528); split; [reflexivity| exact BC9]|].
    split.
    { (* [comment removed for export] *)
      unfold B64F_blocks. cbn [bf_ctx bf_enc bf_id bf_cid bf_eid bf_flags bf_retry bf_nread bf_next bf_prev bn_R]. unfold BIO_SIZE, B64CTX_SIZE.
      split; [left; reflexivity|]. split; [right; left; reflexivity|]. split; [right; right; left; reflexivity|].
      split; [exact BR1|]. split; [exact BR2|]. split; [exact BR3|]. lia. }
    split.
    { (* [comment removed for export] *)
      unhide DJ_C_A. unhide DJ_E_A. unhide DJ_E_C. unfold B64F_apart, BIO_SIZE, B64CTX_SIZE. cbn [bf_ctx bf_enc bn_R].
      split; [exact DJ_C_A|]. split; [exact DJ_E_A| exact DJ_E_C]. }
    split.
    { (* [comment removed for export] *)
      destruct ENC8 as (raw & line & L1e & L2e & CE & LNE & INE & RRE & DU).
      exists raw, line. split; [exact L1e|]. split; [exact L2e|]. split.
      - unhide DJ_E_A. unhide DJ_E_C. eapply rw_cells_transport; [exact CE| exact MU9| exact WM9| cbn; lia].
      - split; [exact LNE|]. split; [right; right; left; reflexivity|]. split; [exact RRE| exact DU]. }
    split; [exact AP|]. split; [exact MF9|]. split; [exact IM9|]. split; [exact GM9|]. split; [exact METH9|]. split; [exact RL9|].
    (* [comment removed for export] *)
    eapply xpres_trans; [exact XP01|].
    eapply xpres_trans; [eapply xpres_weaken; [exact XP2| lia| auto| auto]|].
    eapply xpres_trans; [exact XP23|]. eapply xpres_trans; [exact XP34|]. eapply xpres_trans; [exact XP45|].
    eapply xpres_trans; [eapply xpres_weaken; [exact XP6| lia| exact SUB01| auto]|].
    eapply xpres_trans; [eapply xpres_weaken; [exact XP67| lia| auto| auto]|].
    eapply xpres_trans; [eapply xpres_weaken; [exact XP8| lia| intros b Hb; apply SUB12, SUB01; exact Hb| auto]|].
    eapply xpres_of_munch_gen; [exact MU9| exact WM9|].
    intros q Hq [QC _]. cbn [outside].
    pose proof (HH_fresh_outside H HH _ _ _ _ _ _ (bv_unsigned sp) q HEAP2 ltac:(lia) QC) as QA.
    assert (QC1 : rclient_addr LB1 (bv_unsigned sp) q).
    { destruct QC as [K|[K|(b & Hb & Hr)]]; [left; exact K| right; left; exact K| right; right; exists b; split; [apply SUB01; exact Hb| exact Hr]]. }
    pose proof (HH_fresh_outside H HH _ _ _ _ _ _ (bv_unsigned sp) q HEAP6 ltac:(lia) QC1) as QCC.
    destruct QC as [K|[[[K1 K2] _]|(b & Hb & Hr)]]; [repeat split; lia| unhide CI; repeat split; lia|].
    pose proof (HB b Hb) as BLO. repeat split; lia.
  Qed.
End W.
