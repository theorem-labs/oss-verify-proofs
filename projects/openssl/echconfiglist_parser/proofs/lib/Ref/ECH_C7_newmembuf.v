(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface F_memcpy ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_KitH ECH_Rep ECH_LibState
     ECH_LibStateMF ECH_LibFrame ECH_C0_stmt ECH_C2_stmt ECH_C1_stmt ECH_C1_malloc ECH_C3_stmt ECH_C3_phase ECH_C6_stmt ECH_C6_buf ECH_C7_stmt ECH_C7_read ECH_C7_new.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HX : heap_sr_hyps_x H.
  (* [comment removed for export] *)
  Hypothesis CERTA : getdefctx_fresh_stmt H.
  Let HH : heap_sr_hyps H := proj1 HX.
  Let PERM : RHEAP_perm_law H := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HX))))).

  Local Ltac errno_across ERR MU WM :=
    eapply (rw_cells_transport rsegs _ _ _ _ _ ERR MU WM); unfold RERRNO; hcb; cbn; lia.
  Local Ltac static_tac := right; left; unfold A_mem_buf_method, O_METH_BREAD, A_next_key, A_key_lock, A_td_cancelbuf, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK; cbn; lia.
  Local Ltac mf_windows := unfold memflag_foot, A_mem_inited, A_mem_buf_method; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil.
  (* [comment removed for export] *)
  Local Ltac ctxw :=
    repeat (first [ apply Forall_nil
                  | apply Forall_ctxph_foot
                  | (unfold CTX_X, A_destructor_key, A_defctx_inited, A_tevent_once, A_base_inited, A_in_init_config_key, A_load_strings_once, A_optsdone_lock, A_td_cancelbuf,
                       A_keys, A_next_key, A_key_lock, memflag_foot, A_mem_inited, A_mem_buf_method; cbn [app]; apply Forall_cons; [cbn; lia|]) ]).

  Lemma ctxph_nonneg : forall ph, 0 <= ctxph_bytes ph /\ 0 <= ctxph_cnt ph /\ 0 <= ctxph_big ph /\ 0 <= CNEWEX_STACK ph.
  Proof.
    intros [|x]; cbn [ctxph_bytes ctxph_cnt ctxph_big]; unfold CTXINIT_BYTES, CTXINIT_CNT, CTXINIT_BIG, CNEWEX_STACK, GETGLOBAL_STACK, ctxph_stack, NEWEX_INNER,
      GETANDLOCK_STACK, CUNLOCK_STACK, CTXINIT_STACK, RREALLOC_STACK, RMALLOC_STACK, GETDEFCTX_STACK, CGETLOCAL_STACK, FR_CRYPTO_THREAD_wrap,
      FR_CRYPTO_THREAD_read_lock, FR_get_default_context, FR_CRYPTO_new_ex_data, FR_ossl_crypto_new_ex_data_ex, FR_ossl_lib_ctx_get_ex_data_global,
      FR_get_and_lock, CRWLOCK_STACK, FR_mutex_unlock, FR_pthread_mutex_unlock; lia.
  Qed.

  Lemma ctxph_delta_bounds : forall ph LBN x, ctxph_delta ph LBN x ->
    lb_bytes LBN <= ctxph_bytes ph /\ Z.of_nat (length LBN) <= ctxph_cnt ph /\ lb_big LBN <= ctxph_big ph.
  Proof.
    intros [|x0] LBN x D; cbn [ctxph_delta ctxph_bytes ctxph_cnt ctxph_big] in *.
    - unfold CTXINIT_BIG. lia.
    - destruct D as [-> ->]. cbn. unfold lb_bytes, lb_big. cbn. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma relro_lib_xpres : forall LB SP X m m',
    ECH_LibState.relro_lib m -> xpres LB SP X m m' -> (forall a, RELRO_LO <= a < RELRO_HI -> ~ rin_ivs X a) -> ECH_LibState.relro_lib m'.
  Proof.
    intros LB SP X m m' RL XP NX a Ha Hn. destruct (XP a) as [E _].
    - unfold RELRO_LO, RELRO_HI in Ha. lia.
    - split; [| apply NX; exact Ha]. right; left. unfold ralloc_static, RELRO_LO, RELRO_HI, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK in *. lia.
    - rewrite E. apply RL; assumption.
  Qed.
  (* [comment removed for export] *)
  Lemma magree_lib_of_xpres : forall LB SP X m m',
    xpres LB SP X m m' -> magree (fun a => lib_addr LB a /\ ~ rin_ivs X a) m m'.
  Proof.
    intros LB SP X m m' XP a Ha [HL HXa]. apply XP; [exact Ha|]. split; [| exact HXa].
    destruct HL as [HL|HBk]; [| right; right; exact HBk].
    right; left. unfold LIBX, LIBX0 in HL. cbn [rin_ivs fst snd] in HL. unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma magree_lib_of_block_munch : forall s LB m0 m m' p A n,
    hs_RHEAP H s ((p, A, n) :: LB) m0 -> rblock_range A n -> munch [(A, A + n)] m m' -> wmono rsegs m m' -> magree (lib_addr LB) m m'.
  Proof.
    intros s LB m0 m m' p A n HP BR MU WM. hcb. eapply magree_of_munch; [exact MU| exact WM|].
    intros a Ha HL. cbn. split; [| exact I].
    destruct HL as [HL|HBk].
    - unfold LIBX, LIBX0 in HL. cbn [rin_ivs fst snd] in HL. destruct BR as (_ & _ & NN & _ & BI). lia.
    - pose proof (HH_fresh_outside H HH _ _ _ _ _ _ hceil a HP (Z.le_refl hceil) ltac:(right; right; exact HBk)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma CTXPH_mono : forall L L' (SUB : forall b, In b L -> In b L') m ph, CTXPH L m ph -> CTXPH L' m ph.
  Proof.
    intros L L' SUB m [|x0] C; cbn [CTXPH] in *; [exact C|]. destruct C as [CS [EX (po & pi & O1 & O2)]].
    split; [exact CS|]. split; [| exists po, pi; split; apply SUB; assumption].
    destruct EX as (E1 & E2 & E3 & E4). split; [apply SUB; exact E1|]. split; [exact E2|]. split; [exact E3| exact E4].
  Qed.

  Lemma newmembuf_spec : newmembuf_stmt H.
  Proof.
    unfold newmembuf_stmt. intros until errv.
    intros A0 A1 BP BH LR HP KREL BUD BUDC BUDB AUX SPB SPA ST CEIL LO ERR MI TP MF IM GM METH RL CPH RAE.
    pose proof (ctxph_nonneg ph) as (PHB & PHC & PHG & PHS). set (XS := CNEWEX_STACK ph) in *.
    unfold NEWMEMBUF_STACK, BIONEW_STACK, MEMINIT_STACK, BUFNEW_STACK, CZALLOC_STACK, CMALLOC_STACK, FR_BIO_new_mem_buf, FR_BIO_new, FR_BIO_new_ex, FR_mem_new, FR_mem_init,
      FR_BUF_MEM_new, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, RMALLOC_STACK in LO.
    unfold MEMBIO_BYTES, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in BUD.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (HB := HH_blocks_below H HH _ _ _ HP). subst tp. rewrite errno_RATP in ERR.
    unfold METH_mem, O_METH_BREAD in METH.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply nm_seg1 with (lo := lo); [exact A0| exact A1| exact BP| exact BH| exact LR| exact ST| exact CEIL| lia| exact MI]|].
    intros ms1 (m1 & j1 & -> & MU1 & WM1 & MI1 & ST1 & F01 & F21).
    pose proof (magree_lib_of_stack_munch H HX _ _ _ _ _ _ HP MU1 WM1 ltac:(apply Forall_cons; [cbn; lia| apply Forall_nil])) as AG1.
    assert (XP1 : xpres LB (bv_unsigned sp) (memflag_foot ++ ctxph_foot ph) m m1).
    { eapply xpres_of_munch; [exact MU1| exact WM1| | exact HB]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    apply (rw_cells_transport rsegs _ m m1 _ _ METH) in MU1 as METH1; [| exact WM1| unfold A_mem_buf_method; cbn; lia].
    pose proof (CTXPH_frame _ _ _ _ CPH AG1) as CPH1.
    (* [comment removed for export] *)
    pose proof (czalloc_spec H HH) as CZ. unfold czalloc_stmt, czalloc_stmt_gen in CZ.
    eapply (sr_seq H HH).
    { eapply CZ with (lo := lo) (B := B) (LB := LB) (s := s) (v := v) (num := 128) (size := 1); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try (unfold CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, RMALLOC_STACK; lia).
      all: try first [exact KREL| exact ST1| exact CEIL| exact MI1].
      all: lazymatch goal with
           | |- hs_RHEAP _ _ _ _ => eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]; apply Forall_cons; [left; cbn; lia| apply Forall_nil]
           | |- lb_big _ + _ <= _ => rewrite big1_small by (unfold BIGB; lia); lia
           | |- hs_rauxv_ok _ _ _ => eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]; unfold RAUXV_CELL; apply Forall_cons; [cbn; lia| apply Forall_nil]
           | |- rw_cells _ _ _ _ => rewrite errno_RATP; errno_across ERR MU1 WM1
           | |- MEMFLAG _ _ => eapply MEMFLAG_across; [exact MU1| exact WM1| unfold A_mem_inited; cbn; lia| exact MF]
           | |- IMPL_mem _ => eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]
           | |- GOT_mem _ => eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]
           | |- _ => try lia
           end. }
    clear CZ. intros [ms2 mo2] PO. unfold czalloc_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A & p1 & s2' &
                    -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & XP2 & BR1 & HEAP2 & BLK2 & MF2 & IM2 & GM2).
    rewrite (unsigned_lit (bv_unsigned sp + -80)) in ST2, XP2 by lia. rewrite errno_RATP in ERR2. change (128 * 1) with 128 in BR1, HEAP2, BLK2.
    pose proof BR1 as (AP & _ & _ & AH & AI).
    set (LB1 := (p1, A, 128) :: LB) in *.
    assert (SUB01 : forall b, In b LB -> In b LB1) by (intros b Hb; right; exact Hb).
    assert (HB1 := HH_blocks_below H HH _ _ _ HEAP2).
    assert (F02 : rw_cells rsegs m2 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2); [exact F01| left; cbn; lia| mf_windows]. }
    assert (F22 : rw_cells rsegs m2 (bv_unsigned sp + -80) [CB 8 j1; C8 s3; C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 buf); C8 sp; C8 (Z_to_bv 64 NMB_RET)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2); [exact F21| left; cbn; lia| mf_windows]. }
    assert (METH2 : rw_cells rsegs m2 (A_mem_buf_method + 32)
      [C8 (wz P_bread_conv); C8 (wz P_mem_read); C8 (wz P_mem_puts); C8 (wz P_mem_gets); C8 (wz P_mem_ctrl); C8 (wz P_mem_new); C8 (wz P_mem_free); C8 (wz 0)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2); [exact METH1| static_tac| mf_windows]. }
    assert (RL2 : ECH_LibState.relro_lib m2).
    { eapply relro_lib_xpres; [| exact XP2|]. { eapply relro_lib_munch; [exact RL| exact MU1|]. apply Forall_cons; [unfold RELRO_LO, RELRO_HI; cbn; lia| apply Forall_nil]. }
      intros a Ha. unfold memflag_foot, A_mem_inited, RELRO_LO, RELRO_HI in *. cbn. lia. }
    assert (CPH2 : CTXPH LB m2 ph).
    { eapply CTXPH_frame_mf'; [exact CPH1|]. eapply magree_mono; [eapply magree_lib_of_xpres; exact XP2|].
      intros a [HL HF]. split; [exact HL|]. unfold memflag_foot. cbn. unfold A_mem_inited in *. lia. }
    apply bio_zero_recut in BLK2.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL2| eapply nm_seg2; [exact AP| exact AH| exact BLK2| exact MI2]|].
    intros ms3 (m3 & -> & MU3 & WM3 & MI3 & BA3).
    unfold BIO_SIZE in MU3.
    apply (stk_transport_disjoint rsegs _ m2 m3 _ _ ST2) in MU3 as ST3; [| exact WM3| cbn; lia].
    apply (rw_cells_transport rsegs _ m2 m3 _ _ F02) in MU3 as F03; [| exact WM3| cbn; lia].
    apply (rw_cells_transport rsegs _ m2 m3 _ _ F22) in MU3 as F23; [| exact WM3| cbn; lia].
    apply (rw_cells_transport rsegs _ m2 m3 _ _ METH2) in MU3 as METH3; [| exact WM3| unfold A_mem_buf_method; cbn; lia].
    apply (rw_cells_transport rsegs _ m2 m3 _ _ ERR2) in MU3 as ERR3; [| exact WM3| unfold RERRNO; cbn; lia].
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
    assert (CPH3 : CTXPH LB1 m3 ph).
    { apply (CTXPH_mono LB LB1 SUB01). eapply CTXPH_frame; [exact CPH2|]. eapply magree_lib_of_block_munch; [exact HEAP2| exact BR1| exact MU3| exact WM3]. }
    assert (XP3 : xpres LB (bv_unsigned sp) (memflag_foot ++ ctxph_foot ph) m2 m3).
    { eapply (xpres_of_munch_fresh H HH); [exact HEAP2| lia| exact MU3| exact WM3|]. apply Forall_cons; [right; left; cbn; lia| apply Forall_nil]. }
    destruct (bio_cells_split_ex _ _ _ BA3) as [BA3a EXD3].
    (* [comment removed for export] *)
    pose proof (cnewex_spec H HX CERTA) as CNX. unfold cnewex_stmt in CNX.
    eapply (sr_seq H HH).
    { eapply CNX with (lo := lo) (B := B) (LB := LB1) (s := s2') (ph := ph) (obj := A) (ad := A + O_BIO_EXDATA) (c0 := 0) (k0 := 0);
        unfold O_BIO_EXDATA; rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact EXD3| exact HEAP3| exact KREL2| exact AUX3| exact ST3| exact CEIL| exact MI3| exact MF3| exact IM3| exact GM3| exact RL3| exact CPH3].
      all: lazymatch goal with
           | |- xclient_range _ _ _ _ _ =>
               split; [right; right; exists (p1, A, 128); split; [left; reflexivity| cbn; lia]|]; ctx_x_windows
           | |- off_image _ _ => unfold off_image, IMG_LO, IMG_HI; lia
           | |- forall x0, _ = CtxReady x0 -> _ =>
               intros x Hph; pose proof CPH3 as C; rewrite Hph in C; cbn [CTXPH] in C; destruct C as [_ [[BIN [BSZ _]] _]];
               destruct BIN as [EQ|BIN]; [rewrite <- EQ in BSZ; cbn in BSZ; unfold MUTEX_SIZE in BSZ; lia|];
               pose proof (HH_fresh_disjoint_client H HH _ _ _ _ _ _ (bv_unsigned sp) (blk_addr (cx_exlock x)) MUTEX_SIZE HEAP2
                  ltac:(right; right; exists (cx_exlock x); split; [exact BIN| rewrite BSZ; lia]) ltac:(lia) ltac:(unfold MUTEX_SIZE; lia)) as D;
               unfold MUTEX_SIZE in *; lia
           | |- lb_bytes _ + _ <= _ => unfold LB1; rewrite lb_bytes_cons; cbn [blk_size snd]; lia
           | |- Z.of_nat (length _) + _ <= _ => unfold LB1; cbn [length]; lia
           | |- lb_big _ + _ <= _ => unfold LB1; rewrite lb_big_cons; cbn [blk_size snd]; rewrite big1_small by (unfold BIGB; lia); lia
           | |- rw_cells _ _ (errno_addr _) _ => rewrite errno_RATP; exact ERR3
           | |- _ mod 16 = 0 => clear - SPA SPR LO PHS; lia
           | |- _ mod 2 = 0 => unfold NEX_RA2; rewrite unsigned_lit by lia; reflexivity
           | |- _ => try lia
           end.
      all: match goal with |- ?G => idtac "CNX-LEFT:" G end. }
    clear CNX. intros [ms4 mo4] PO. unfold cnewex_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m4 & errv4 & s4' & LBN & x &
                    -> & KREL4 & MP4 & MI4 & ST4 & ERR4 & AUX4 & HEAP4 & DELTA & CPH4 & KEYS4 & EXD4 & MF4 & IM4 & GM4 & RL4 & XP4).
    unfold O_BIO_EXDATA in XP4, EXD4. rewrite (unsigned_lit (bv_unsigned sp + -80)) in ST4, XP4 by lia. rewrite errno_RATP in ERR4.
    pose proof (ctxph_delta_bounds _ _ _ DELTA) as (NB1 & NB2 & NB3).
    set (LB2 := LBN ++ LB1) in *.
    assert (SUB12 : forall b, In b LB1 -> In b LB2) by (intros b Hb; unfold LB2; apply in_or_app; right; exact Hb).
    assert (AIN2 : In (p1, A, 128) LB2) by (apply SUB12; left; reflexivity).
    assert (HB2 := HH_blocks_below H HH _ _ _ HEAP4).
    assert (F04 : rw_cells rsegs m4 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP4); [exact F03| left; cbn; lia|]. ctxw. }
    assert (F24 : rw_cells rsegs m4 (bv_unsigned sp + -80) [CB 8 j1; C8 s3; C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 buf); C8 sp; C8 (Z_to_bv 64 NMB_RET)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP4); [exact F23| left; cbn; lia|]. ctxw. }
    assert (METH4 : rw_cells rsegs m4 (A_mem_buf_method + 32)
      [C8 (wz P_bread_conv); C8 (wz P_mem_read); C8 (wz P_mem_puts); C8 (wz P_mem_gets); C8 (wz P_mem_ctrl); C8 (wz P_mem_new); C8 (wz P_mem_free); C8 (wz 0)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP4); [exact METH3| static_tac|]. ctxw. }
    assert (BA4a : rw_cells rsegs m4 A (firstn 18 (bio_cells bio_hdr1))).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP4); [exact BA3a| |].
      - right; right. exists (p1, A, 128). split; [left; reflexivity| cbn; lia].
      - ctxw. }
    pose proof (bio_cells_join_ex _ _ _ BA4a EXD4) as BA4. clear BA4a EXD4.
    (* [comment removed for export] *)
    assert (CPHx : CTXPH (LBN ++ LB) m4 (CtxReady x)).
    { cbn [CTXPH] in CPH4 |- *. destruct CPH4 as [CS [[BIN [BSZ [BRR BMX]]] (po & pi & O1 & O2)]].
      assert (DROP : forall q a n, In (q, a, n) LB2 -> n <> 128 -> In (q, a, n) (LBN ++ LB)).
      { intros q a n Hin Hn. unfold LB2, LB1 in Hin. apply in_app_or in Hin. apply in_or_app. destruct Hin as [Hin|[Hin|Hin]]; [left; exact Hin| | right; exact Hin].
        exfalso. injection Hin. lia. }
      split; [exact CS|]. split.
      - split; [| split; [exact BSZ| split; [exact BRR| exact BMX]]]. destruct (cx_exlock x) as [[q a] n]. cbn [blk_size snd] in BSZ. apply DROP; [exact BIN| unfold MUTEX_SIZE in BSZ; lia].
      - exists po, pi. split; apply DROP; try assumption; lia. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL4| eapply nm_seg3 with (lo := lo); [exact AP| exact AH| exact METH4| rewrite unsigned_lit by lia; exact ST4| exact CEIL| rewrite unsigned_lit by lia; lia| exact MI4]|].
    intros ms5 (m5 & j3 & -> & MU5 & WM5 & MI5 & ST5 & F35 & METH5).
    rewrite (unsigned_lit (bv_unsigned sp + -80)) in MU5, ST5, F35 |- * by lia.
    replace (bv_unsigned sp + -80 + -48) with (bv_unsigned sp + -128) in MU5, ST5, F35 |- * by lia.
    apply (rw_cells_transport rsegs _ m4 m5 _ _ F04) in MU5 as F05; [| exact WM5| cbn; lia].
    apply (rw_cells_transport rsegs _ m4 m5 _ _ F24) in MU5 as F25; [| exact WM5| cbn; lia].
    apply (rw_cells_transport rsegs _ m4 m5 _ _ BA4) in MU5 as BA5; [| exact WM5| cbn; lia].
    apply (rw_cells_transport rsegs _ m4 m5 _ _ ERR4) in MU5 as ERR5; [| exact WM5| unfold RERRNO; cbn; lia].
    assert (AUX5 : hs_rauxv_ok H m5 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX4| exact MU5| exact WM5|]. unfold RAUXV_CELL. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    assert (HEAP5 : hs_RHEAP H s4' LB2 m5).
    { eapply (HH_RHEAP_frame H HH); [exact HEAP4| exact MU5| exact WM5|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (MF5 : MEMFLAG m5 1) by (eapply MEMFLAG_across; [exact MU5| exact WM5| unfold A_mem_inited; cbn; lia| exact MF4]).
    assert (IM5 : IMPL_mem m5) by (eapply IMPL_across; [exact MU5| exact WM5| unfold A_malloc_impl; cbn; lia| exact IM4]).
    assert (GM5 : GOT_mem m5) by (eapply GOT_across; [exact MU5| exact WM5| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM4]).
    assert (RL5 : ECH_LibState.relro_lib m5).
    { eapply relro_lib_munch; [exact RL4| exact MU5|]. apply Forall_cons; [unfold RELRO_LO, RELRO_HI; cbn; lia| apply Forall_nil]. }
    assert (CPH5 : CTXPH (LBN ++ LB) m5 (CtxReady x)).
    { eapply CTXPH_frame; [exact CPHx|]. eapply magree_mono; [eapply (magree_lib_of_stack_munch H HX _ _ _ _ _ _ HEAP4 MU5 WM5); apply Forall_cons; [cbn; lia| apply Forall_nil]|].
      intros a [HL|HBk]; [left; exact HL| right]. destruct HBk as (b & Hb & R). exists b. split; [| exact R].
      unfold LB2, LB1. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; exact Hb| right; right; exact Hb]. }
    assert (KEYS5 : ph = CtxFresh -> CTX_keys m5).
    { intros E. specialize (KEYS4 E). destruct KEYS4 as (K1 & K2 & K3). unfold CTX_keys.
      split; [| split]; (eapply rw_cells_transport; [eassumption| exact MU5| exact WM5|]); unfold A_next_key, A_key_lock, A_td_cancelbuf; cbn; lia. }
    assert (XP5 : xpres LB (bv_unsigned sp) (memflag_foot ++ ctxph_foot ph) m4 m5).
    { eapply xpres_of_munch; [exact MU5| exact WM5| | exact HB]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (BY2 : lb_bytes LB2 = lb_bytes LBN + 128 + lb_bytes LB) by (unfold LB2, LB1; rewrite lb_bytes_app, lb_bytes_cons; cbn [blk_size snd]; lia).
    assert (CN2 : Z.of_nat (length LB2) = Z.of_nat (length LBN) + 1 + Z.of_nat (length LB)) by (unfold LB2, LB1; rewrite length_app; cbn [length]; lia).
    assert (BG2 : lb_big LB2 = lb_big LBN + lb_big LB) by (unfold LB2, LB1; rewrite lb_big_app, lb_big_cons; cbn [blk_size snd]; rewrite big1_small by (unfold BIGB; lia); lia).
    (* [comment removed for export] *)
    pose proof (czalloc_spec H HH) as CZ. unfold czalloc_stmt, czalloc_stmt_gen in CZ.
    eapply (sr_seq H HH).
    { eapply CZ with (lo := lo) (B := B) (LB := LB2) (s := s4') (v := 1) (num := 16) (size := 1); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try (unfold CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, RMALLOC_STACK; lia).
      all: try first [exact HEAP5| exact KREL4| exact AUX5| exact ST5| exact CEIL| exact MI5| exact MF5| exact IM5| exact GM5].
      all: lazymatch goal with
           | |- lb_big _ + _ <= _ => rewrite big1_small by (unfold BIGB; lia); lia
           | |- rw_cells _ _ _ _ => rewrite errno_RATP; exact ERR5
           | |- _ => try lia
           end.
      all: match goal with |- ?G => idtac "CZ2-LEFT:" G end. }
    clear CZ. intros [ms6 mo6] PO. unfold czalloc_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m6 & errv6 & Abb & p2 & s6' &
                    -> & KREL6 & MP6 & MI6 & ST6 & ERR6 & AUX6 & XP6 & BR2 & HEAP6 & BB6 & MF6 & IM6 & GM6).
    rewrite (unsigned_lit (bv_unsigned sp + -128)) in ST6, XP6 by lia. rewrite errno_RATP in ERR6. change (16 * 1) with 16 in BR2, HEAP6, BB6.
    pose proof BR2 as (BBP & _ & _ & BBH & BBI).
    set (LB3 := (p2, Abb, 16) :: LB2) in *.
    assert (F36 : rw_cells rsegs m6 (bv_unsigned sp + -128) [CB 8 j3; C8 (Z_to_bv 64 A_mem_buf_method); C8 (Z_to_bv 64 (A + O_BIO_EXDATA)); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (bv_unsigned sp + -32)); C8 (Z_to_bv 64 NEX_RA3)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP6); [exact F35| left; cbn; lia| ctxw]. }
    assert (F26 : rw_cells rsegs m6 (bv_unsigned sp + -80) [CB 8 j1; C8 s3; C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 buf); C8 sp; C8 (Z_to_bv 64 NMB_RET)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP6); [exact F25| left; cbn; lia| ctxw]. }
    assert (F06 : rw_cells rsegs m6 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP6); [exact F05| left; cbn; lia| ctxw]. }
    assert (METH6 : rw_cells rsegs m6 (A_mem_buf_method + 32)
      [C8 (wz P_bread_conv); C8 (wz P_mem_read); C8 (wz P_mem_puts); C8 (wz P_mem_gets); C8 (wz P_mem_ctrl); C8 (wz P_mem_new); C8 (wz P_mem_free); C8 (wz 0)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP6); [exact METH5| static_tac| ctxw]. }
    assert (BA6 : rw_cells rsegs m6 A (bio_cells bio_hdr1)).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP6); [exact BA5| right; right; exists (p1, A, 128); split; [exact AIN2| cbn; lia]| ctxw]. }
    assert (RL6 : ECH_LibState.relro_lib m6).
    { eapply relro_lib_xpres; [exact RL5| exact XP6|]. intros a Ha. unfold memflag_foot, A_mem_inited, RELRO_LO, RELRO_HI in *. cbn. lia. }
    assert (SUBx2 : forall b, In b (LBN ++ LB) -> In b LB2).
    { intros b Hb. unfold LB2, LB1. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; exact Hb| right; right; exact Hb]. }
    assert (CPH6 : CTXPH (LBN ++ LB) m6 (CtxReady x)).
    { eapply CTXPH_frame_mf'; [exact CPH5|]. eapply magree_mono; [eapply magree_lib_of_xpres; exact XP6|].
      intros a [HL HF]. split; [| unfold memflag_foot; cbn; unfold A_mem_inited in *; lia].
      destruct HL as [HL|(b & Hb & R)]; [left; exact HL| right; exists b; split; [apply SUBx2; exact Hb| exact R]]. }
    assert (KEYS6 : ph = CtxFresh -> CTX_keys m6).
    { intros E. specialize (KEYS5 E). destruct KEYS5 as (K1 & K2 & K3). unfold CTX_keys.
      split; [| split]; (eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP6); [eassumption| static_tac| ctxw]). }
    pose proof (HH_fresh_disjoint_client H HH _ _ _ _ _ _ (bv_unsigned sp) A 128 HEAP6
                  ltac:(right; right; exists (p1, A, 128); split; [exact AIN2| cbn; lia]) ltac:(lia) ltac:(lia)) as DJ_A_BB.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL6| eapply nm_seg4; [exact BBP| exact BBH| exact MI6]|].
    intros ms7 ->.
    (* [comment removed for export] *)
    pose proof (bufnew_spec H HH) as BN. unfold bufnew_stmt in BN.
    eapply (sr_seq H HH).
    { eapply BN with (lo := lo) (B := B) (LB := LB3) (s := s6') (v := 1); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try (unfold BUFNEW_STACK, FR_BUF_MEM_new, CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, RMALLOC_STACK; lia).
      all: try first [exact HEAP6| exact KREL6| exact AUX6| exact ST6| exact CEIL| exact MI6| exact MF6| exact IM6| exact GM6].
      all: lazymatch goal with
           | |- lb_bytes _ + _ <= _ => unfold LB3; rewrite lb_bytes_cons; cbn [blk_size snd]; unfold BUFMEM_SIZE; lia
           | |- Z.of_nat (length _) + _ <= _ => unfold LB3; cbn [length]; lia
           | |- lb_big _ <= _ => unfold LB3; rewrite lb_big_cons; cbn [blk_size snd]; rewrite big1_small by (unfold BIGB; lia); lia
           | |- rw_cells _ _ _ _ => rewrite errno_RATP; exact ERR6
           | |- _ mod 2 = 0 => unfold MI_RA2; rewrite unsigned_lit by lia; reflexivity
           | |- _ => try lia
           end.
      all: match goal with |- ?G => idtac "BN-LEFT:" G end. }
    clear BN. intros [ms8 mo8] PO. unfold bufnew_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (x0 & x1 & x2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & x3 & x4 & x5 & x6 & m8 & errv8 & Abm & p3 & s8' &
                    -> & KREL8 & MP8 & MI8 & ST8 & ERR8 & AUX8 & XP8 & BR3 & HEAP8 & BM8 & MF8 & IM8 & GM8).
    rewrite (unsigned_lit (bv_unsigned sp + -128)) in ST8, XP8 by lia. rewrite errno_RATP in ERR8. unfold BUFMEM_SIZE in BR3, HEAP8.
    pose proof BR3 as (BMP & _ & _ & BMH & BMI).
    set (LB4 := (p3, Abm, 32) :: LB3) in *.
    assert (F38 : rw_cells rsegs m8 (bv_unsigned sp + -128) [CB 8 j3; C8 (Z_to_bv 64 A_mem_buf_method); C8 (Z_to_bv 64 (A + O_BIO_EXDATA)); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (bv_unsigned sp + -32)); C8 (Z_to_bv 64 NEX_RA3)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP8); [exact F36| left; cbn; lia| ctxw]. }
    assert (F28 : rw_cells rsegs m8 (bv_unsigned sp + -80) [CB 8 j1; C8 s3; C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 buf); C8 sp; C8 (Z_to_bv 64 NMB_RET)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP8); [exact F26| left; cbn; lia| ctxw]. }
    assert (F08 : rw_cells rsegs m8 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP8); [exact F06| left; cbn; lia| ctxw]. }
    assert (METH8 : rw_cells rsegs m8 (A_mem_buf_method + 32)
      [C8 (wz P_bread_conv); C8 (wz P_mem_read); C8 (wz P_mem_puts); C8 (wz P_mem_gets); C8 (wz P_mem_ctrl); C8 (wz P_mem_new); C8 (wz P_mem_free); C8 (wz 0)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP8); [exact METH6| static_tac| ctxw]. }
    assert (BA8 : rw_cells rsegs m8 A (bio_cells bio_hdr1)).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP8); [exact BA6| right; right; exists (p1, A, 128); split; [right; exact AIN2| cbn; lia]| ctxw]. }
    assert (BB8 : rw_cells rsegs m8 Abb [C8 (wz 0); C8 (wz 0)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP8); [| | ctxw].
      - eapply rw_cells_recut; [exact BB6| vm_compute; repeat split; reflexivity| apply bytes_eq_of_unsigned; vm_compute; reflexivity].
      - right; right. exists (p2, Abb, 16). split; [left; reflexivity| cbn; lia]. }
    assert (RL8 : ECH_LibState.relro_lib m8).
    { eapply relro_lib_xpres; [exact RL6| exact XP8|]. intros a Ha. unfold memflag_foot, A_mem_inited, RELRO_LO, RELRO_HI in *. cbn. lia. }
    assert (CPH8 : CTXPH (LBN ++ LB) m8 (CtxReady x)).
    { eapply CTXPH_frame_mf'; [exact CPH6|]. eapply magree_mono; [eapply magree_lib_of_xpres; exact XP8|].
      intros a [HL HF]. split; [| unfold memflag_foot; cbn; unfold A_mem_inited in *; lia].
      destruct HL as [HL|(b & Hb & R)]; [left; exact HL| right; exists b; split; [right; apply SUBx2; exact Hb| exact R]]. }
    assert (KEYS8 : ph = CtxFresh -> CTX_keys m8).
    { intros E. specialize (KEYS6 E). destruct KEYS6 as (K1 & K2 & K3). unfold CTX_keys.
      split; [| split]; (eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP8); [eassumption| static_tac| ctxw]). }
    pose proof (HH_fresh_disjoint_client H HH _ _ _ _ _ _ (bv_unsigned sp) A 128 HEAP8
                  ltac:(right; right; exists (p1, A, 128); split; [right; exact AIN2| cbn; lia]) ltac:(lia) ltac:(lia)) as DJ_A_BM.
    pose proof (HH_fresh_disjoint_client H HH _ _ _ _ _ _ (bv_unsigned sp) Abb 16 HEAP8
                  ltac:(right; right; exists (p2, Abb, 16); split; [left; reflexivity| cbn; lia]) ltac:(lia) ltac:(lia)) as DJ_BB_BM.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL8| eapply nm_seg5; [exact BBP| exact BBH| exact BMP| exact BMH| exact BB8| exact MI8]|].
    intros ms9 (m9 & -> & MU9 & WM9 & MI9 & BB9). unfold BIOBUFMEM_SIZE in MU9.
    apply (stk_transport_disjoint rsegs _ m8 m9 _ _ ST8) in MU9 as ST9; [| exact WM9| cbn; lia].
    apply (rw_cells_transport rsegs _ m8 m9 _ _ F38) in MU9 as F39; [| exact WM9| cbn; lia].
    apply (rw_cells_transport rsegs _ m8 m9 _ _ F28) in MU9 as F29; [| exact WM9| cbn; lia].
    apply (rw_cells_transport rsegs _ m8 m9 _ _ F08) in MU9 as F09; [| exact WM9| cbn; lia].
    apply (rw_cells_transport rsegs _ m8 m9 _ _ METH8) in MU9 as METH9; [| exact WM9| unfold A_mem_buf_method; cbn; lia].
    apply (rw_cells_transport rsegs _ m8 m9 _ _ BA8) in MU9 as BA9; [| exact WM9| cbn; lia].
    apply (rw_cells_transport rsegs _ m8 m9 _ _ BM8) in MU9 as BM9; [| exact WM9| cbn; lia].
    apply (rw_cells_transport rsegs _ m8 m9 _ _ ERR8) in MU9 as ERR9; [| exact WM9| unfold RERRNO; cbn; lia].
    assert (AUX9 : hs_rauxv_ok H m9 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX8| exact MU9| exact WM9|]. unfold RAUXV_CELL. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    assert (HEAP9 : hs_RHEAP H s8' LB4 m9).
    { eapply (HH_RHEAP_frame H HH); [exact HEAP8| exact MU9| exact WM9|]. apply Forall_cons; [| apply Forall_nil].
      right; right. exists (p2, Abb, 16). split; [right; left; reflexivity| cbn; lia]. }
    assert (MF9 : MEMFLAG m9 1) by (eapply MEMFLAG_across; [exact MU9| exact WM9| unfold A_mem_inited; cbn; lia| exact MF8]).
    assert (IM9 : IMPL_mem m9) by (eapply IMPL_across; [exact MU9| exact WM9| unfold A_malloc_impl; cbn; lia| exact IM8]).
    assert (GM9 : GOT_mem m9) by (eapply GOT_across; [exact MU9| exact WM9| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM8]).
    assert (RL9 : ECH_LibState.relro_lib m9).
    { eapply relro_lib_munch; [exact RL8| exact MU9|]. apply Forall_cons; [unfold RELRO_LO, RELRO_HI; cbn; lia| apply Forall_nil]. }
    assert (CPH9 : CTXPH (LBN ++ LB) m9 (CtxReady x)).
    { eapply CTXPH_frame; [exact CPH8|]. eapply magree_mono; [eapply magree_lib_of_block_munch; [exact HEAP6| exact BR2| exact MU9| exact WM9]|].
      intros a [HL|(b & Hb & R)]; [left; exact HL| right; exists b; split; [apply SUBx2; exact Hb| exact R]]. }
    assert (KEYS9 : ph = CtxFresh -> CTX_keys m9).
    { intros E. specialize (KEYS8 E). destruct KEYS8 as (K1 & K2 & K3). unfold CTX_keys.
      split; [| split]; (eapply rw_cells_transport; [eassumption| exact MU9| exact WM9|]); unfold A_next_key, A_key_lock, A_td_cancelbuf; cbn; lia. }
    (* [comment removed for export] *)
    pose proof (czalloc_spec H HH) as CZ. unfold czalloc_stmt, czalloc_stmt_gen in CZ.
    eapply (sr_seq H HH).
    { eapply CZ with (lo := lo) (B := B) (LB := LB4) (s := s8') (v := 1) (num := 32) (size := 1); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try (unfold CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, RMALLOC_STACK; lia).
      all: try first [exact HEAP9| exact KREL8| exact AUX9| exact ST9| exact CEIL| exact MI9| exact MF9| exact IM9| exact GM9].
      all: lazymatch goal with
           | |- lb_bytes _ + _ <= _ => unfold LB4, LB3; rewrite !lb_bytes_cons; cbn [blk_size snd]; lia
           | |- Z.of_nat (length _) + _ <= _ => unfold LB4, LB3; cbn [length]; lia
           | |- lb_big _ + _ <= _ => unfold LB4, LB3; rewrite !lb_big_cons; cbn [blk_size snd]; rewrite !big1_small by (unfold BIGB; lia); lia
           | |- rw_cells _ _ _ _ => rewrite errno_RATP; exact ERR9
           | |- _ mod 2 = 0 => unfold MI_RA3; rewrite unsigned_lit by lia; reflexivity
           | |- _ => try lia
           end.
      all: match goal with |- ?G => idtac "CZ3-LEFT:" G end. }
    clear CZ. intros [ms10 mo10] PO. unfold czalloc_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (y0 & y1 & y2 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & y3 & y4 & y5 & y6 & m10 & errv10 & Arp & p4 & s10' &
                    -> & KREL10 & MP10 & MI10 & ST10 & ERR10 & AUX10 & XP10 & BR4 & HEAP10 & RP10 & MF10 & IM10 & GM10).
    rewrite (unsigned_lit (bv_unsigned sp + -128)) in ST10, XP10 by lia. rewrite errno_RATP in ERR10. change (32 * 1) with 32 in BR4, HEAP10, RP10.
    pose proof BR4 as (RPP & _ & _ & RPH & RPI).
    assert (F310 : rw_cells rsegs m10 (bv_unsigned sp + -128) [CB 8 j3; C8 (Z_to_bv 64 A_mem_buf_method); C8 (Z_to_bv 64 (A + O_BIO_EXDATA)); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (bv_unsigned sp + -32)); C8 (Z_to_bv 64 NEX_RA3)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP10); [exact F39| left; cbn; lia| ctxw]. }
    assert (F210 : rw_cells rsegs m10 (bv_unsigned sp + -80) [CB 8 j1; C8 s3; C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 buf); C8 sp; C8 (Z_to_bv 64 NMB_RET)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP10); [exact F29| left; cbn; lia| ctxw]. }
    assert (F010 : rw_cells rsegs m10 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP10); [exact F09| left; cbn; lia| ctxw]. }
    assert (METH10 : rw_cells rsegs m10 (A_mem_buf_method + 32)
      [C8 (wz P_bread_conv); C8 (wz P_mem_read); C8 (wz P_mem_puts); C8 (wz P_mem_gets); C8 (wz P_mem_ctrl); C8 (wz P_mem_new); C8 (wz P_mem_free); C8 (wz 0)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP10); [exact METH9| static_tac| ctxw]. }
    assert (BA10 : rw_cells rsegs m10 A (bio_cells bio_hdr1)).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP10); [exact BA9| right; right; exists (p1, A, 128); split; [right; right; exact AIN2| cbn; lia]| ctxw]. }
    assert (BB10 : rw_cells rsegs m10 Abb [C8 (Z_to_bv 64 Abm); C8 (wz 0)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP10); [exact BB9| right; right; exists (p2, Abb, 16); split; [right; left; reflexivity| cbn; lia]| ctxw]. }
    assert (BM10 : rw_cells rsegs m10 Abm (buf_cells (mkBUF 0 0 0 0))).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP10); [exact BM9| right; right; exists (p3, Abm, 32); split; [left; reflexivity| cbn; lia]| ctxw]. }
    assert (RL10 : ECH_LibState.relro_lib m10).
    { eapply relro_lib_xpres; [exact RL9| exact XP10|]. intros a Ha. unfold memflag_foot, A_mem_inited, RELRO_LO, RELRO_HI in *. cbn. lia. }
    assert (CPH10 : CTXPH (LBN ++ LB) m10 (CtxReady x)).
    { eapply CTXPH_frame_mf'; [exact CPH9|]. eapply magree_mono; [eapply magree_lib_of_xpres; exact XP10|].
      intros a [HL HF]. split; [| unfold memflag_foot; cbn; unfold A_mem_inited in *; lia].
      destruct HL as [HL|(b & Hb & R)]; [left; exact HL| right; exists b; split; [right; right; apply SUBx2; exact Hb| exact R]]. }
    assert (KEYS10 : ph = CtxFresh -> CTX_keys m10).
    { intros E. specialize (KEYS9 E). destruct KEYS9 as (K1 & K2 & K3). unfold CTX_keys.
      split; [| split]; (eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP10); [eassumption| static_tac| ctxw]). }
    pose proof (HH_fresh_disjoint_client H HH _ _ _ _ _ _ (bv_unsigned sp) A 128 HEAP10
                  ltac:(right; right; exists (p1, A, 128); split; [right; right; exact AIN2| cbn; lia]) ltac:(lia) ltac:(lia)) as DJ_A_RP.
    pose proof (HH_fresh_disjoint_client H HH _ _ _ _ _ _ (bv_unsigned sp) Abb 16 HEAP10
                  ltac:(right; right; exists (p2, Abb, 16); split; [right; left; reflexivity| cbn; lia]) ltac:(lia) ltac:(lia)) as DJ_BB_RP.
    pose proof (HH_fresh_disjoint_client H HH _ _ _ _ _ _ (bv_unsigned sp) Abm 32 HEAP10
                  ltac:(right; right; exists (p3, Abm, 32); split; [left; reflexivity| cbn; lia]) ltac:(lia) ltac:(lia)) as DJ_BM_RP.
    assert (APART : MEMBIO_apart A (nm_R buf len Abb Abm Arp p1 p2 p3 p4)).
    { unfold MEMBIO_apart, nm_R, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE. cbn [mb_bb mb_bm mb_rp]. lia. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL10| eapply nm_seg6 with (lo := lo);
      [exact BR1| exact BR2| exact BR3| exact BR4| exact BP| exact BH| exact LR| exact APART| exact BA10| exact BB10| exact BM10| exact RP10
      | exact F310| exact F210| exact F010| exact METH10| exact ST10| exact CEIL| lia| exact MI10| exact RAE]|].
    intros ms11 (a1f & a2f & a3f & m11 & -> & MU11 & WM11 & MI11 & ST11 & BA11 & BB11 & BM11 & RP11 & METH11).
    unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in MU11.
    (* [comment removed for export] *)
    assert (OUT11 : forall a, 0 <= a < 2^64 -> rclient_addr LB (bv_unsigned sp) a ->
              outside [(bv_unsigned sp + -128, bv_unsigned sp); (A, A + 128); (Abb, Abb + 16); (Abm, Abm + 32); (Arp, Arp + 32)] a).
    { intros a Ha HC. cbn.
      assert (CL : rclient_addr LB2 lo a /\ rclient_addr LB3 lo a /\ rclient_addr LB4 lo a /\ (a < lo \/ bv_unsigned sp <= a)).
      { destruct HC as [K|[[K K']|(b & Hb & R)]].
        - repeat split; try (left; lia). right; exact K.
        - repeat split; try (right; left; split; assumption). left. lia.
        - assert (R2 : in_block LB2 a) by (exists b; split; [apply SUB12; right; exact Hb| exact R]).
          repeat split; try (right; right; first [exact R2| exists b; split; [first [right; apply SUB12; right; exact Hb| right; right; apply SUB12; right; exact Hb]| exact R]]).
          left. pose proof (HB b Hb). lia. }
      destruct CL as (C2 & C3 & C4 & CS).
      pose proof (HH_fresh_outside H HH _ _ _ _ _ _ (bv_unsigned sp) a HEAP2 ltac:(lia) HC) as O1.
      pose proof (HH_fresh_outside H HH _ _ _ _ _ _ lo a HEAP6 CEIL C2) as O2.
      pose proof (HH_fresh_outside H HH _ _ _ _ _ _ lo a HEAP8 CEIL C3) as O3.
      pose proof (HH_fresh_outside H HH _ _ _ _ _ _ lo a HEAP10 CEIL C4) as O4.
      split; [clear - CS LO; lia|]. split; [clear - O1; lia|]. split; [clear - O2; lia|]. split; [clear - O3; lia|]. split; [clear - O4; lia| exact I]. }
    assert (XP11 : xpres LB (bv_unsigned sp) (memflag_foot ++ ctxph_foot ph) m10 m11).
    { eapply xpres_of_munch_eq; [exact MU11| exact WM11|]. intros a Ha [HC _]. left. apply OUT11; assumption. }
    apply (sr_done H HH). unfold newmembuf_post. cbn [cfg_ms cfg_model].
    exists y0, y1, y2, a1f, a2f, a3f, f4, f5, f6, f7, y3, y4, y5, y6, m11, errv10, s10', LBN, x, A, (nm_R buf len Abb Abm Arp p1 p2 p3 p4).
    (* [comment removed for export] *)
    assert (OUTL : forall a, 0 <= a < 2^64 -> in_block (LBN ++ LB) a ->
              outside [(bv_unsigned sp + -128, bv_unsigned sp); (A, A + 128); (Abb, Abb + 16); (Abm, Abm + 32); (Arp, Arp + 32)] a).
    { intros a Ha (b & Hb & R).
      assert (R2 : in_block LB2 a) by (exists b; split; [apply SUBx2; exact Hb| exact R]).
      pose proof (HB2 b (SUBx2 _ Hb)) as BLO.
      pose proof (HH_fresh_outside H HH _ _ _ _ _ _ lo a HEAP6 CEIL ltac:(right; right; exact R2)) as O2.
      pose proof (HH_fresh_outside H HH _ _ _ _ _ _ lo a HEAP8 CEIL ltac:(right; right; destruct R2 as (bb & Hbb & Rb); exists bb; split; [right; exact Hbb| exact Rb])) as O3.
      pose proof (HH_fresh_outside H HH _ _ _ _ _ _ lo a HEAP10 CEIL ltac:(right; right; destruct R2 as (bb & Hbb & Rb); exists bb; split; [right; right; exact Hbb| exact Rb])) as O4.
      assert (O1 : a + 1 <= A \/ A + 128 <= a).
      { apply in_app_or in Hb. destruct Hb as [Hb|Hb].
        - assert (NE : blk_id b <> blk_id (p1, A, 128)).
          { eapply nodup_ids_app_ne with (l1 := LBN) (l2 := LB1); [| exact Hb| left; reflexivity].
            exact (HH_RHEAP_blocks_nodup H HH _ _ _ HEAP4). }
          pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ b (p1, A, 128) HEAP4 ltac:(unfold LB2; apply in_or_app; left; exact Hb) AIN2 NE) as D.
          cbn [blk_addr blk_size fst snd] in D. clear - D R. lia.
        - exact (HH_fresh_outside H HH _ _ _ _ _ _ lo a HEAP2 CEIL ltac:(right; right; exists b; split; [exact Hb| exact R])). }
      cbn. split; [clear - BLO R LO CEIL; lia|]. split; [clear - O1; lia|]. split; [clear - O2; lia|]. split; [clear - O3; lia|]. split; [clear - O4; lia| exact I]. }
    split; [reflexivity|].
    split; [exact KREL10|].
    split. { eapply (mpres_trans H HH); [exact MP2|]. eapply (mpres_trans H HH); [exact MP4|]. eapply (mpres_trans H HH); [exact MP6|].
             eapply (mpres_trans H HH); [exact MP8| exact MP10]. }
    split; [exact MI11|]. split; [exact ST11|].
    split. { rewrite errno_RATP. eapply rw_cells_transport; [exact ERR10| exact MU11| exact WM11|]. unfold RERRNO in *. cbn. clear - AI BBI BMI RPI LO HCEILB CEIL. lia. }
    split. { eapply (HH_rauxv_frame H HH); [exact AUX10| exact MU11| exact WM11|]. unfold RAUXV_CELL in *.
             repeat (apply Forall_cons; [cbn; clear - AI BBI BMI RPI AH BBH BMH RPH LO CEIL SPB HCEILB SPR; lia|]); apply Forall_nil. }
    split.
    { assert (HEAP11 : hs_RHEAP H s10' ((p4, Arp, 32) :: LB4) m11).
      { eapply (HH_RHEAP_frame H HH); [exact HEAP10| exact MU11| exact WM11|].
        apply Forall_cons; [left; cbn; lia|].
        apply Forall_cons; [right; right; exists (p1, A, 128); split; [right; right; right; exact AIN2| cbn; lia]|].
        apply Forall_cons; [right; right; exists (p2, Abb, 16); split; [right; right; left; reflexivity| cbn; lia]|].
        apply Forall_cons; [right; right; exists (p3, Abm, 32); split; [right; left; reflexivity| cbn; lia]|].
        apply Forall_cons; [right; right; exists (p4, Arp, 32); split; [left; reflexivity| cbn; lia]| apply Forall_nil]. }
      eapply PERM; [exact HEAP11|]. unfold LB4, LB3, LB2, LB1, blocks_MEMBIO, nm_R, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE.
      cbn [mb_id mb_bb mb_bm mb_rp mb_bbid mb_bmid mb_rpid app].
      apply (Permutation_trans (l' := (p4, Arp, 32) :: (p3, Abm, 32) :: (p2, Abb, 16) :: (p1, A, 128) :: LBN ++ LB)).
      - do 3 apply perm_skip. apply Permutation_sym. apply Permutation_middle.
      - change (Permutation (rev [(p1, A, 128); (p2, Abb, 16); (p3, Abm, 32); (p4, Arp, 32)] ++ (LBN ++ LB))
                            ([(p1, A, 128); (p2, Abb, 16); (p3, Abm, 32); (p4, Arp, 32)] ++ (LBN ++ LB))).
        apply Permutation_app_tail. apply Permutation_sym. apply Permutation_rev. }
    split; [exact DELTA|].
    split.
    { apply (CTXPH_mono (LBN ++ LB)). { intros b Hb. apply in_or_app. right. exact Hb. }
      eapply CTXPH_frame; [exact CPH10|]. eapply magree_of_munch; [exact MU11| exact WM11|].
      intros a Ha [HL|HBk]; [| apply OUTL; assumption].
      unfold LIBX, LIBX0 in HL. cbn [rin_ivs fst snd] in HL. cbn. clear - HL AI BBI BMI RPI LO HCEILB CEIL. repeat split; lia. }
    split. { intros E. specialize (KEYS10 E). destruct KEYS10 as (K1 & K2 & K3). unfold CTX_keys.
             split; [| split]; (eapply rw_cells_transport; [eassumption| exact MU11| exact WM11|]); unfold A_next_key, A_key_lock, A_td_cancelbuf; cbn;
               clear - AI BBI BMI RPI LO HCEILB CEIL; lia. }
    split.
    { unfold MEMBIO, blocks_MEMBIO, nm_R, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE.
      cbn [mb_buf mb_len mb_pos mb_flags mb_numf mb_nread mb_next mb_prev mb_bb mb_bm mb_rp mb_id mb_bbid mb_bmid mb_rpid app].
      rewrite ?Z.sub_0_r, ?Z.add_0_r.
      split; [exact BA11|]. split; [exact BB11|]. split; [exact BM11|]. split; [exact RP11|].
      split; [apply in_eq|]. split; [apply in_cons, in_eq|]. split; [apply in_cons, in_cons, in_eq|]. split; [apply in_cons, in_cons, in_cons, in_eq|].
      split; [exact BR1|]. split; [exact BR2|]. split; [exact BR3|]. split; [exact BR4|].
      unfold BIO_FLAGS_MEM_RDONLY, BIO_FLAGS_MEM_LEGACY_EOF. repeat split; try reflexivity; clear - LR BP BH; lia. }
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact AP|]. split; [exact APART|].
    split; [eapply MEMFLAG_across; [exact MU11| exact WM11| unfold A_mem_inited; cbn; clear - AI BBI BMI RPI LO HCEILB CEIL; lia| exact MF10]|].
    split; [eapply IMPL_across; [exact MU11| exact WM11| unfold A_malloc_impl; cbn; clear - AI BBI BMI RPI LO HCEILB CEIL; lia| exact IM10]|].
    split; [eapply GOT_across; [exact MU11| exact WM11| unfold A_got_CRYPTO_malloc; cbn; clear - AI BBI BMI RPI LO HCEILB CEIL; lia| exact GM10]|].
    split; [exact METH11|].
    split; [eapply relro_lib_munch; [exact RL10| exact MU11|]; unfold RELRO_LO, RELRO_HI; repeat (apply Forall_cons; [cbn; clear - AI BBI BMI RPI LO HCEILB CEIL; lia|]); apply Forall_nil|].
    (* [comment removed for export] *)
    eapply xpres_trans; [exact XP1|].
    eapply xpres_trans; [eapply xpres_weaken; [exact XP2| lia| auto| intros q Hq; apply rin_ivs_app; left; exact Hq]|].
    eapply xpres_trans; [exact XP3|].
    eapply xpres_trans.
    { eapply xpres_reLB; [exact XP4|]. intros q Hq HCq NXq. split.
      - destruct HCq as [K|[K|(b & Hb & R)]]; [left; lia| right; left; exact K| right; right; exists b; split; [right; exact Hb| exact R]].
      - cbn [rin_ivs fst snd]. intros [K|K]; [| apply NXq; apply rin_ivs_app; right; exact K].
        pose proof (HH_fresh_outside H HH _ _ _ _ _ _ (bv_unsigned sp) q HEAP2 ltac:(lia) HCq). lia. }
    eapply xpres_trans; [exact XP5|].
    eapply xpres_trans; [eapply xpres_weaken; [exact XP6| lia| intros b Hb; apply SUB12; right; exact Hb| intros q Hq; apply rin_ivs_app; left; exact Hq]|].
    eapply xpres_trans; [eapply xpres_weaken; [exact XP8| lia| intros b Hb; right; apply SUB12; right; exact Hb| intros q Hq; apply rin_ivs_app; left; exact Hq]|].
    eapply xpres_trans.
    { eapply xpres_weaken; [eapply (xpres_of_munch_fresh H HH) with (SP := bv_unsigned sp) (X := memflag_foot ++ ctxph_foot ph); [exact HEAP6| lia| exact MU9| exact WM9|]| lia| intros b Hb; apply SUB12; right; exact Hb| auto].
      apply Forall_cons; [right; left; cbn; lia| apply Forall_nil]. }
    eapply xpres_trans; [eapply xpres_weaken; [exact XP10| lia| intros b Hb; right; right; apply SUB12; right; exact Hb| intros q Hq; apply rin_ivs_app; left; exact Hq]|].
    exact XP11.
  Qed.
End W.
