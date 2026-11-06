(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface F_memcpy ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_KitH ECH_KitSeg ECH_Rep ECH_LibState ECH_LibStateMF ECH_LibFrame ECH_LibMid ECH_C0_stmt ECH_C2_stmt ECH_C1_stmt ECH_C1_malloc ECH_C1_free ECH_C3_stmt ECH_C3_newex ECH_C6_stmt ECH_C7_stmt ECH_C8_stmt ECH_C9_stmt ECH_C7_read ECH_C7_new ECH_C7_free ECH_C7_freeint ECH_C7_biofree ECH_C7_biofreeint ECH_C9_new ECH_C9_free ECH_C9_biofreeb64 ECH_C9_freeall.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma frame_split3 : forall {HCEIL : HeapCeil} m A j s1 s0 ra,
  rw_cells usegs m A [CB 4 j; C4 (wz 0); C8 s1; C8 s0; C8 ra] ->
  rw_cells usegs m A [CB 4 j] /\ rw_cells usegs m (A + 4) [C4 (wz 0)] /\ rw_cells usegs m (A + 8) [C8 s1; C8 s0; C8 ra].
Proof.
  intros HC m A j s1 s0 ra K.
  apply (proj1 (rw_cells_app usegs m A [CB 4 j] _)) in K as [K1 K]. cbn [cells_size csize Nat.add] in K. change (Z.of_nat 4) with 4 in K.
  apply (proj1 (rw_cells_app usegs m (A + 4) [C4 (wz 0)] _)) in K as [K2 K3]. cbn [cells_size csize Nat.add] in K3. change (Z.of_nat 4) with 4 in K3.
  replace (A + 4 + 4) with (A + 8) in K3 by lia.
  split; [exact K1| split; [exact K2| exact K3]].
Qed.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.

  Local Ltac static_tac := right; left; unfold A_b64_method, A_mem_buf_method, O_METH_BREAD, A_next_key, A_key_lock, A_td_cancelbuf, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK; cbn; lia.
  Local Ltac stack_lia := unfold BIOFREEINT_B64_STACK, BIOFREEINT_STACK, BIOFREEALL_STACK, BIOFREE_B64_STACK, BIOFREE_STACK, B64FREE_STACK, ENCFREE_STACK, FR_EVP_ENCODE_CTX_free, FR_b64_free,
      MEMFREE_STACK, BUFFREE_STACK, FR_mem_free, FR_mem_buf_free, FR_BUF_MEM_free, FR_BIO_free_all, FR_BIO_free, CFREE_STACK, CFREEEX_STACK, RFREE_STACK, FR_BIO_free_int,
      FR_CRYPTO_free_ex_data, GETGLOBAL_READY_STACK, NEWEX_INNER, GETANDLOCK_STACK, FR_get_and_lock, CRWLOCK_STACK, CUNLOCK_STACK,
      FR_mutex_unlock, FR_pthread_mutex_unlock, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock, FR_ossl_lib_ctx_get_ex_data_global, GETDEFCTX_STACK, FR_get_default_context in *; lia.

  Lemma biofreeall_spec : biofreeall_stmt H.
  Proof.
    unfold biofreeall_stmt. intros until errv.
    intros A0 BU NXT ENC MB MNX CPH ND7 HP KREL AUX SPB SPAL ST CEIL LO ERR MI TP IM GM METHB METHM RAE.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (LO96 : lo <= bv_unsigned sp - 96) by stack_lia.
    subst tp. rewrite errno_RATP in ERR.
    pose proof BU as (BA & (hdr & junk & elen & LH & LJ & ELR & CTX0) & BLK).
    pose proof BLK as (INa & INc & INe & RA & RC & RE & FLR & RTR & NRR & NXR & PVR).
    pose proof RA as (AP & _ & _ & AH & AI). pose proof RC as (CP & _ & _ & CH & CI). pose proof RE as (EP & _ & _ & EH & EI).
    pose proof MB as (MBA & MBB & MBM & MBRP & INm & INbb & INbm & INrp & RM & RBB & RBM & RRP & POS & LEN & BUFP & BUFH & MFL & RDO & L128 & NUMF & NRD0 & NRDB & MNXR & MPVR).
    pose proof RM as (MP & _ & _ & MH & MI_). pose proof RBB as (BBP & _ & _ & BBH & BBI). pose proof RBM as (BMP & _ & _ & BMH & BMI). pose proof RRP as (RPP & _ & _ & RPH & RPI).
    unfold BIO_SIZE, B64CTX_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in AH, AI, CH, CI, EH, EI, MH, MI_, BBH, BBI, BMH, BMI, RPH, RPI, INa, INc, INe, INm, INbb, INbm, INrp.
    pose proof ENC as (raw & line & L1e & L2e & CE & LNE & INE & RRE & DU). unfold ENCCTX_SIZE in INE, RRE.
    pose proof CPH as CPH0. cbn [CTXPH] in CPH. destruct CPH as [CS [EX OI]]. pose proof EX as (XIN & XSZ & XRR & XM).
    destruct (cx_exlock x) as [[xq xa] xn] eqn:EXB. cbn [blk_addr blk_size blk_id fst snd] in XIN, XSZ, XRR, XM. unfold MUTEX_SIZE in XSZ. subst xn.
    pose proof XRR as (XP1 & _ & _ & XH & XI). unfold MUTEX_SIZE in XH, XI.
    destruct OI as (po & pi & OIN & IIN).
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    (* [comment removed for export] *)
    cbn [map blk_id blocks_B64F blocks_MEMBIO app fst snd] in ND7.
    apply NoDup_cons_iff in ND7 as [N1 ND7]. apply NoDup_cons_iff in ND7 as [N2 ND7]. apply NoDup_cons_iff in ND7 as [N3 ND7].
    apply NoDup_cons_iff in ND7 as [N4 ND7]. apply NoDup_cons_iff in ND7 as [N5 ND7]. apply NoDup_cons_iff in ND7 as [N6 _].
    repeat (apply not_in_cons in N1 as [? N1]). repeat (apply not_in_cons in N2 as [? N2]). repeat (apply not_in_cons in N3 as [? N3]).
    repeat (apply not_in_cons in N4 as [? N4]). repeat (apply not_in_cons in N5 as [? N5]). repeat (apply not_in_cons in N6 as [? N6]).
    (* [comment removed for export] *)
    pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ _ _ HP INa INc ltac:(cbn; congruence)) as DJ_a_c. cbn [blk_addr blk_size fst snd] in DJ_a_c.
    pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ _ _ HP INa INe ltac:(cbn; congruence)) as DJ_a_e. cbn [blk_addr blk_size fst snd] in DJ_a_e.
    pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ _ _ HP INc INe ltac:(cbn; congruence)) as DJ_c_e. cbn [blk_addr blk_size fst snd] in DJ_c_e.
    assert (APART64 : B64F_apart a R) by (unfold B64F_apart, BIO_SIZE, B64CTX_SIZE; split; [exact DJ_a_c| split; [exact DJ_a_e| exact DJ_c_e]]).
    pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ _ _ HP INm INbb ltac:(cbn; congruence)) as DJ_m_bb. cbn [blk_addr blk_size fst snd] in DJ_m_bb.
    pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ _ _ HP INm INbm ltac:(cbn; congruence)) as DJ_m_bm. cbn [blk_addr blk_size fst snd] in DJ_m_bm.
    pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ _ _ HP INm INrp ltac:(cbn; congruence)) as DJ_m_rp. cbn [blk_addr blk_size fst snd] in DJ_m_rp.
    pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ _ _ HP INbb INbm ltac:(cbn; congruence)) as DJ_bb_bm. cbn [blk_addr blk_size fst snd] in DJ_bb_bm.
    pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ _ _ HP INbb INrp ltac:(cbn; congruence)) as DJ_bb_rp. cbn [blk_addr blk_size fst snd] in DJ_bb_rp.
    pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ _ _ HP INbm INrp ltac:(cbn; congruence)) as DJ_bm_rp. cbn [blk_addr blk_size fst snd] in DJ_bm_rp.
    assert (APARTM : MEMBIO_apart mb M).
    { unfold MEMBIO_apart, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE.
      split; [exact DJ_m_bb|]. split; [exact DJ_m_bm|]. split; [exact DJ_m_rp|]. split; [exact DJ_bb_bm|]. split; [exact DJ_bb_rp| exact DJ_bm_rp]. }
    clear DJ_a_c DJ_a_e DJ_c_e DJ_m_bb DJ_m_bm DJ_m_rp DJ_bb_bm DJ_bb_rp DJ_bm_rp.
    hide AI; hide CI; hide EI; hide MI_; hide BBI; hide BMI; hide RPI; hide XI.
    unfold METH_b64, O_METH_BREAD in METHB. unfold METH_mem, O_METH_BREAD in METHM.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply bfa_seg1 with (lo := lo) (a := a) (B := b64f_bio R); cbn [b64f_bio bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite];
      try first [exact A0| exact RA| exact BA| exact ST| exact CEIL| exact MI]; try (unfold A_b64_method; lia)|].
    all: try match goal with |- forall _, _ => idtac | |- ?G => idtac "A1-LEFT:" G end.
    intros ms1 (m1 & j & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    cbn [b64f_bio bio_next] in *.
    destruct (frame_split3 _ _ _ _ _ _ FR1) as (FRJ1 & SL1 & FR31).
    replace (bv_unsigned sp + -32 + 4) with (bv_unsigned sp + -28) in SL1 by lia. replace (bv_unsigned sp + -32 + 8) with (bv_unsigned sp + -24) in FR31 by lia.
    unhide AI; unhide CI; unhide EI; unhide MI_; unhide BBI; unhide BMI; unhide RPI; unhide XI.
    assert (HP1 : hs_RHEAP H s LB m1).
    { eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (AUX1 : hs_rauxv_ok H m1 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]. unfold RAUXV_CELL. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
    apply (rw_cells_transport usegs _ m m1 _ _ ERR) in MU1 as ERR1; [| exact WM1| unfold RERRNO; cbn; lia].
    assert (IM1 : IMPL_mem m1) by (eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]).
    assert (GM1 : GOT_mem m1) by (eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]).
    apply (rw_cells_transport usegs _ m m1 _ _ BA) in MU1 as BA1; [| exact WM1| cbn; lia].
    apply (rw_cells_transport usegs _ m m1 _ _ CTX0) in MU1 as CTX1; [| exact WM1| cbn; lia].
    apply (rw_cells_transport usegs _ m m1 _ _ CE) in MU1 as CE1; [| exact WM1| cbn; lia].
    apply (rw_cells_transport usegs _ m m1 _ _ METHB) in MU1 as METHB1; [| exact WM1| unfold A_b64_method; cbn; lia].
    apply (rw_cells_transport usegs _ m m1 _ _ METHM) in MU1 as METHM1; [| exact WM1| unfold A_mem_buf_method; cbn; lia].
    assert (XP01 : xpres LB (bv_unsigned sp) [] m m1).
    { eapply (xpres_of_munch_exX H HH s LB m m m1 (bv_unsigned sp) [] _ LB []); [exact HP| lia| exact MU1| exact WM1| | |].
      - intros b Hb. split; [exact Hb| intros hb []].
      - intros hb [].
      - apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (AGL1 : magree (lib_addr LB) m m1).
    { eapply magree_mono; [eapply magree_lib_of_xpres_fr; exact XP01|]. intros q HL. split; [exact HL| cbn; tauto]. }
    assert (CPH1 : CTXPH LB m1 (CtxReady x)) by (eapply CTXPH_frame; [exact CPH0| exact AGL1]).
    assert (MB1 : MEMBIO LB m1 mb M).
    { eapply (MEMBIO_frame0 LB LB); [exact MB| | exact XP01]. unfold blocks_MEMBIO, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE.
      intros b [<-|[<-|[<-|[<-|[]]]]]; assumption. }
    assert (BU1 : B64F_used LB m1 a R).
    { split; [exact BA1|]. split; [exists hdr, junk, elen; split; [exact LH|]; split; [exact LJ|]; split; [exact ELR| exact CTX1]| exact BLK]. }
    assert (ENC1 : ENCCTX LB m1 (bf_enc R) d (bf_eid R)).
    { exists raw, line. split; [exact L1e|]. split; [exact L2e|]. split; [exact CE1|]. split; [exact LNE|]. split; [exact INE|]. split; [exact RRE| exact DU]. }
    hide AI; hide CI; hide EI; hide MI_; hide BBI; hide BMI; hide RPI; hide XI.
    (* [comment removed for export] *)
    pose proof (biofreeint_b64_spec H HH) as C1. unfold biofreeint_b64_stmt in C1.
    eapply (sr_seq H HH).
    { eapply C1 with (lo := lo) (B := B) (LB := LB) (s := s) (x := x) (a := a) (rbp := bv_unsigned sp + -28) (R := R) (d := d); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact SL1| exact BU1| exact APART64| exact ENC1| exact CPH1| exact HP1| exact KREL| exact AUX1| exact ST1| exact CEIL| exact MI1| exact IM1| exact GM1].
      all: lazymatch goal with
           | |- rw_cells _ _ (errno_addr _) _ => rewrite errno_RATP; exact ERR1
           | |- METH_b64 _ => unfold METH_b64, O_METH_BREAD; exact METHB1
           | |- _ mod 2 = 0 => unfold BFA_RA; rewrite unsigned_lit by lia; reflexivity
           | |- _ => try stack_lia; try lia
           end.
      all: match goal with |- ?G => idtac "C1-LEFT:" G end. }
    clear C1. intros [ms2 mo2] PO. unfold biofreeint_b64_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & s2' & LB1 &
                    -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & HEAP2 & PERM1 & IM2 & GM2 & METHB2 & SL2 & XP2).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST2, XP2 by lia. rewrite errno_RATP in ERR2.
    assert (HB2 := HH_blocks_below H HH _ _ _ HEAP2).
    (* [comment removed for export] *)
    assert (KEEP : forall b, In b LB -> b <> (bf_id R, a, 128) -> b <> (bf_cid R, bf_ctx R, 2584) -> b <> (bf_eid R, bf_enc R, 92) -> In b LB1).
    { intros b Hb N1b N2b N3b. pose proof (Permutation_in _ PERM1 Hb) as K. unfold blocks_B64F, BIO_SIZE, B64CTX_SIZE in K. cbn [app] in K.
      destruct K as [K|[K|[K|K]]]; [congruence| congruence| congruence| exact K]. }
    assert (SUB1 : forall b, In b LB1 -> In b LB).
    { intros b Hb. apply (Permutation_in _ (Permutation_sym PERM1)). apply in_or_app. right. exact Hb. }
    assert (INm1 : In (mb_id M, mb, 128) LB1) by (apply KEEP; [exact INm| congruence| congruence| congruence]).
    assert (INbb1 : In (mb_bbid M, mb_bb M, 16) LB1) by (apply KEEP; [exact INbb| congruence| congruence| congruence]).
    assert (INbm1 : In (mb_bmid M, mb_bm M, 32) LB1) by (apply KEEP; [exact INbm| congruence| congruence| congruence]).
    assert (INrp1 : In (mb_rpid M, mb_rp M, 32) LB1) by (apply KEEP; [exact INrp| congruence| congruence| congruence]).
    assert (INx1 : In (xq, xa, 40) LB1) by (apply KEEP; [exact XIN| congruence| congruence| congruence]).
    assert (OIN1 : In (po, cx_olock x, 40) LB1) by (apply KEEP; [exact OIN| congruence| congruence| congruence]).
    assert (IIN1 : In (pi, cx_ilock x, 40) LB1) by (apply KEEP; [exact IIN| congruence| congruence| congruence]).
    (* [comment removed for export] *)
    assert (XP12 : xpres LB1 (bv_unsigned sp) [] m1 m2).
    { intros q Hq [HC HX]. apply XP2; [exact Hq|]. split.
      - destruct HC as [K|[K|K]]; [left; lia| right; left; exact K| right; right; exact K].
      - cbn. intros [[K1 K2]|[]]. destruct HC as [K|[[K _]|(b & Hb & Hr)]]; [lia| lia|]. pose proof (HB2 b Hb). lia. }
    unhide AI; unhide CI; unhide EI; unhide MI_; unhide BBI; unhide BMI; unhide RPI; unhide XI.
    assert (AGL2 : magree (lib_addr LB1) m1 m2).
    { eapply magree_mono; [eapply magree_lib_of_xpres_fr; exact XP12|]. intros q HL. split; [exact HL| cbn; tauto]. }
    assert (CPH1' : CTXPH LB1 m1 (CtxReady x)).
    { cbn [CTXPH] in CPH1 |- *. destruct CPH1 as [CS1 [EX1 _]]. split; [exact CS1|]. split.
      - unfold EXLOCK in EX1 |- *. rewrite EXB in EX1 |- *. cbn [blk_addr blk_size fst snd] in EX1 |- *. destruct EX1 as (_ & K2 & K3 & K4).
        split; [exact INx1| split; [exact K2| split; [exact K3| exact K4]]].
      - exists po, pi. split; [exact OIN1| exact IIN1]. }
    assert (CPH2 : CTXPH LB1 m2 (CtxReady x)) by (eapply CTXPH_frame; [exact CPH1'| exact AGL2]).
    assert (MB2 : MEMBIO LB1 m2 mb M).
    { eapply (MEMBIO_frame0 LB LB1); [exact MB1| | exact XP12]. unfold blocks_MEMBIO, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE.
      intros b [<-|[<-|[<-|[<-|[]]]]]; assumption. }
    pose proof MB2 as (MBA2 & _).
    assert (FRJ2 : rw_cells usegs m2 (bv_unsigned sp + -32) [CB 4 j]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2); [exact FRJ1| left; cbn; lia| apply Forall_cons; [cbn; lia| apply Forall_nil]]. }
    assert (FR32 : rw_cells usegs m2 (bv_unsigned sp + -24) [C8 s1; C8 s0; C8 ra]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2); [exact FR31| left; cbn; lia| apply Forall_cons; [cbn; lia| apply Forall_nil]]. }
    assert (METHM2 : rw_cells usegs m2 (A_mem_buf_method + 32)
      [C8 (wz P_bread_conv); C8 (wz P_mem_read); C8 (wz P_mem_puts); C8 (wz P_mem_gets); C8 (wz P_mem_ctrl); C8 (wz P_mem_new); C8 (wz P_mem_free); C8 (wz 0)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2); [exact METHM1| static_tac| apply Forall_cons; [unfold A_mem_buf_method; cbn; lia| apply Forall_nil]]. }
    unfold METH_b64, O_METH_BREAD in METHB2.
    hide AI; hide CI; hide EI; hide MI_; hide BBI; hide BMI; hide RPI; hide XI.
    (* [comment removed for export] *)
    rewrite NXT.
    eapply (sr_evt_krel H HH); [exact KREL2| eapply bfa_seg2 with (lo := lo) (mb := mb) (B := membio_bio M) (j := j); cbn [membio_bio bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite];
      try first [exact RM| exact MBA2| exact FRJ2| exact SL2| exact FR32| exact ST2| exact CEIL| exact MI2]; try (unfold A_mem_buf_method; lia)|].
    all: try match goal with |- forall _, _ => idtac | |- ?G => idtac "A2-LEFT:" G end.
    intros ms3 (m3 & -> & MU3 & WM3 & MI3 & ST3 & SL3).
    cbn [membio_bio bio_next] in *. rewrite MNX.
    unhide AI; unhide CI; unhide EI; unhide MI_; unhide BBI; unhide BMI; unhide RPI; unhide XI.
    assert (HP3 : hs_RHEAP H s2' LB1 m3).
    { eapply (HH_RHEAP_frame H HH); [exact HEAP2| exact MU3| exact WM3|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (AUX3 : hs_rauxv_ok H m3 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX2| exact MU3| exact WM3|]. unfold RAUXV_CELL. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
    apply (rw_cells_transport usegs _ m2 m3 _ _ ERR2) in MU3 as ERR3; [| exact WM3| unfold RERRNO; cbn; lia].
    assert (IM3 : IMPL_mem m3) by (eapply IMPL_across; [exact MU3| exact WM3| unfold A_malloc_impl; cbn; lia| exact IM2]).
    assert (GM3 : GOT_mem m3) by (eapply GOT_across; [exact MU3| exact WM3| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM2]).
    apply (rw_cells_transport usegs _ m2 m3 _ _ FRJ2) in MU3 as FRJ3; [| exact WM3| cbn; lia].
    apply (rw_cells_transport usegs _ m2 m3 _ _ FR32) in MU3 as FR33; [| exact WM3| cbn; lia].
    apply (rw_cells_transport usegs _ m2 m3 _ _ METHB2) in MU3 as METHB3; [| exact WM3| unfold A_b64_method; cbn; lia].
    apply (rw_cells_transport usegs _ m2 m3 _ _ METHM2) in MU3 as METHM3; [| exact WM3| unfold A_mem_buf_method; cbn; lia].
    assert (XP23 : xpres LB1 (bv_unsigned sp) [] m2 m3).
    { eapply (xpres_of_munch_exX H HH s2' LB1 m2 m2 m3 (bv_unsigned sp) [] _ LB1 []); [exact HEAP2| lia| exact MU3| exact WM3| | |].
      - intros b Hb. split; [exact Hb| intros hb []].
      - intros hb [].
      - apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (AGL3 : magree (lib_addr LB1) m2 m3).
    { eapply magree_mono; [eapply magree_lib_of_xpres_fr; exact XP23|]. intros q HL. split; [exact HL| cbn; tauto]. }
    assert (CPH3 : CTXPH LB1 m3 (CtxReady x)) by (eapply CTXPH_frame; [exact CPH2| exact AGL3]).
    assert (MB3 : MEMBIO LB1 m3 mb M).
    { eapply (MEMBIO_frame0 LB1 LB1); [exact MB2| | exact XP23]. unfold blocks_MEMBIO, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE.
      intros b [<-|[<-|[<-|[<-|[]]]]]; assumption. }
    hide AI; hide CI; hide EI; hide MI_; hide BBI; hide BMI; hide RPI; hide XI.
    (* [comment removed for export] *)
    pose proof (biofreeint_mem_spec H HH (@cfreeex_spec HCEIL)) as C2.  (* [comment removed for export] *) unfold biofreeint_mem_stmt in C2.
    eapply (sr_seq H HH).
    { eapply C2 with (lo := lo) (B := B) (LB := LB1) (s := s2') (x := x) (a := mb) (rbp := bv_unsigned sp + -28) (R := M); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact SL3| exact MB3| exact APARTM| exact CPH3| exact HP3| exact KREL2| exact AUX3| exact ST3| exact CEIL| exact MI3| exact IM3| exact GM3].
      all: lazymatch goal with
           | |- rw_cells _ _ (errno_addr _) _ => rewrite errno_RATP; exact ERR3
           | |- METH_mem _ => unfold METH_mem, O_METH_BREAD; exact METHM3
           | |- _ mod 2 = 0 => unfold BFA_RA; rewrite unsigned_lit by lia; reflexivity
           | |- _ => try stack_lia; try lia
           end.
      all: match goal with |- ?G => idtac "C2-LEFT:" G end. }
    clear C2. intros [ms4 mo4] PO. unfold biofreeint_mem_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m4 & errv4 & s4' & LB2 &
                    -> & KREL4 & MP4 & MI4 & ST4 & ERR4 & AUX4 & HEAP4 & PERM2 & IM4 & GM4 & METHM4 & SL4 & XP4).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST4, XP4 by lia. rewrite errno_RATP in ERR4.
    assert (HB4 := HH_blocks_below H HH _ _ _ HEAP4).
    assert (SUB2 : forall b, In b LB2 -> In b LB1).
    { intros b Hb. apply (Permutation_in _ (Permutation_sym PERM2)). apply in_or_app. right. exact Hb. }
    assert (XP34 : xpres LB2 (bv_unsigned sp) [] m3 m4).
    { intros q Hq [HC HX]. apply XP4; [exact Hq|]. split.
      - destruct HC as [K|[K|K]]; [left; lia| right; left; exact K| right; right; exact K].
      - cbn. intros [[K1 K2]|[]]. destruct HC as [K|[[K _]|(b & Hb & Hr)]]; [lia| lia|]. pose proof (HB4 b Hb). lia. }
    assert (FRJ4 : rw_cells usegs m4 (bv_unsigned sp + -32) [CB 4 j]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP4); [exact FRJ3| left; cbn; lia| apply Forall_cons; [cbn; lia| apply Forall_nil]]. }
    assert (FR34 : rw_cells usegs m4 (bv_unsigned sp + -24) [C8 s1; C8 s0; C8 ra]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP4); [exact FR33| left; cbn; lia| apply Forall_cons; [cbn; lia| apply Forall_nil]]. }
    assert (METHB4 : rw_cells usegs m4 (A_b64_method + 32)
      [C8 (wz P_bread_conv); C8 (wz P_b64_read); C8 (wz P_b64_puts); C8 (wz 0); C8 (wz P_b64_ctrl); C8 (wz P_b64_new); C8 (wz P_b64_free); C8 (wz P_b64_callback_ctrl)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP4); [exact METHB3| static_tac| apply Forall_cons; [unfold A_b64_method; cbn; lia| apply Forall_nil]]. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL4| eapply bfa_seg3 with (lo := lo); [exact FRJ4| exact SL4| exact FR34| exact ST4| exact CEIL| lia| exact MI4| exact RAE]|].
    intros ms5 [-> ST4'].
    apply (sr_done H HH). unfold biofreeall_post. cbn [cfg_ms cfg_model].
    exists v0, v1, v2, (Z_to_bv 64 0), c1, c2, c3, c4, c5, c6, c7, v3, v4, v5, v6, m4, errv4, s4', LB2.
    split; [reflexivity|]. split; [exact KREL4|].
    split; [eapply (mpres_trans H HH); [exact MP2| exact MP4]|].
    split; [exact MI4|]. split; [exact ST4'|]. split; [rewrite errno_RATP; exact ERR4|]. split; [exact AUX4|]. split; [exact HEAP4|].
    split.
    { (* [comment removed for export] *)
      eapply Permutation_trans; [exact PERM1|]. apply Permutation_app_head. exact PERM2. }
    split; [exact IM4|]. split; [exact GM4|]. split; [unfold METH_b64, O_METH_BREAD; exact METHB4|]. split; [exact METHM4|].
    (* [comment removed for export] *)
    eapply xpres_trans; [eapply xpres_weaken; [exact XP01| lia| intros b Hb; apply SUB1, SUB2; exact Hb| cbn; tauto]|].
    eapply xpres_trans; [eapply xpres_weaken; [exact XP12| lia| intros b Hb; apply SUB2; exact Hb| cbn; tauto]|].
    eapply xpres_trans; [eapply xpres_weaken; [exact XP23| lia| intros b Hb; apply SUB2; exact Hb| cbn; tauto]|].
    exact XP34.
  Qed.
End W.
