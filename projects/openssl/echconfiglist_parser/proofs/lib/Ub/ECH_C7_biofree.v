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
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface F_memcpy ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_KitH ECH_Rep ECH_LibState ECH_LibStateMF ECH_LibFrame ECH_C0_stmt ECH_C2_stmt ECH_C1_stmt ECH_C1_malloc ECH_C1_free ECH_C3_stmt ECH_C6_stmt ECH_C6_buf ECH_C7_stmt ECH_C7_read ECH_C7_new ECH_C7_free.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma nodup_ids_ne : forall (L : list block) b1 b2, List.NoDup (map blk_id L) -> In b1 L -> In b2 L -> b1 <> b2 -> blk_id b1 <> blk_id b2.
Proof.
  induction L as [|c L IH]; intros b1 b2 ND H1 H2 NE; [destruct H1|]. cbn in ND. inversion ND as [|x l NI ND']; subst.
  destruct H1 as [->|H1], H2 as [->|H2].
  - congruence.
  - intros E. apply NI. rewrite E. apply in_map. exact H2.
  - intros E. apply NI. rewrite <- E. apply in_map. exact H1.
  - exact (IH _ _ ND' H1 H2 NE).
Qed.

Lemma perm4_tail : forall (A : Type) (x1 x2 x3 x4 : A) l, Permutation (x1 :: x2 :: x3 :: x4 :: l) (x4 :: x3 :: x1 :: x2 :: l).
Proof.
  intros A x1 x2 x3 x4 l.
  change (x4 :: x3 :: x1 :: x2 :: l) with ([x4; x3] ++ x1 :: x2 :: l).
  apply Permutation_cons_app. cbn.
  change (x4 :: x3 :: x2 :: l) with ([x4; x3] ++ x2 :: l).
  apply Permutation_cons_app. cbn. apply perm_swap.
Qed.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.
  (* [comment removed for export] *)
  Hypothesis CFX : cfreeex_stmt.

  Local Ltac static_tac := right; left; unfold A_mem_buf_method, O_METH_BREAD, A_next_key, A_key_lock, A_td_cancelbuf, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK; cbn; lia.

  (* [comment removed for export] *)
  Lemma magree_lib_of_xpres_fr : forall LB SP X m m',
    xpres LB SP X m m' -> magree (fun a => lib_addr LB a /\ ~ rin_ivs X a) m m'.
  Proof.
    intros LB SP X m m' XP a Ha [HL HXa]. apply XP; [exact Ha|]. split; [| exact HXa].
    destruct HL as [HL|HBk]; [| right; right; exact HBk].
    right; left. unfold LIBX, LIBX0 in HL. cbn [rin_ivs fst snd] in HL. unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma xpres_of_munch_ex : forall s LB m0 m m' SP W (L' EX : list block),
    hs_RHEAP H s LB m0 -> hceil <= SP -> munch W m m' -> wmono usegs m m' ->
    (forall b, In b L' -> In b LB /\ (forall hb, In hb EX -> blk_id b <> blk_id hb)) ->
    (forall hb, In hb EX -> In hb LB) ->
    Forall (fun iv : Z * Z => (hceil <= fst iv /\ snd iv <= SP)
                              \/ (exists hb, In hb EX /\ blk_addr hb <= fst iv /\ snd iv <= blk_addr hb + blk_size hb)) W ->
    xpres L' SP [] m m'.
  Proof.
    intros s LB m0 m m' SP W L' EX HP CE MU WM HL HEX FW. hcb.
    eapply xpres_of_munch_gen; [exact MU| exact WM|].
    intros a Ha [HC _].
    clear MU WM. induction W as [|[lo hi] W IH]; [exact I|]. cbn.
    pose proof (Forall_inv FW) as K1. cbn in K1.
    split; [| apply IH; apply (Forall_inv_tail FW)].
    destruct K1 as [[K1 K2]|(hb & Hhb & K1 & K2)].
    - destruct HC as [HC|[[HC _]|(b & Hb & Hr)]]; [lia| lia|].
      destruct (HL b Hb) as [HbL _]. pose proof (HH_blocks_below H HH _ _ _ HP b HbL). lia.
    - pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP (HEX hb Hhb)) as (B1 & B2 & B3 & B4 & B5).
      destruct HC as [HC|[[[HC1 HC2] _]|(b & Hb & Hr)]]; [lia| lia|].
      destruct (HL b Hb) as [HbL HNE].
      pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ b hb HP HbL (HEX hb Hhb) (HNE hb Hhb)) as D. lia.
  Qed.

  Lemma biofree_spec : biofree_mem_stmt H.
  Proof.
    unfold biofree_mem_stmt. intros until errv.
    intros A0 MB APART CPH HP KREL AUX SPB SPAL ST CEIL LO ERR MI TP IM GM METH RAE.
    unfold BIOFREE_STACK, MEMFREE_STACK, BUFFREE_STACK, CFREE_STACK, CFREEEX_STACK, RFREE_STACK, FR_BIO_free, FR_BIO_free_int, FR_mem_free, FR_mem_buf_free,
      FR_BUF_MEM_free, FR_CRYPTO_free_ex_data, GETGLOBAL_READY_STACK, NEWEX_INNER, GETANDLOCK_STACK, FR_get_and_lock, CRWLOCK_STACK, CUNLOCK_STACK,
      FR_mutex_unlock, FR_pthread_mutex_unlock, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock, FR_ossl_lib_ctx_get_ex_data_global, GETDEFCTX_STACK, FR_get_default_context in LO.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    subst tp. rewrite errno_RATP in ERR.
    pose proof MB as (BA & BB & BM & BRP & INa & INbb & INbm & INrp & RA & RBB & RBM & RRP & POS & LEN & BUFP & BUFH & FL & RDO & L128 & NUMF & NRD0 & NRDB & NXT & PRV).
    pose proof RA as (AP & AAL & _ & AH & AI). pose proof RBB as (BBP & _ & _ & BBH & BBI). pose proof RBM as (BMP & _ & _ & BMH & BMI). pose proof RRP as (RPP & _ & _ & RPH & RPI).
    pose proof APART as (AP1 & AP2 & AP3 & AP4 & AP5 & AP6). unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in AH, AI, BBH, BBI, BMH, BMI, RPH, RPI, AP1, AP2, AP3, AP4, AP5, AP6.
    cbn [CTXPH] in CPH. destruct CPH as [CS [EX OI]]. pose proof EX as (XIN & XSZ & XRR & XM).
    destruct (cx_exlock x) as [[xq xa] xn] eqn:EXB. cbn [blk_addr blk_size blk_id fst snd] in XIN, XSZ, XRR, XM. unfold MUTEX_SIZE in XSZ. subst xn.
    pose proof XRR as (XP1 & _ & _ & XH & XI). unfold MUTEX_SIZE in XH, XI.
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ HP) as ND0.
    (* [comment removed for export] *)
    assert (NE_bb_bm : (mb_bbid R, mb_bb R, 16) <> (mb_bmid R, mb_bm R, 32)) by (intros E; congruence).
    assert (NE_rp_bm : (mb_rpid R, mb_rp R, 32) <> (mb_bmid R, mb_bm R, 32)) by (intros E; injection E; intros; lia).
    assert (NE_id_bm : (mb_id R, a, 128) <> (mb_bmid R, mb_bm R, 32)) by (intros E; congruence).
    assert (NE_x_bm : (xq, xa, 40) <> (mb_bmid R, mb_bm R, 32)) by (intros E; congruence).
    assert (NE_bb_rp : (mb_bbid R, mb_bb R, 16) <> (mb_rpid R, mb_rp R, 32)) by (intros E; congruence).
    assert (NE_id_rp : (mb_id R, a, 128) <> (mb_rpid R, mb_rp R, 32)) by (intros E; congruence).
    assert (NE_x_rp : (xq, xa, 40) <> (mb_rpid R, mb_rp R, 32)) by (intros E; congruence).
    assert (NE_id_bb : (mb_id R, a, 128) <> (mb_bbid R, mb_bb R, 16)) by (intros E; congruence).
    assert (NE_x_bb : (xq, xa, 40) <> (mb_bbid R, mb_bb R, 16)) by (intros E; congruence).
    assert (NE_x_id : (xq, xa, 40) <> (mb_id R, a, 128)) by (intros E; congruence).
    unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in INa, INbb, INbm, INrp.
    pose proof (nodup_ids_ne LB _ _ ND0 INbb INbm NE_bb_bm) as ID_bb_bm.
    pose proof (nodup_ids_ne LB _ _ ND0 INrp INbm NE_rp_bm) as ID_rp_bm.
    pose proof (nodup_ids_ne LB _ _ ND0 INa INbm NE_id_bm) as ID_id_bm.
    pose proof (nodup_ids_ne LB _ _ ND0 XIN INbm NE_x_bm) as ID_x_bm.
    pose proof (nodup_ids_ne LB _ _ ND0 INbb INrp NE_bb_rp) as ID_bb_rp.
    pose proof (nodup_ids_ne LB _ _ ND0 INa INrp NE_id_rp) as ID_id_rp.
    pose proof (nodup_ids_ne LB _ _ ND0 XIN INrp NE_x_rp) as ID_x_rp.
    pose proof (nodup_ids_ne LB _ _ ND0 INa INbb NE_id_bb) as ID_id_bb.
    pose proof (nodup_ids_ne LB _ _ ND0 XIN INbb NE_x_bb) as ID_x_bb.
    pose proof (nodup_ids_ne LB _ _ ND0 XIN INa NE_x_id) as ID_x_id.
    cbn [blk_id fst snd] in ID_bb_bm, ID_rp_bm, ID_id_bm, ID_x_bm, ID_bb_rp, ID_id_rp, ID_x_rp, ID_id_bb, ID_x_bb, ID_x_id.
    (* [comment removed for export] *)
    pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ _ _ HP INa XIN ltac:(cbn; congruence)) as DJ_a_x. cbn [blk_addr blk_size fst snd] in DJ_a_x.
    pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ _ _ HP INbm XIN ltac:(cbn; congruence)) as DJ_bm_x. cbn [blk_addr blk_size fst snd] in DJ_bm_x.
    (* [comment removed for export] *)
    hide AP1; hide AP2; hide AP3; hide AP4; hide AP5; hide AP6; hide BBI; hide RPI; hide AI; hide BMI; hide XI; hide DJ_a_x; hide DJ_bm_x.
    clear APART. assert (APART : MEMBIO_apart a R) by (unhide AP1; unhide AP2; unhide AP3; unhide AP4; unhide AP5; unhide AP6; unfold MEMBIO_apart, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE; tauto).
    set (L1 := hs_lb_remove H (mb_bmid R) LB).
    set (L2 := hs_lb_remove H (mb_rpid R) L1).
    set (L3 := hs_lb_remove H (mb_bbid R) L2).
    set (L4 := hs_lb_remove H (mb_id R) L3).
    pose proof (lb_remove_exact H HH (mb_bmid R) (mb_bm R) 32 LB ND0 INbm) as (_ & _ & IFF1). fold L1 in IFF1.
    assert (INrp1 : In (mb_rpid R, mb_rp R, 32) L1) by (apply (proj2 (IFF1 _)); split; [exact INrp| exact ID_rp_bm]).
    assert (INbb1 : In (mb_bbid R, mb_bb R, 16) L1) by (apply (proj2 (IFF1 _)); split; [exact INbb| exact ID_bb_bm]).
    assert (INa1 : In (mb_id R, a, 128) L1) by (apply (proj2 (IFF1 _)); split; [exact INa| exact ID_id_bm]).
    assert (INx1 : In (xq, xa, 40) L1) by (apply (proj2 (IFF1 _)); split; [exact XIN| exact ID_x_bm]).
    assert (SUB10 : forall b, In b L1 -> In b LB) by (intros b Hb; apply (proj1 (IFF1 b)); exact Hb).
    unfold METH_mem, O_METH_BREAD in METH.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply fr_seg1 with (lo := lo); try first [exact A0| exact SPAL| exact RA| exact RBB| exact RBM| exact APART| exact BA| exact BB| exact BM| exact ST| exact CEIL| exact MI| exact NUMF]; try lia;
      unfold METH_mem, O_METH_BREAD; exact METH|].
    intros ms1 (m1 & j3 & -> & MU1 & WM1 & MI1 & ST1 & BA1 & BB1 & BM1 & METH1 & F01 & F11 & F21).
    unhide AI; unhide BMI.
    assert (HP1 : hs_RHEAP H s LB m1).
    { eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|].
      apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; right; exists (mb_id R, a, 128); split; [exact INa| cbn; lia]|].
      apply Forall_cons; [right; right; exists (mb_bmid R, mb_bm R, 32); split; [exact INbm| cbn; lia]| apply Forall_nil]. }
    assert (AUX1 : hs_rauxv_ok H m1 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]. unfold RAUXV_CELL. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
    apply (rw_cells_transport usegs _ m m1 _ _ ERR) in MU1 as ERR1; [| exact WM1| unfold RERRNO; cbn; lia].
    assert (IM1 : IMPL_mem m1) by (eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]).
    assert (GM1 : GOT_mem m1) by (eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]).
    (* [comment removed for export] *)
    assert (AG1 : magree (lib_addr [(xq, xa, 40)]) m m1).
    { eapply magree_of_munch; [exact MU1| exact WM1|]. intros q Hq HL. cbn.
      destruct HL as [HL|(b & [<-|[]] & Hr)].
      - unfold LIBX, LIBX0 in HL. cbn [rin_ivs fst snd] in HL. repeat split; lia.
      - cbn [blk_addr blk_size fst snd] in Hr. unhide DJ_a_x; unhide DJ_bm_x. repeat split; lia. }
    hide AI; hide BMI.
    destruct (bio_cells_split_ex _ _ _ BA1) as [_ EXD1].
    (* [comment removed for export] *)
    pose proof (buffree_spec H HH) as BF. unfold buffree_stmt in BF.
    eapply (sr_seq H HH).
    { eapply BF with (lo := lo) (B := B) (LB := LB) (s := s) (p := mb_bmid R) (A := mb_bm R) (len := mb_len R - mb_pos R) (mx := mb_len R - mb_pos R) (fl := 0);
        rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact BM1| exact HP1| exact KREL| exact AUX1| exact ST1| exact CEIL| exact MI1| exact IM1| exact GM1].
      all: lazymatch goal with
           | |- In _ _ => unfold BUFMEM_SIZE; exact INbm
           | |- rw_cells _ _ (errno_addr _) _ => rewrite errno_RATP; exact ERR1
           | |- _ mod 2 = 0 => unfold MBF_RA, MF_RA1; rewrite unsigned_lit by lia; reflexivity
           | |- _ => try (unfold BUFFREE_STACK, FR_BUF_MEM_free, CFREE_STACK, RFREE_STACK; lia); try lia
           end.
      all: match goal with |- ?G => idtac "BF-LEFT:" G end. }
    clear BF. intros [ms2 mo2] PO. unfold buffree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & s2' &
                    -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & XP2 & HEAP2 & IM2 & GM2).
    rewrite (unsigned_lit (bv_unsigned sp + -96)) in ST2, XP2 by lia. rewrite errno_RATP in ERR2. unfold BUFMEM_SIZE in XP2, HEAP2. fold L1 in XP2, HEAP2.
    pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ HEAP2) as ND1.
    pose proof (lb_remove_exact H HH (mb_rpid R) (mb_rp R) 32 L1 ND1 INrp1) as (_ & _ & IFF2). fold L2 in IFF2.
    assert (INbb2 : In (mb_bbid R, mb_bb R, 16) L2) by (apply (proj2 (IFF2 _)); split; [exact INbb1| exact ID_bb_rp]).
    assert (INa2 : In (mb_id R, a, 128) L2) by (apply (proj2 (IFF2 _)); split; [exact INa1| exact ID_id_rp]).
    assert (INx2 : In (xq, xa, 40) L2) by (apply (proj2 (IFF2 _)); split; [exact INx1| exact ID_x_rp]).
    assert (SUB21 : forall b, In b L2 -> In b L1) by (intros b Hb; apply (proj1 (IFF2 b)); exact Hb).
    assert (BB2 : rw_cells usegs m2 (mb_bb R) [C8 (wz (mb_bm R)); C8 (wz (mb_rp R))]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2); [exact BB1| right; right; exists (mb_bbid R, mb_bb R, 16); split; [exact INbb1| cbn; lia]| apply Forall_nil]. }
    assert (F22 : rw_cells usegs m2 (bv_unsigned sp + -96) [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 (bv_unsigned sp + -32)); C8 (Z_to_bv 64 BFI_RA1)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2); [exact F21| left; cbn; lia| apply Forall_nil]. }
    assert (F12 : rw_cells usegs m2 (bv_unsigned sp + -64) [C8 s2; C8 s1; C8 sp; C8 (Z_to_bv 64 BF_RET)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2); [exact F11| left; cbn; lia| apply Forall_nil]. }
    assert (F02 : rw_cells usegs m2 (bv_unsigned sp + -32) [CB 12 j3; C4 (wz 0); C8 s0; C8 ra]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2); [exact F01| left; cbn; lia| apply Forall_nil]. }
    assert (METH2 : rw_cells usegs m2 (A_mem_buf_method + 32)
      [C8 (wz P_bread_conv); C8 (wz P_mem_read); C8 (wz P_mem_puts); C8 (wz P_mem_gets); C8 (wz P_mem_ctrl); C8 (wz P_mem_new); C8 (wz P_mem_free); C8 (wz 0)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2); [exact METH1| static_tac| apply Forall_nil]. }
    assert (EXD2 : rw_cells usegs m2 (a + O_BIO_EXDATA) [C8 (wz 0); C8 (wz 0)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2); [exact EXD1| right; right; exists (mb_id R, a, 128); split; [exact INa1| unfold O_BIO_EXDATA; cbn; lia]| apply Forall_nil]. }
    assert (AG2 : magree (lib_addr [(xq, xa, 40)]) m1 m2).
    { eapply magree_mono; [eapply magree_lib_of_xpres_fr; exact XP2|]. intros q HL. split; [| cbn; tauto].
      destruct HL as [HL|(b & [<-|[]] & Hr)]; [left; exact HL| right]. exists (xq, xa, 40). split; [exact INx1| exact Hr]. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL2| eapply fr_seg2 with (lo := lo); [exact RBB| exact BB2| exact ST2| exact CEIL| lia| exact MI2]|].
    intros ms3 [-> ST2'].
    (* [comment removed for export] *)
    pose proof (cfree_spec H HH) as CF. unfold cfree_stmt in CF.
    eapply (sr_seq H HH).
    { eapply CF with (lo := lo) (B := B) (LB := L1) (s := s2') (p := mb_rpid R) (A := mb_rp R) (n := 32); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact HEAP2| exact KREL2| exact INrp1| exact AUX2| exact ST2'| exact CEIL| exact MI2| exact IM2| exact GM2].
      all: lazymatch goal with
           | |- rw_cells _ _ (errno_addr _) _ => rewrite errno_RATP; exact ERR2
           | |- _ => try (unfold CFREE_STACK, RFREE_STACK; lia); try lia
           end.
      all: match goal with |- ?G => idtac "CF1-LEFT:" G end. }
    intros [ms4 mo4] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & s3' &
                    -> & KREL3 & MP3 & MI3 & ST3 & ERR3 & AUX3 & XP3 & HEAP3 & IM3 & GM3).
    rewrite (unsigned_lit (bv_unsigned sp + -96)) in ST3, XP3 by lia. rewrite errno_RATP in ERR3. fold L2 in XP3, HEAP3.
    pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ HEAP3) as ND2.
    pose proof (lb_remove_exact H HH (mb_bbid R) (mb_bb R) 16 L2 ND2 INbb2) as (_ & _ & IFF3). fold L3 in IFF3.
    assert (INa3 : In (mb_id R, a, 128) L3) by (apply (proj2 (IFF3 _)); split; [exact INa2| exact ID_id_bb]).
    assert (INx3 : In (xq, xa, 40) L3) by (apply (proj2 (IFF3 _)); split; [exact INx2| exact ID_x_bb]).
    assert (SUB32 : forall b, In b L3 -> In b L2) by (intros b Hb; apply (proj1 (IFF3 b)); exact Hb).
    assert (F23 : rw_cells usegs m3 (bv_unsigned sp + -96) [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 (bv_unsigned sp + -32)); C8 (Z_to_bv 64 BFI_RA1)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP3); [exact F22| left; cbn; lia| apply Forall_nil]. }
    assert (F13 : rw_cells usegs m3 (bv_unsigned sp + -64) [C8 s2; C8 s1; C8 sp; C8 (Z_to_bv 64 BF_RET)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP3); [exact F12| left; cbn; lia| apply Forall_nil]. }
    assert (F03 : rw_cells usegs m3 (bv_unsigned sp + -32) [CB 12 j3; C4 (wz 0); C8 s0; C8 ra]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP3); [exact F02| left; cbn; lia| apply Forall_nil]. }
    assert (METH3 : rw_cells usegs m3 (A_mem_buf_method + 32)
      [C8 (wz P_bread_conv); C8 (wz P_mem_read); C8 (wz P_mem_puts); C8 (wz P_mem_gets); C8 (wz P_mem_ctrl); C8 (wz P_mem_new); C8 (wz P_mem_free); C8 (wz 0)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP3); [exact METH2| static_tac| apply Forall_nil]. }
    assert (EXD3 : rw_cells usegs m3 (a + O_BIO_EXDATA) [C8 (wz 0); C8 (wz 0)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP3); [exact EXD2| right; right; exists (mb_id R, a, 128); split; [exact INa2| unfold O_BIO_EXDATA; cbn; lia]| apply Forall_nil]. }
    assert (AG3 : magree (lib_addr [(xq, xa, 40)]) m2 m3).
    { eapply magree_mono; [eapply magree_lib_of_xpres_fr; exact XP3|]. intros q HL. split; [| cbn; tauto].
      destruct HL as [HL|(b & [<-|[]] & Hr)]; [left; exact HL| right]. exists (xq, xa, 40). split; [exact INx2| exact Hr]. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL3| eapply fr_seg3; exact MI3|].
    intros ms5 ->.
    (* [comment removed for export] *)
    eapply (sr_seq H HH).
    { eapply CF with (lo := lo) (B := B) (LB := L2) (s := s3') (p := mb_bbid R) (A := mb_bb R) (n := 16); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact HEAP3| exact KREL3| exact INbb2| exact AUX3| exact ST3| exact CEIL| exact MI3| exact IM3| exact GM3].
      all: lazymatch goal with
           | |- rw_cells _ _ (errno_addr _) _ => rewrite errno_RATP; exact ERR3
           | |- _ => try (unfold CFREE_STACK, RFREE_STACK; lia); try lia
           end.
      all: match goal with |- ?G => idtac "CF2-LEFT:" G end. }
    intros [ms6 mo6] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m4 & s4' &
                    -> & KREL4 & MP4 & MI4 & ST4 & ERR4 & AUX4 & XP4 & HEAP4 & IM4 & GM4).
    rewrite (unsigned_lit (bv_unsigned sp + -96)) in ST4, XP4 by lia. rewrite errno_RATP in ERR4. fold L3 in XP4, HEAP4.
    pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ HEAP4) as ND3.
    pose proof (lb_remove_exact H HH (mb_id R) a 128 L3 ND3 INa3) as (_ & _ & IFF4). fold L4 in IFF4.
    assert (SUB43 : forall b, In b L4 -> In b L3) by (intros b Hb; apply (proj1 (IFF4 b)); exact Hb).
    assert (F24 : rw_cells usegs m4 (bv_unsigned sp + -96) [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 (bv_unsigned sp + -32)); C8 (Z_to_bv 64 BFI_RA1)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP4); [exact F23| left; cbn; lia| apply Forall_nil]. }
    assert (F14 : rw_cells usegs m4 (bv_unsigned sp + -64) [C8 s2; C8 s1; C8 sp; C8 (Z_to_bv 64 BF_RET)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP4); [exact F13| left; cbn; lia| apply Forall_nil]. }
    assert (F04 : rw_cells usegs m4 (bv_unsigned sp + -32) [CB 12 j3; C4 (wz 0); C8 s0; C8 ra]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP4); [exact F03| left; cbn; lia| apply Forall_nil]. }
    assert (METH4 : rw_cells usegs m4 (A_mem_buf_method + 32)
      [C8 (wz P_bread_conv); C8 (wz P_mem_read); C8 (wz P_mem_puts); C8 (wz P_mem_gets); C8 (wz P_mem_ctrl); C8 (wz P_mem_new); C8 (wz P_mem_free); C8 (wz 0)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP4); [exact METH3| static_tac| apply Forall_nil]. }
    assert (EXD4 : rw_cells usegs m4 (a + O_BIO_EXDATA) [C8 (wz 0); C8 (wz 0)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP4); [exact EXD3| right; right; exists (mb_id R, a, 128); split; [exact INa3| unfold O_BIO_EXDATA; cbn; lia]| apply Forall_nil]. }
    assert (AG4 : magree (lib_addr [(xq, xa, 40)]) m3 m4).
    { eapply magree_mono; [eapply magree_lib_of_xpres_fr; exact XP4|]. intros q HL. split; [| cbn; tauto].
      destruct HL as [HL|(b & [<-|[]] & Hr)]; [left; exact HL| right]. exists (xq, xa, 40). split; [exact INx3| exact Hr]. }
    pose proof (magree_trans _ _ _ _ AG1 (magree_trans _ _ _ _ AG2 (magree_trans _ _ _ _ AG3 AG4))) as AG04.
    assert (CS4 : CTX_statics m4 x) by (eapply (CTX_statics_frame [(xq, xa, 40)]); [exact CS| exact AG04]).
    assert (EX4 : EXLOCK L3 m4 (xq, xa, 40)).
    { assert (EX0 : EXLOCK [(xq, xa, 40)] m (xq, xa, 40)) by (split; [left; reflexivity| exact (proj2 EX)]).
      pose proof (EXLOCK_frame _ _ _ _ EX0 AG04) as [_ K]. split; [exact INx3| exact K]. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL4| eapply fr_seg4 with (lo := lo); [exact F24| exact AP| unfold BIO_SIZE; exact AH| exact ST4| exact CEIL| lia| exact MI4]|].
    intros ms7 [-> ST4'].
    (* [comment removed for export] *)
    pose proof CFX as CX. unfold cfreeex_stmt in CX. cbv zeta in CX.
    eapply (sr_evt_krel H HH).
    { exact KREL4. }
    { eapply CX with (lo := lo) (LB := L3) (x := x) (obj := a) (ad := a + O_BIO_EXDATA); rewrite ?EXB; cbn [blk_addr blk_size fst snd];
        rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact EXD4| exact CS4| exact EX4| exact ST4'| exact CEIL| exact MI4| exact IM4| exact GM4].
      all: lazymatch goal with
           | |- off_image _ _ => unhide AI; unfold off_image, IMG_LO, IMG_HI, O_BIO_EXDATA; lia
           | |- _ mod 2 = 0 => unfold BFI_RA2; rewrite unsigned_lit by lia; reflexivity
           | |- _ mod 8 = 0 => unfold O_BIO_EXDATA; clear - AAL; lia                    (* [comment removed for export] *)
           | |- _ \/ _ => unhide DJ_a_x; unfold O_BIO_EXDATA, MUTEX_SIZE; lia
           | |- context [CFREEEX_STACK] => unfold CFREEEX_STACK, FR_CRYPTO_free_ex_data, GETGLOBAL_READY_STACK, NEWEX_INNER, GETANDLOCK_STACK, FR_get_and_lock, CRWLOCK_STACK, CUNLOCK_STACK,
                             FR_mutex_unlock, FR_pthread_mutex_unlock, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock, FR_ossl_lib_ctx_get_ex_data_global, GETDEFCTX_STACK, FR_get_default_context; lia
           | |- _ => try (unfold O_BIO_EXDATA; lia)
           end.
      all: match goal with |- ?G => idtac "CX-LEFT:" G end. }
    clear CX. intros ms8 PO. unfold c3_post in PO.
    destruct PO as (x0 & x1 & x2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & x3 & x4 & x5 & x6 & m5 & -> & -> & MU5 & WM5 & MI5 & ST5 & CS5 & EX5 & EXD5).
    rewrite (unsigned_lit (bv_unsigned sp + -64)) in MU5, ST5 by lia. rewrite EXB in MU5. cbn [blk_addr fst snd] in MU5. unfold mutex_foot, O_BIO_EXDATA in MU5.
    unhide AI; unhide XI.
    assert (HEAP5 : hs_RHEAP H s4' L3 m5).
    { eapply (HH_RHEAP_frame H HH); [exact HEAP4| exact MU5| exact WM5|].
      apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; right; exists (mb_id R, a, 128); split; [exact INa3| cbn; lia]|].
      apply Forall_cons; [right; right; exists (xq, xa, 40); split; [exact INx3| cbn; lia]| apply Forall_nil]. }
    assert (AUX5 : hs_rauxv_ok H m5 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX4| exact MU5| exact WM5|]. unfold RAUXV_CELL. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
    apply (rw_cells_transport usegs _ m4 m5 _ _ ERR4) in MU5 as ERR5; [| exact WM5| unfold RERRNO; cbn; lia].
    assert (IM5 : IMPL_mem m5) by (eapply IMPL_across; [exact MU5| exact WM5| unfold A_malloc_impl; cbn; lia| exact IM4]).
    assert (GM5 : GOT_mem m5) by (eapply GOT_across; [exact MU5| exact WM5| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM4]).
    apply (rw_cells_transport usegs _ m4 m5 _ _ F14) in MU5 as F15; [| exact WM5| cbn; lia].
    apply (rw_cells_transport usegs _ m4 m5 _ _ F04) in MU5 as F05; [| exact WM5| cbn; lia].
    apply (rw_cells_transport usegs _ m4 m5 _ _ METH4) in MU5 as METH5; [| exact WM5| unfold A_mem_buf_method; cbn; lia].
    hide AI; hide XI.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL4| eapply fr_seg5; exact MI5|].
    intros ms9 ->.
    (* [comment removed for export] *)
    eapply (sr_seq H HH).
    { eapply CF with (lo := lo) (B := B) (LB := L3) (s := s4') (p := mb_id R) (A := a) (n := 128); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact HEAP5| exact KREL4| exact INa3| exact AUX5| exact ST5| exact CEIL| exact MI5| exact IM5| exact GM5].
      all: lazymatch goal with
           | |- rw_cells _ _ (errno_addr _) _ => rewrite errno_RATP; exact ERR5
           | |- _ => try (unfold CFREE_STACK, RFREE_STACK; lia); try lia
           end.
      all: match goal with |- ?G => idtac "CF3-LEFT:" G end. }
    clear CF. intros [ms10 mo10] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (y0 & y1 & y2 & f0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & y3 & y4 & y5 & y6 & m6 & s6' &
                    -> & KREL6 & MP6 & MI6 & ST6 & ERR6 & AUX6 & XP6 & HEAP6 & IM6 & GM6).
    rewrite (unsigned_lit (bv_unsigned sp + -64)) in ST6, XP6 by lia. rewrite errno_RATP in ERR6. fold L4 in XP6, HEAP6.
    assert (F16 : rw_cells usegs m6 (bv_unsigned sp + -64) [C8 s2; C8 s1; C8 sp; C8 (Z_to_bv 64 BF_RET)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP6); [exact F15| left; cbn; lia| apply Forall_nil]. }
    assert (F06 : rw_cells usegs m6 (bv_unsigned sp + -32) [CB 12 j3; C4 (wz 0); C8 s0; C8 ra]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP6); [exact F05| left; cbn; lia| apply Forall_nil]. }
    assert (METH6 : rw_cells usegs m6 (A_mem_buf_method + 32)
      [C8 (wz P_bread_conv); C8 (wz P_mem_read); C8 (wz P_mem_puts); C8 (wz P_mem_gets); C8 (wz P_mem_ctrl); C8 (wz P_mem_new); C8 (wz P_mem_free); C8 (wz 0)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP6); [exact METH5| static_tac| apply Forall_nil]. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL6| eapply fr_seg6 with (lo := lo); [exact F16| exact F06| exact ST6| exact CEIL| lia| exact MI6| exact RAE]|].
    intros ms11 [-> ST6'].
    apply (sr_done H HH). unfold biofree_mem_post. cbn [cfg_ms cfg_model].
    exists y0, y1, y2, f1, f2, f3, f4, f5, f6, f7, y3, y4, y5, y6, m6, errv2, s6', L4.
    split; [reflexivity|]. split; [exact KREL6|].
    split; [eapply (mpres_trans H HH); [exact MP2| eapply (mpres_trans H HH); [exact MP3| eapply (mpres_trans H HH); [exact MP4| exact MP6]]]|].
    split; [exact MI6|]. split; [exact ST6'|]. split; [rewrite errno_RATP; exact ERR6|]. split; [exact AUX6|]. split; [exact HEAP6|].
    split.
    { (* [comment removed for export] *)
      unfold blocks_MEMBIO, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE. cbn [app].
      apply Permutation_sym.
      eapply Permutation_trans; [| exact (lb_remove_perm H HH _ _ _ _ _ _ HP INbm)]. fold L1.
      eapply Permutation_trans; [| apply perm_skip; exact (lb_remove_perm H HH _ _ _ _ _ _ HEAP2 INrp1)]. fold L2.
      eapply Permutation_trans; [| apply perm_skip; apply perm_skip; exact (lb_remove_perm H HH _ _ _ _ _ _ HEAP3 INbb2)]. fold L3.
      eapply Permutation_trans; [| apply perm_skip; apply perm_skip; apply perm_skip; exact (lb_remove_perm H HH _ _ _ _ _ _ HEAP5 INa3)]. fold L4.
      apply Permutation_sym. apply perm4_tail. }
    split; [exact IM6|]. split; [exact GM6|]. split; [unfold METH_mem, O_METH_BREAD; exact METH6|].
    (* [comment removed for export] *)
    assert (HL4 : forall b, In b L4 -> In b LB /\ (forall hb, In hb [(mb_id R, a, 128); (mb_bmid R, mb_bm R, 32)] -> blk_id b <> blk_id hb)).
    { intros b Hb. destruct (proj1 (IFF4 b) Hb) as [Hb3 NEa]. pose proof (SUB21 _ (SUB32 _ Hb3)) as Hb1. destruct (proj1 (IFF1 b) Hb1) as [Hb0 NEbm].
      split; [exact Hb0|]. intros hb [<-|[<-|[]]]; cbn [blk_id fst snd]; [exact NEa| exact NEbm]. }
    eapply xpres_trans.
    { eapply (xpres_of_munch_ex s LB m m m1 (bv_unsigned sp)); [exact HP| lia| exact MU1| exact WM1| exact HL4| |].
      - intros hb [<-|[<-|[]]]; [exact INa| exact INbm].
      - apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; exists (mb_id R, a, 128); split; [left; reflexivity| cbn; lia]|].
        apply Forall_cons; [right; exists (mb_bmid R, mb_bm R, 32); split; [right; left; reflexivity| cbn; lia]| apply Forall_nil]. }
    eapply xpres_trans; [eapply xpres_weaken; [exact XP2| lia| intros b Hb; apply SUB21, SUB32, SUB43; exact Hb| auto]|].
    eapply xpres_trans; [eapply xpres_weaken; [exact XP3| lia| intros b Hb; apply SUB32, SUB43; exact Hb| auto]|].
    eapply xpres_trans; [eapply xpres_weaken; [exact XP4| lia| intros b Hb; apply SUB43; exact Hb| auto]|].
    eapply xpres_trans; [| eapply xpres_weaken; [exact XP6| lia| auto| auto]].
    eapply xpres_of_munch_eq; [exact MU5| exact WM5|].
    intros q Hq [QC _]. cbn [outside].
    assert (CASE : (xa + 4 <= q < xa + 8) \/ ~ (xa + 4 <= q < xa + 8)) by lia.
    destruct CASE as [INX|OUTX].
    - right. unfold EXLOCK, MUTEX in EX4, EX5. rewrite EXB in EX5. cbn [blk_addr blk_size fst snd] in EX4, EX5.
      destruct EX4 as (_ & _ & _ & XM4). destruct EX5 as (_ & _ & _ & XM5).
      unhide XI. eapply (rw_cells_same_raw m4 m5); [exact XM4| exact XM5| cbn; lia| cbn; lia].
    - left. destruct QC as [K|[[[K1 K2] _]|(b & Hb & Hr)]]; [repeat split; lia| unhide AI; repeat split; lia|].
      destruct (HL4 b Hb) as [Hb0 HNE]. pose proof (HB b Hb0) as BLO.
      pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ b (mb_id R, a, 128) HP Hb0 INa (HNE _ (or_introl eq_refl))) as D. cbn [blk_addr blk_size fst snd] in D.
      repeat split; lia.
  Qed.
End W.
