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
     ECH_LibStateMF ECH_LibFrame ECH_C0_stmt ECH_C2_stmt ECH_C1_stmt ECH_C1_malloc ECH_C1_free ECH_C3_stmt ECH_C3_newex ECH_C6_stmt ECH_C7_stmt ECH_C8_stmt ECH_C8_small
     ECH_C9_stmt ECH_C7_read ECH_C7_new ECH_C7_free ECH_C7_freeint ECH_C7_biofree ECH_C7_biofreeint ECH_C9_new ECH_C9_free.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma perm3_rev : forall (A : Type) (x1 x2 x3 : A) l, Permutation (x1 :: x2 :: x3 :: l) (x3 :: x2 :: x1 :: l).
Proof.
  intros A x1 x2 x3 l.
  eapply Permutation_trans; [apply perm_swap|].                       (* [comment removed for export] *)
  eapply Permutation_trans; [apply perm_skip; apply perm_swap|].      (* [comment removed for export] *)
  apply perm_swap.                                                     (* [comment removed for export] *)
Qed.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.

  Local Ltac static_tac := right; left; unfold A_b64_method, O_METH_BREAD, A_next_key, A_key_lock, A_td_cancelbuf, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK; cbn; lia.

  (* [comment removed for export] *)
  Definition BIOFREEINT_B64_STACK : Z := FR_BIO_free_int + Z.max B64FREE_STACK (Z.max CFREEEX_STACK CFREE_STACK).
  Definition biofreeint_b64_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (LB : list block) (a : Z) (R : b64frep) (rbp lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun k => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : PState) (LBr : list block),
      cfg_ms k = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ hs_KREL H s' (cfg_model k) /\ hs_MPRES H mo (cfg_model k)
      /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ rw_cells rsegs m' (errno_addr tp) [C4 errv'] /\ hs_rauxv_ok H m' B
      /\ hs_RHEAP H s' LBr m' /\ Permutation LB (blocks_B64F a R ++ LBr)
      /\ IMPL_mem m' /\ GOT_mem m' /\ METH_b64 m'
      /\ rw_cells rsegs m' rbp [C4 (wz 0)]
      /\ xpres LBr (bv_unsigned sp) [(rbp, rbp + 4)] m m'.
  Definition biofreeint_b64_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (x : ctxinfo)
           (a lo B rbp : Z) (R : b64frep) (d : list Z) (errv jv : word),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 rbp -> rw_cells rsegs m rbp [C4 jv] -> bv_unsigned sp <= rbp -> rbp + 4 <= B -> rbp + 4 <= 2^64 ->
      B64F_used LB m a R -> B64F_apart a R -> ENCCTX LB m (bf_enc R) d (bf_eid R) -> CTXPH LB m (CtxReady x) ->
      hs_RHEAP H s LB m -> hs_KREL H s mo ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - BIOFREEINT_B64_STACK ->
      rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
      IMPL_mem m -> GOT_mem m -> METH_b64 m -> bv_unsigned ra mod 2 = 0 ->
      hs_SR H (biofreeint_b64_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB a R rbp lo B m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_free_int) fc None m (seg_rom rsegs)) mo).

  Lemma biofreeint_b64_spec : biofreeint_b64_stmt.
  Proof.
    unfold biofreeint_b64_stmt. intros until jv.
    intros A0 A1 SLOT RLO RB RHI BU APART ENC CPH HP KREL AUX SPB ST CEIL LO ERR MI TP IM GM METH RAE.
    unfold BIOFREEINT_B64_STACK, B64FREE_STACK, ENCFREE_STACK, FR_EVP_ENCODE_CTX_free, FR_b64_free, CFREE_STACK, CFREEEX_STACK, RFREE_STACK, FR_BIO_free_int,
      FR_CRYPTO_free_ex_data, GETGLOBAL_READY_STACK, NEWEX_INNER, GETANDLOCK_STACK, FR_get_and_lock, CRWLOCK_STACK, CUNLOCK_STACK,
      FR_mutex_unlock, FR_pthread_mutex_unlock, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock, FR_ossl_lib_ctx_get_ex_data_global, GETDEFCTX_STACK, FR_get_default_context in LO.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    subst tp. rewrite errno_RATP in ERR.
    pose proof BU as (BA & (hdr & junk & elen & LH & LJ & ELR & CTX0) & BLK).
    pose proof BLK as (INa & INc & INe & RA & RC & RE & FLR & RTR & NRR & NXR & PVR).
    pose proof RA as (AP & _ & _ & AH & AI). pose proof RC as (CP & _ & _ & CH & CI). pose proof RE as (EP & _ & _ & EH & EI).
    pose proof APART as (APac & APae & APce). unfold BIO_SIZE, B64CTX_SIZE in AH, AI, CH, CI, EH, EI, APac, APae, APce, INa, INc, INe.
    assert (ENR : 0 <= bf_enc R < 2^64) by lia. assert (CXR : 0 <= bf_ctx R < 2^64) by lia.
    pose proof ENC as (raw & line & L1e & L2e & CE & LNE & INE & RRE & DU). unfold ENCCTX_SIZE in INE, RRE.
    cbn [CTXPH] in CPH. destruct CPH as [CS [EX OI]]. pose proof EX as (XIN & XSZ & XRR & XM).
    destruct (cx_exlock x) as [[xq xa] xn] eqn:EXB. cbn [blk_addr blk_size blk_id fst snd] in XIN, XSZ, XRR, XM. unfold MUTEX_SIZE in XSZ. subst xn.
    pose proof XRR as (XP1 & _ & _ & XH & XI). unfold MUTEX_SIZE in XH, XI.
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ HP) as ND0.
    (* [comment removed for export] *)
    assert (NE_a_c : (bf_id R, a, 128) <> (bf_cid R, bf_ctx R, 2584)) by (intros E; congruence).
    assert (NE_a_e : (bf_id R, a, 128) <> (bf_eid R, bf_enc R, 92)) by (intros E; congruence).
    assert (NE_c_e : (bf_cid R, bf_ctx R, 2584) <> (bf_eid R, bf_enc R, 92)) by (intros E; congruence).
    assert (NE_x_a : (xq, xa, 40) <> (bf_id R, a, 128)) by (intros E; congruence).
    assert (NE_x_c : (xq, xa, 40) <> (bf_cid R, bf_ctx R, 2584)) by (intros E; congruence).
    assert (NE_x_e : (xq, xa, 40) <> (bf_eid R, bf_enc R, 92)) by (intros E; congruence).
    pose proof (nodup_ids_ne LB _ _ ND0 INa INc NE_a_c) as ID_a_c.
    pose proof (nodup_ids_ne LB _ _ ND0 INa INe NE_a_e) as ID_a_e.
    pose proof (nodup_ids_ne LB _ _ ND0 INc INe NE_c_e) as ID_c_e.
    pose proof (nodup_ids_ne LB _ _ ND0 XIN INa NE_x_a) as ID_x_a.
    pose proof (nodup_ids_ne LB _ _ ND0 XIN INc NE_x_c) as ID_x_c.
    pose proof (nodup_ids_ne LB _ _ ND0 XIN INe NE_x_e) as ID_x_e.
    cbn [blk_id fst snd] in ID_a_c, ID_a_e, ID_c_e, ID_x_a, ID_x_c, ID_x_e.
    (* [comment removed for export] *)
    pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ _ _ HP INa XIN ltac:(cbn; congruence)) as DJ_a_x. cbn [blk_addr blk_size fst snd] in DJ_a_x.
    pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ _ _ HP INc XIN ltac:(cbn; congruence)) as DJ_c_x. cbn [blk_addr blk_size fst snd] in DJ_c_x.
    pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ _ _ HP INe XIN ltac:(cbn; congruence)) as DJ_e_x. cbn [blk_addr blk_size fst snd] in DJ_e_x.
    (* [comment removed for export] *)
    hide APac; hide APae; hide APce; hide AI; hide CI; hide EI; hide XI; hide DJ_a_x; hide DJ_c_x; hide DJ_e_x.
    set (L1 := hs_lb_remove H (bf_eid R) LB).
    set (L2 := hs_lb_remove H (bf_cid R) L1).
    set (L3 := hs_lb_remove H (bf_id R) L2).
    pose proof (lb_remove_exact H HH (bf_eid R) (bf_enc R) 92 LB ND0 INe) as (_ & _ & IFF1). fold L1 in IFF1.
    assert (INa1 : In (bf_id R, a, 128) L1) by (apply (proj2 (IFF1 _)); split; [exact INa| exact ID_a_e]).
    assert (INc1 : In (bf_cid R, bf_ctx R, 2584) L1) by (apply (proj2 (IFF1 _)); split; [exact INc| exact ID_c_e]).
    assert (INx1 : In (xq, xa, 40) L1) by (apply (proj2 (IFF1 _)); split; [exact XIN| exact ID_x_e]).
    assert (SUB10 : forall b, In b L1 -> In b LB) by (intros b Hb; apply (proj1 (IFF1 b)); exact Hb).
    unfold METH_b64, O_METH_BREAD in METH.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply bf_seg1 with (lo := lo) (R := R) (hdr := hdr) (junk := junk) (elen := elen);
      try first [exact A0| exact A1| exact SLOT| exact RA| exact RC| exact BA| exact LH| exact LJ| exact CTX0| exact ST| exact CEIL| exact MI];
      try (unfold METH_b64, O_METH_BREAD; exact METH)|].
    all: try (unhide APac; unfold BIO_SIZE, B64CTX_SIZE; lia).
    intros ms1 (m1 & -> & MU1 & WM1 & MI1 & ST1 & BA1 & CTX1 & METH1 & SL1 & F11 & F21). unfold METH_b64, O_METH_BREAD in METH1.
    unhide AI; unhide EI.
    assert (HP1 : hs_RHEAP H s LB m1).
    { eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|].
      apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [left; cbn; lia|].
      apply Forall_cons; [right; right; exists (bf_id R, a, 128); split; [exact INa| cbn; lia]| apply Forall_nil]. }
    assert (AUX1 : hs_rauxv_ok H m1 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]. unfold RAUXV_CELL. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
    apply (rw_cells_transport rsegs _ m m1 _ _ ERR) in MU1 as ERR1; [| exact WM1| unfold RERRNO; cbn; lia].
    assert (IM1 : IMPL_mem m1) by (eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]).
    assert (GM1 : GOT_mem m1) by (eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]).
    unhide APae. apply (rw_cells_transport rsegs _ m m1 _ _ CE) in MU1 as CE1; [| exact WM1| cbn; lia]. hide APae.
    (* [comment removed for export] *)
    assert (AG1 : magree (lib_addr [(xq, xa, 40)]) m m1).
    { eapply magree_of_munch; [exact MU1| exact WM1|]. intros q Hq HL. cbn.
      destruct HL as [HL|(b & [<-|[]] & Hr)].
      - unfold LIBX, LIBX0 in HL. cbn [rin_ivs fst snd] in HL. repeat split; lia.
      - cbn [blk_addr blk_size fst snd] in Hr. unhide DJ_a_x. repeat split; lia. }
    hide AI; hide EI.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply (@cfree_null_evt_spec HCEIL) with (lo := lo); rewrite ?unsigned_lit by lia;
      first [exact ST1| exact CEIL| lia| exact MI1| exact IM1| exact GM1]|].
    intros ms2 (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & ST2 & IM2 & GM2).
    rewrite (unsigned_lit (bv_unsigned sp + -80)) in MU2, ST2 by lia.
    unhide AI; unhide CI; unhide EI; unhide XI.
    assert (HP2 : hs_RHEAP H s LB m2).
    { eapply (HH_RHEAP_frame H HH); [exact HP1| exact MU2| exact WM2|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (AUX2 : hs_rauxv_ok H m2 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX1| exact MU2| exact WM2|]. unfold RAUXV_CELL. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
    apply (rw_cells_transport rsegs _ m1 m2 _ _ ERR1) in MU2 as ERR2; [| exact WM2| unfold RERRNO; cbn; lia].
    apply (rw_cells_transport rsegs _ m1 m2 _ _ BA1) in MU2 as BA2; [| exact WM2| cbn; lia].
    apply (rw_cells_transport rsegs _ m1 m2 _ _ CTX1) in MU2 as CTX2; [| exact WM2| cbn; lia].
    apply (rw_cells_transport rsegs _ m1 m2 _ _ METH1) in MU2 as METH2; [| exact WM2| unfold A_b64_method; cbn; lia].
    apply (rw_cells_transport rsegs _ m1 m2 _ _ SL1) in MU2 as SL2; [| exact WM2| cbn; lia].
    apply (rw_cells_transport rsegs _ m1 m2 _ _ F11) in MU2 as F12; [| exact WM2| cbn; lia].
    apply (rw_cells_transport rsegs _ m1 m2 _ _ F21) in MU2 as F22; [| exact WM2| cbn; lia].
    apply (rw_cells_transport rsegs _ m1 m2 _ _ CE1) in MU2 as CE2; [| exact WM2| cbn; lia].
    assert (AG2 : magree (lib_addr [(xq, xa, 40)]) m1 m2).
    { eapply magree_of_munch; [exact MU2| exact WM2|]. intros q Hq HL. cbn.
      destruct HL as [HL|(b & [<-|[]] & Hr)].
      - unfold LIBX, LIBX0 in HL. cbn [rin_ivs fst snd] in HL. repeat split; lia.
      - cbn [blk_addr blk_size fst snd] in Hr. repeat split; lia. }
    hide AI; hide CI; hide EI; hide XI.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply bf_seg2 with (lo := lo) (R := R) (hdr := hdr) (junk := junk) (elen := elen); first [exact RC| exact ENR| exact LH| exact LJ| exact ELR| exact CTX2| exact ST2| exact CEIL| lia| exact MI2]|].
    intros ms3 (m3 & -> & MU3 & WM3 & MI3 & ST3 & CTX3).
    unhide AI; unhide CI; unhide EI; unhide XI; unhide APac; unhide APce.
    assert (HP3 : hs_RHEAP H s LB m3).
    { eapply (HH_RHEAP_frame H HH); [exact HP2| exact MU3| exact WM3|].
      apply Forall_cons; [right; right; exists (bf_cid R, bf_ctx R, 2584); split; [exact INc| cbn; lia]| apply Forall_nil]. }
    assert (AUX3 : hs_rauxv_ok H m3 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX2| exact MU3| exact WM3|]. unfold RAUXV_CELL. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
    apply (rw_cells_transport rsegs _ m2 m3 _ _ ERR2) in MU3 as ERR3; [| exact WM3| unfold RERRNO; cbn; lia].
    assert (IM3 : IMPL_mem m3) by (eapply IMPL_across; [exact MU3| exact WM3| unfold A_malloc_impl; cbn; lia| exact IM2]).
    assert (GM3 : GOT_mem m3) by (eapply GOT_across; [exact MU3| exact WM3| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM2]).
    apply (rw_cells_transport rsegs _ m2 m3 _ _ BA2) in MU3 as BA3; [| exact WM3| cbn; lia].
    apply (rw_cells_transport rsegs _ m2 m3 _ _ METH2) in MU3 as METH3; [| exact WM3| unfold A_b64_method; cbn; lia].
    apply (rw_cells_transport rsegs _ m2 m3 _ _ SL2) in MU3 as SL3; [| exact WM3| cbn; lia].
    apply (rw_cells_transport rsegs _ m2 m3 _ _ F12) in MU3 as F13; [| exact WM3| cbn; lia].
    apply (rw_cells_transport rsegs _ m2 m3 _ _ F22) in MU3 as F23; [| exact WM3| cbn; lia].
    apply (rw_cells_transport rsegs _ m2 m3 _ _ CE2) in MU3 as CE3; [| exact WM3| cbn; lia].
    assert (AG3 : magree (lib_addr [(xq, xa, 40)]) m2 m3).
    { eapply magree_of_munch; [exact MU3| exact WM3|]. intros q Hq HL. cbn.
      destruct HL as [HL|(b & [<-|[]] & Hr)].
      - unfold LIBX, LIBX0 in HL. cbn [rin_ivs fst snd] in HL. repeat split; lia.
      - cbn [blk_addr blk_size fst snd] in Hr. unhide DJ_c_x. repeat split; lia. }
    hide AI; hide CI; hide EI; hide XI; hide APac; hide APce.
    assert (ENC3 : ENCCTX LB m3 (bf_enc R) d (bf_eid R)).
    { exists raw, line. split; [exact L1e|]. split; [exact L2e|]. split; [exact CE3|]. split; [exact LNE|]. split; [exact INE|]. split; [exact RRE| exact DU]. }
    (* [comment removed for export] *)
    pose proof (encfree_spec H HH) as EF. unfold encfree_stmt in EF.
    eapply (sr_seq H HH).
    { eapply EF with (lo := lo) (B := B) (LB := LB) (s := s) (p := bf_eid R) (a := bf_enc R) (d := d); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact ENC3| exact HP3| exact KREL| exact AUX3| exact ST3| exact CEIL| exact MI3| exact IM3| exact GM3].
      all: lazymatch goal with
           | |- rw_cells _ _ (errno_addr _) _ => rewrite errno_RATP; exact ERR3
           | |- _ mod 2 = 0 => unfold B64FR_RA2; rewrite unsigned_lit by lia; reflexivity
           | |- _ => try (unfold ENCFREE_STACK, FR_EVP_ENCODE_CTX_free, CFREE_STACK, RFREE_STACK; lia); try lia
           end.
      all: match goal with |- ?G => idtac "EF-LEFT:" G end. }
    clear EF. intros [ms4 mo4] PO. unfold encfree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m4 & errv4 & s4' &
                    -> & KREL4 & MP4 & MI4 & ST4 & ERR4 & AUX4 & XP4 & HEAP4 & IM4 & GM4).
    rewrite (unsigned_lit (bv_unsigned sp + -80)) in ST4, XP4 by lia. rewrite errno_RATP in ERR4. fold L1 in XP4, HEAP4.
    pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ HEAP4) as ND1.
    pose proof (lb_remove_exact H HH (bf_cid R) (bf_ctx R) 2584 L1 ND1 INc1) as (_ & _ & IFF2). fold L2 in IFF2.
    assert (INa2 : In (bf_id R, a, 128) L2) by (apply (proj2 (IFF2 _)); split; [exact INa1| exact ID_a_c]).
    assert (INx2 : In (xq, xa, 40) L2) by (apply (proj2 (IFF2 _)); split; [exact INx1| exact ID_x_c]).
    assert (SUB21 : forall b, In b L2 -> In b L1) by (intros b Hb; apply (proj1 (IFF2 b)); exact Hb).
    unhide AI.
    assert (BA4 : rw_cells rsegs m4 a (bio_cells (mkBIO A_b64_method 1 1 (bf_flags R) (bf_retry R) 0 (bf_ctx R) (bf_next R) (bf_prev R) 0 (bf_nread R) 0))).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP4); [exact BA3| right; right; exists (bf_id R, a, 128); split; [exact INa1| cbn; lia]| apply Forall_nil]. }
    hide AI.
    assert (F24 : rw_cells rsegs m4 (bv_unsigned sp + -80) [C8 s4; C8 s3; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 a); C8 sp; C8 (Z_to_bv 64 BFI_RA1)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP4); [exact F23| left; cbn; lia| apply Forall_nil]. }
    assert (F14 : rw_cells rsegs m4 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP4); [exact F13| left; cbn; lia| apply Forall_nil]. }
    assert (SL4 : rw_cells rsegs m4 rbp [C4 (wz 0)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP4); [exact SL3| left; cbn; lia| apply Forall_nil]. }
    assert (METH4 : rw_cells rsegs m4 (A_b64_method + 32)
      [C8 (wz P_bread_conv); C8 (wz P_b64_read); C8 (wz P_b64_puts); C8 (wz 0); C8 (wz P_b64_ctrl); C8 (wz P_b64_new); C8 (wz P_b64_free); C8 (wz P_b64_callback_ctrl)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP4); [exact METH3| static_tac| apply Forall_nil]. }
    assert (AG4 : magree (lib_addr [(xq, xa, 40)]) m3 m4).
    { eapply magree_mono; [eapply magree_lib_of_xpres_fr; exact XP4|]. intros q HL. split; [| cbn; tauto].
      destruct HL as [HL|(b & [<-|[]] & Hr)]; [left; exact HL| right]. exists (xq, xa, 40). split; [exact INx1| exact Hr]. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL4| eapply bf_seg3; exact MI4|].
    intros ms5 ->.
    (* [comment removed for export] *)
    pose proof (cfree_spec H HH) as CF. unfold cfree_stmt in CF.
    eapply (sr_seq H HH).
    { eapply CF with (lo := lo) (B := B) (LB := L1) (s := s4') (p := bf_cid R) (A := bf_ctx R) (n := 2584); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact HEAP4| exact KREL4| exact INc1| exact AUX4| exact ST4| exact CEIL| exact MI4| exact IM4| exact GM4].
      all: lazymatch goal with
           | |- rw_cells _ _ (errno_addr _) _ => rewrite errno_RATP; exact ERR4
           | |- _ => try (unfold CFREE_STACK, RFREE_STACK; lia); try lia
           end.
      all: match goal with |- ?G => idtac "CF1-LEFT:" G end. }
    intros [ms6 mo6] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m6 & s6' &
                    -> & KREL6 & MP6 & MI6 & ST6 & ERR6 & AUX6 & XP6 & HEAP6 & IM6 & GM6).
    rewrite (unsigned_lit (bv_unsigned sp + -80)) in ST6, XP6 by lia. rewrite errno_RATP in ERR6. fold L2 in XP6, HEAP6.
    pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ HEAP6) as ND2.
    pose proof (lb_remove_exact H HH (bf_id R) a 128 L2 ND2 INa2) as (_ & _ & IFF3). fold L3 in IFF3.
    assert (SUB32 : forall b, In b L3 -> In b L2) by (intros b Hb; apply (proj1 (IFF3 b)); exact Hb).
    unhide AI.
    assert (BA6 : rw_cells rsegs m6 a (bio_cells (mkBIO A_b64_method 1 1 (bf_flags R) (bf_retry R) 0 (bf_ctx R) (bf_next R) (bf_prev R) 0 (bf_nread R) 0))).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP6); [exact BA4| right; right; exists (bf_id R, a, 128); split; [exact INa2| cbn; lia]| apply Forall_nil]. }
    hide AI.
    assert (F26 : rw_cells rsegs m6 (bv_unsigned sp + -80) [C8 s4; C8 s3; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 a); C8 sp; C8 (Z_to_bv 64 BFI_RA1)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP6); [exact F24| left; cbn; lia| apply Forall_nil]. }
    assert (F16 : rw_cells rsegs m6 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP6); [exact F14| left; cbn; lia| apply Forall_nil]. }
    assert (SL6 : rw_cells rsegs m6 rbp [C4 (wz 0)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP6); [exact SL4| left; cbn; lia| apply Forall_nil]. }
    assert (METH6 : rw_cells rsegs m6 (A_b64_method + 32)
      [C8 (wz P_bread_conv); C8 (wz P_b64_read); C8 (wz P_b64_puts); C8 (wz 0); C8 (wz P_b64_ctrl); C8 (wz P_b64_new); C8 (wz P_b64_free); C8 (wz P_b64_callback_ctrl)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP6); [exact METH4| static_tac| apply Forall_nil]. }
    assert (AG6 : magree (lib_addr [(xq, xa, 40)]) m4 m6).
    { eapply magree_mono; [eapply magree_lib_of_xpres_fr; exact XP6|]. intros q HL. split; [| cbn; tauto].
      destruct HL as [HL|(b & [<-|[]] & Hr)]; [left; exact HL| right]. exists (xq, xa, 40). split; [exact INx2| exact Hr]. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL6| eapply bf_seg4 with (lo := lo) (a := a) (fl := bf_flags R) (rt := bf_retry R) (ctx := bf_ctx R) (nx := bf_next R) (pv := bf_prev R) (nr := bf_nread R);
      first [exact RA| exact FLR| exact RTR| exact CXR| exact NXR| exact PVR| exact NRR| exact BA6| exact F26| exact ST6| exact CEIL| lia| exact MI6]|].
    intros ms7 (m7 & -> & MU7 & WM7 & MI7 & ST7 & BA7).
    unhide AI; unhide XI.
    assert (HEAP7 : hs_RHEAP H s6' L2 m7).
    { eapply (HH_RHEAP_frame H HH); [exact HEAP6| exact MU7| exact WM7|].
      apply Forall_cons; [left; cbn; lia|].
      apply Forall_cons; [right; right; exists (bf_id R, a, 128); split; [exact INa2| cbn; lia]|].
      apply Forall_cons; [right; right; exists (bf_id R, a, 128); split; [exact INa2| cbn; lia]| apply Forall_nil]. }
    assert (AUX7 : hs_rauxv_ok H m7 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX6| exact MU7| exact WM7|]. unfold RAUXV_CELL. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
    apply (rw_cells_transport rsegs _ m6 m7 _ _ ERR6) in MU7 as ERR7; [| exact WM7| unfold RERRNO; cbn; lia].
    assert (IM7 : IMPL_mem m7) by (eapply IMPL_across; [exact MU7| exact WM7| unfold A_malloc_impl; cbn; lia| exact IM6]).
    assert (GM7 : GOT_mem m7) by (eapply GOT_across; [exact MU7| exact WM7| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM6]).
    apply (rw_cells_transport rsegs _ m6 m7 _ _ F16) in MU7 as F17; [| exact WM7| cbn; lia].
    apply (rw_cells_transport rsegs _ m6 m7 _ _ SL6) in MU7 as SL7; [| exact WM7| cbn; lia].
    apply (rw_cells_transport rsegs _ m6 m7 _ _ METH6) in MU7 as METH7; [| exact WM7| unfold A_b64_method; cbn; lia].
    assert (AG7 : magree (lib_addr [(xq, xa, 40)]) m6 m7).
    { eapply magree_of_munch; [exact MU7| exact WM7|]. intros q Hq HL. cbn.
      destruct HL as [HL|(b & [<-|[]] & Hr)].
      - unfold LIBX, LIBX0 in HL. cbn [rin_ivs fst snd] in HL. repeat split; lia.
      - cbn [blk_addr blk_size fst snd] in Hr. unhide DJ_a_x. repeat split; lia. }
    hide AI; hide XI.
    destruct (bio_cells_split_ex _ _ _ BA7) as [_ EXD7].
    pose proof (magree_trans _ _ _ _ AG1 (magree_trans _ _ _ _ AG2 (magree_trans _ _ _ _ AG3 (magree_trans _ _ _ _ AG4 (magree_trans _ _ _ _ AG6 AG7))))) as AG07.
    assert (CS7 : CTX_statics m7 x) by (eapply (CTX_statics_frame [(xq, xa, 40)]); [exact CS| exact AG07]).
    assert (EX7 : EXLOCK L2 m7 (xq, xa, 40)).
    { assert (EX0 : EXLOCK [(xq, xa, 40)] m (xq, xa, 40)) by (split; [left; reflexivity| exact (proj2 EX)]).
      pose proof (EXLOCK_frame _ _ _ _ EX0 AG07) as [_ K]. split; [exact INx2| exact K]. }
    (* [comment removed for export] *)
    pose proof (@cfreeex_spec HCEIL) as CX. unfold cfreeex_stmt in CX. cbv zeta in CX.
    eapply (sr_evt_krel H HH).
    { exact KREL6. }
    { eapply CX with (lo := lo) (LB := L2) (x := x) (obj := a) (ad := a + O_BIO_EXDATA); rewrite ?EXB; cbn [blk_addr blk_size fst snd];
        rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact EXD7| exact CS7| exact EX7| exact ST7| exact CEIL| exact MI7| exact IM7| exact GM7].
      all: lazymatch goal with
           | |- off_image _ _ => unhide AI; unfold off_image, IMG_LO, IMG_HI, O_BIO_EXDATA; lia
           | |- _ mod 2 = 0 => unfold BFI_RA2; rewrite unsigned_lit by lia; reflexivity
           | |- _ \/ _ => unhide DJ_a_x; unfold O_BIO_EXDATA, MUTEX_SIZE; lia
           | |- context [CFREEEX_STACK] => unfold CFREEEX_STACK, FR_CRYPTO_free_ex_data, GETGLOBAL_READY_STACK, NEWEX_INNER, GETANDLOCK_STACK, FR_get_and_lock, CRWLOCK_STACK, CUNLOCK_STACK,
                             FR_mutex_unlock, FR_pthread_mutex_unlock, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock, FR_ossl_lib_ctx_get_ex_data_global, GETDEFCTX_STACK, FR_get_default_context; lia
           | |- _ => try (unfold O_BIO_EXDATA; lia)
           end.
      all: match goal with |- ?G => idtac "CX-LEFT:" G end. }
    clear CX. intros ms8 PO. unfold c3_post in PO.
    destruct PO as (x0 & x1 & x2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & x3 & x4 & x5 & x6 & m8 & -> & -> & MU8 & WM8 & MI8 & ST8 & CS8 & EX8 & EXD8).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in MU8, ST8 by lia. rewrite EXB in MU8. cbn [blk_addr fst snd] in MU8. unfold mutex_foot, O_BIO_EXDATA in MU8.
    unhide AI; unhide XI.
    assert (HEAP8 : hs_RHEAP H s6' L2 m8).
    { eapply (HH_RHEAP_frame H HH); [exact HEAP7| exact MU8| exact WM8|].
      apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; right; exists (bf_id R, a, 128); split; [exact INa2| cbn; lia]|].
      apply Forall_cons; [right; right; exists (xq, xa, 40); split; [exact INx2| cbn; lia]| apply Forall_nil]. }
    assert (AUX8 : hs_rauxv_ok H m8 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX7| exact MU8| exact WM8|]. unfold RAUXV_CELL. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
    apply (rw_cells_transport rsegs _ m7 m8 _ _ ERR7) in MU8 as ERR8; [| exact WM8| unfold RERRNO; cbn; lia].
    assert (IM8 : IMPL_mem m8) by (eapply IMPL_across; [exact MU8| exact WM8| unfold A_malloc_impl; cbn; lia| exact IM7]).
    assert (GM8 : GOT_mem m8) by (eapply GOT_across; [exact MU8| exact WM8| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM7]).
    apply (rw_cells_transport rsegs _ m7 m8 _ _ F17) in MU8 as F18; [| exact WM8| cbn; lia].
    apply (rw_cells_transport rsegs _ m7 m8 _ _ SL7) in MU8 as SL8; [| exact WM8| cbn; lia].
    apply (rw_cells_transport rsegs _ m7 m8 _ _ METH7) in MU8 as METH8; [| exact WM8| unfold A_b64_method; cbn; lia].
    hide AI; hide XI.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL6| eapply fr_seg5; exact MI8|].
    intros ms9 ->.
    (* [comment removed for export] *)
    eapply (sr_seq H HH).
    { eapply CF with (lo := lo) (B := B) (LB := L2) (s := s6') (p := bf_id R) (A := a) (n := 128); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact HEAP8| exact KREL6| exact INa2| exact AUX8| exact ST8| exact CEIL| exact MI8| exact IM8| exact GM8].
      all: lazymatch goal with
           | |- rw_cells _ _ (errno_addr _) _ => rewrite errno_RATP; exact ERR8
           | |- _ => try (unfold CFREE_STACK, RFREE_STACK; lia); try lia
           end.
      all: match goal with |- ?G => idtac "CF2-LEFT:" G end. }
    clear CF. intros [ms10 mo10] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (y0 & y1 & y2 & f0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & y3 & y4 & y5 & y6 & m10 & s10' &
                    -> & KREL10 & MP10 & MI10 & ST10 & ERR10 & AUX10 & XP10 & HEAP10 & IM10 & GM10).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST10, XP10 by lia. rewrite errno_RATP in ERR10. fold L3 in XP10, HEAP10.
    assert (F1_10 : rw_cells rsegs m10 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP10); [exact F18| left; cbn; lia| apply Forall_nil]. }
    assert (SL10 : rw_cells rsegs m10 rbp [C4 (wz 0)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP10); [exact SL8| left; cbn; lia| apply Forall_nil]. }
    assert (METH10 : rw_cells rsegs m10 (A_b64_method + 32)
      [C8 (wz P_bread_conv); C8 (wz P_b64_read); C8 (wz P_b64_puts); C8 (wz 0); C8 (wz P_b64_ctrl); C8 (wz P_b64_new); C8 (wz P_b64_free); C8 (wz P_b64_callback_ctrl)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP10); [exact METH8| static_tac| apply Forall_nil]. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL10| eapply fi_seg6 with (lo := lo); [exact F1_10| exact ST10| exact CEIL| lia| exact MI10| exact RAE]|].
    intros ms11 [-> ST10'].
    apply (sr_done H HH). unfold biofreeint_b64_post. cbn [cfg_ms cfg_model].
    exists y0, y1, y2, f1, f2, f3, f4, f5, f6, f7, y3, y4, y5, y6, m10, errv4, s10', L3.
    split; [reflexivity|]. split; [exact KREL10|].
    split; [eapply (mpres_trans H HH); [exact MP4| eapply (mpres_trans H HH); [exact MP6| exact MP10]]|].
    split; [exact MI10|]. split; [exact ST10'|]. split; [rewrite errno_RATP; exact ERR10|]. split; [exact AUX10|]. split; [exact HEAP10|].
    split.
    { (* [comment removed for export] *)
      unfold blocks_B64F, BIO_SIZE, B64CTX_SIZE. cbn [app].
      apply Permutation_sym.
      eapply Permutation_trans; [| exact (lb_remove_perm H HH _ _ _ _ _ _ HP3 INe)]. fold L1.
      eapply Permutation_trans; [| apply perm_skip; exact (lb_remove_perm H HH _ _ _ _ _ _ HEAP4 INc1)]. fold L2.
      eapply Permutation_trans; [| apply perm_skip; apply perm_skip; exact (lb_remove_perm H HH _ _ _ _ _ _ HEAP8 INa2)]. fold L3.
      apply perm3_rev. }
    split; [exact IM10|]. split; [exact GM10|]. split; [unfold METH_b64, O_METH_BREAD; exact METH10|]. split; [exact SL10|].
    (* [comment removed for export] *)
    assert (HL3 : forall b, In b L3 -> In b LB /\ (forall hb, In hb [(bf_id R, a, 128); (bf_cid R, bf_ctx R, 2584)] -> blk_id b <> blk_id hb)).
    { intros b Hb. destruct (proj1 (IFF3 b) Hb) as [Hb2 NEa]. destruct (proj1 (IFF2 b) Hb2) as [Hb1 NEc]. pose proof (SUB10 _ Hb1) as Hb0.
      split; [exact Hb0|]. intros hb [<-|[<-|[]]]; cbn [blk_id fst snd]; [exact NEa| exact NEc]. }
    unhide AI; unhide CI; unhide XI.
    eapply xpres_trans.
    { eapply (xpres_of_munch_exX H HH s LB m m m1 (bv_unsigned sp)); [exact HP| lia| exact MU1| exact WM1| exact HL3| |].
      - intros hb [<-|[<-|[]]]; [exact INa| exact INc].
      - apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; right; cbn; intros q Hq; lia|].
        apply Forall_cons; [right; left; exists (bf_id R, a, 128); split; [left; reflexivity| cbn; lia]| apply Forall_nil]. }
    eapply xpres_trans.
    { eapply (xpres_of_munch_exX H HH s LB m m1 m2 (bv_unsigned sp)); [exact HP| lia| exact MU2| exact WM2| exact HL3| |].
      - intros hb [<-|[<-|[]]]; [exact INa| exact INc].
      - apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    eapply xpres_trans.
    { eapply (xpres_of_munch_exX H HH s LB m m2 m3 (bv_unsigned sp)); [exact HP| lia| exact MU3| exact WM3| exact HL3| |].
      - intros hb [<-|[<-|[]]]; [exact INa| exact INc].
      - apply Forall_cons; [right; left; exists (bf_cid R, bf_ctx R, 2584); split; [right; left; reflexivity| cbn; lia]| apply Forall_nil]. }
    eapply xpres_trans; [eapply xpres_weaken; [exact XP4| lia| intros b Hb; apply SUB21, SUB32; exact Hb| cbn; tauto]|].
    eapply xpres_trans; [eapply xpres_weaken; [exact XP6| lia| intros b Hb; apply SUB32; exact Hb| cbn; tauto]|].
    eapply xpres_trans.
    { eapply (xpres_of_munch_exX H HH s LB m m6 m7 (bv_unsigned sp)); [exact HP| lia| exact MU7| exact WM7| exact HL3| |].
      - intros hb [<-|[<-|[]]]; [exact INa| exact INc].
      - apply Forall_cons; [left; cbn; lia|].
        apply Forall_cons; [right; left; exists (bf_id R, a, 128); split; [left; reflexivity| cbn; lia]|].
        apply Forall_cons; [right; left; exists (bf_id R, a, 128); split; [left; reflexivity| cbn; lia]| apply Forall_nil]. }
    eapply xpres_trans; [| eapply xpres_weaken; [exact XP10| lia| auto| cbn; tauto]].
    eapply xpres_of_munch_eq; [exact MU8| exact WM8|].
    intros q Hq [QC _]. cbn [outside].
    assert (CASE : (xa + 4 <= q < xa + 8) \/ ~ (xa + 4 <= q < xa + 8)) by lia.
    destruct CASE as [INX|OUTX].
    - right. unfold EXLOCK, MUTEX in EX7, EX8. rewrite EXB in EX8. cbn [blk_addr blk_size fst snd] in EX7, EX8.
      destruct EX7 as (_ & _ & _ & XM7). destruct EX8 as (_ & _ & _ & XM8).
      eapply (rw_cells_same_raw m7 m8); [exact XM7| exact XM8| cbn; lia| cbn; lia].
    - left. destruct QC as [K|[[[K1 K2] _]|(b & Hb & Hr)]]; [repeat split; lia| repeat split; lia|].
      destruct (HL3 b Hb) as [Hb0 HNE]. pose proof (HB b Hb0) as BLO.
      pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ b (bf_id R, a, 128) HP Hb0 INa (HNE _ (or_introl eq_refl))) as D. cbn [blk_addr blk_size fst snd] in D.
      repeat split; lia.
  Qed.
End W.
