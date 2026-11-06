(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Rep ECH_LibState
     ECH_C1_stmt ECH_C1_malloc ECH_C1_free ECH_C1_freeopt ECH_C5_stmt ECH_C5_popfree ECH_C13_stmt.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.

  Definition XF_RA : Z := 0x26c080.
  Definition XF_T1 : Z := 0xdf0a0.
  Definition VPM_FILE : Z := 0x364d2.
  Definition xf_frame (s2 s1 s0 ra : word) : list cell := [C8 s2; C8 s1; C8 s0; C8 ra].

  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  (* [comment removed for export] *)
  Lemma xf_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a lo : Z) (E : extrep) (pad : list byte),
      rw_cells rsegs m a (ext_cells E pad) -> 0 < a -> a + EXT_SIZE <= lo -> 0 <= ex_val E < 2^64 ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 XF_RA) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 a)
                       (Z_to_bv 64 (ex_val E)) (Z_to_bv 64 VPM_FILE) (Z_to_bv 64 60) a3 a4 a5 a6 a7
                       (Z_to_bv 64 VPM_FILE) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m1 (seg_rom rsegs)
          /\ munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ stk rsegs m1 lo (bv_unsigned sp + -32)
          /\ rw_cells rsegs m1 (bv_unsigned sp + -32) (xf_frame s2 s1 s0 ra)
          /\ rw_cells rsegs m1 a (ext_cells E pad))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_ossl_echext_free) fc None m (seg_rom rsegs)).
  Proof.
    intros until pad. intros HDR POS BL DR ST CEIL LO MI. unfold P_ossl_echext_free, P_CRYPTO_free, XF_RA, VPM_FILE.
    unfold ext_cells, wz in HDR. unfold EXT_SIZE in *.
    pose proof (rw_cells_bound _ _ _ _ HDR) as HB. cbn [cells_size csize Nat.add] in HB.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    carve_frame 32%nat ST.
    do 7 step. st1. do 6 step. finish.
    all: unfold ext_cells, wz; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma xf_seg2 :
    forall (sp gp tp t0 t1 t2 s0x a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a : Z),
      rw_cells rsegs m (bv_unsigned sp + -32) (xf_frame s2 s1 s0 ra) -> mem_inv rsegs m ->
      evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 XF_T1) t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 VPM_FILE) (Z_to_bv 64 61) a3 a4 a5 a6 a7
                                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom rsegs))
        (MS (mkR (Z_to_bv 64 XF_RA) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0x (Z_to_bv 64 a) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 VPM_FILE) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 XF_RA)) fc None m (seg_rom rsegs)).
  Proof.
    intros until a. intros FR MI. unfold XF_RA, XF_T1, VPM_FILE, P_CRYPTO_free.
    replace (ret_pc (Z_to_bv 64 0x26c080)) with (Z_to_bv 64 0x26c080) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR. unfold xf_frame in FR.
    do 10 step. apply evt_done. reflexivity.
  Qed.
End S.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.

  (* [comment removed for export] *)
  Lemma EXTobj_frame_law : EXTobj_frame.
  Proof.
    unfold EXTobj_frame, EP_frame. intros LB LB' m m' p x SP ((pad & PL & HC) & HIN & OF) KEEP XP BEL.
    unfold EXTobj. split; [| split; [apply KEEP; left; reflexivity|]].
    - exists pad. split; [exact PL|]. eapply xpres_rw_cells'; [exact XP| exact HC| | constructor].
      right; right. exists (ex_id x, p, EXT_SIZE). split; [apply KEEP; left; reflexivity|]. unfold ext_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold EXT_SIZE. lia.
    - revert OF KEEP. unfold blocks_EXT. destruct (ex_val_o x) as [[vid vn]|]; cbn [ofield blocks_of]; intros OF KEEP; [| exact OF].
      destruct OF as (O1 & O2 & O3). split; [exact O1|]. split; [exact O2|]. apply KEEP. right. left. reflexivity.
  Qed.

  Lemma EXTobj_owned_law : EP_owned extrep EXTobj blocks_EXT.
  Proof.
    unfold EP_owned. intros LB m p x (HC & HIN & OF) b Hb.
    unfold blocks_EXT in Hb. destruct Hb as [<-|Hb]; [exact HIN|].
    revert OF Hb. destruct (ex_val_o x) as [[vid vn]|]; cbn [blocks_of ofield]; intros OF Hb; [| destruct Hb].
    destruct Hb as [<-|[]]. destruct OF as (_ & _ & O3). exact O3.
  Qed.

  Lemma GOT_echfree_frame : G_frame GOT_echfree.
  Proof.
    unfold G_frame, GOT_echfree. intros LB SP m m' GM XP CE. hcb.
    eapply xpres_rw_cells'; [exact XP| exact GM| | constructor].
    right; left. unfold A_got_ossl_echext_free, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK. cbn. lia.
  Qed.

  Lemma GOT_echfree_across : forall W m m1,
    munch W m m1 -> wmono rsegs m m1 -> disjoint_from W A_got_ossl_echext_free 16 -> GOT_echfree m -> GOT_echfree m1.
  Proof. intros W m m1 MU WM DJ GM. eapply rw_cells_transport; [exact GM| exact MU| exact WM| exact DJ]. Qed.
  Lemma GOT_echfree_xpres : forall LB SP X m m1,
    xpres LB SP X m m1 -> Forall (fun iv : Z * Z => A_got_ossl_echext_free + 16 <= fst iv \/ snd iv <= A_got_ossl_echext_free) X ->
    GOT_echfree m -> GOT_echfree m1.
  Proof.
    intros LB SP X m m1 XP FX GM. hcb. eapply xpres_rw_cells'; [exact XP| exact GM| | exact FX].
    right; left. unfold A_got_ossl_echext_free, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK. cbn. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma extfree_spec : extfree_stmt H.
  Proof.
    unfold extfree_stmt, efree_stmt_at. intros until errv.
    intros A0 XO ND HP KREL AUX SPB ST CEIL LO ERR MI TP IM GM GG RAE. subst a0.
    unfold EXTFREE_STACK, FR_ossl_echext_free, CFREE_STACK, RFREE_STACK in LO.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    pose proof XO as XO'. destruct XO' as ((pad & PL & HC) & HIN & OF).
    pose proof (HB _ HIN) as ABL. cbn [blk_addr blk_size fst snd] in ABL. unfold EXT_SIZE in ABL.
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP HIN) as BRA. cbn [blk_addr blk_size fst snd] in BRA. destruct BRA as (POS & _).
    assert (SUBL : forall q L b, In b (hs_lb_remove H q L) -> In b L) by (intros q L b Hb; eapply (proj2 (proj2 (HH_lb_remove H HH))); exact Hb).
    assert (DR : 0 <= ex_val x < 2^64).
    { clear - OF HB HCEILB. revert OF. destruct (ex_val_o x) as [[vid vn]|]; cbn [ofield]; intros OF; [| lia]. destruct OF as (O1 & O2 & O3). pose proof (HB _ O3) as VBL. cbn [blk_addr blk_size fst snd] in VBL. lia. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply xf_seg1 with (lo := lo); [exact HC| exact POS| unfold EXT_SIZE; lia| exact DR| exact ST| exact CEIL| lia| exact MI]|].
    intros ms1 (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & HC1).
    assert (HP1 : hs_RHEAP H s LB m1).
    { eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (AUX1 : hs_rauxv_ok H m1 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]. unfold RAUXV_CELL. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    subst tp. rewrite errno_RATP in ERR.
    apply (rw_cells_transport rsegs _ m m1 _ _ ERR) in MU1 as ERR1; [| exact WM1| unfold RERRNO; cbn; lia].
    assert (IM1 : IMPL_mem m1) by (eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]).
    assert (GM1 : GOT_mem m1) by (eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]).
    assert (GG1 : GOT_echfree m1) by (eapply GOT_echfree_across; [exact MU1| exact WM1| unfold A_got_ossl_echext_free; cbn; lia| exact GG]).
    assert (XP1 : xpres LB (bv_unsigned sp) [] m m1).
    { eapply xpres_of_munch; [exact MU1| exact WM1| | exact HB]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    (* [comment removed for export] *)
    pose proof (cfree_opt_spec H HH) as CF.
    eapply (sr_seq H HH).
    { eapply CF with (lo := lo) (B := B) (LB := LB) (s := s) (P := ex_val x) (o := ex_val_o x); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact HP1| exact KREL| exact AUX1| exact ST1| exact CEIL| exact MI1| exact IM1| exact GM1].
      all: try first [unfold CFREE_STACK, RFREE_STACK; lia | rewrite errno_RATP; exact ERR1].
      clear - OF. revert OF. destruct (ex_val_o x) as [[vid vn]|]; cbn [ofield]; intros OF; [| exact OF]. destruct OF as (_ & _ & O3). exact O3. }
    clear CF. intros [ms2 mo2] PO. unfold cfree_opt_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & s2' & LB2 &
                    -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & PERM2 & SUB2 & XP2 & HEAP2 & IM2 & GM2).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST2, XP2 by lia. rewrite errno_RATP in ERR2.
    assert (HIN2 : In (ex_id x, p, EXT_SIZE) LB2).
    { eapply perm_in_rest; [exact PERM2| exact HIN|]. clear - ND. unfold blocks_EXT in ND. intros Kb.
      revert ND Kb. destruct (ex_val_o x) as [[vid vn]|]; cbn [blocks_of map app]; intros ND Kb; [| destruct Kb]. destruct Kb as [Kb|[]].
      inversion ND as [|i l NI ND']; subst. apply NI. left. rewrite <- Kb. reflexivity. }
    assert (HB2 := HH_blocks_below H HH _ _ _ HEAP2).
    assert (GG2 : GOT_echfree m2) by (eapply GOT_echfree_xpres; [exact XP2| constructor| exact GG1]).
    assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -32) (xf_frame s2 s1 s0 ra)).
    { eapply xpres_rw_cells'; [exact XP2| exact FR1| left; cbn; lia| constructor]. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL2| eapply xf_seg2; [exact FR2| exact MI2]|].
    intros ms3 ->.
    (* [comment removed for export] *)
    unfold xf_frame in FR2.
    pose proof (stk_release rsegs m2 lo _ _ ST2 FR2 ltac:(lia)) as ST3. cbn [cells_size csize Nat.add] in ST3.
    replace (bv_unsigned sp + -32 + Z.of_nat 32) with (bv_unsigned sp) in ST3 by lia.
    pose proof (cfree_spec H HH) as CF. unfold cfree_stmt in CF.
    eapply (sr_mono H HH).
    { eapply CF with (lo := lo) (B := B) (LB := LB2) (s := s2') (p := ex_id x) (n := EXT_SIZE); try reflexivity.
      all: try first [exact HEAP2| exact KREL2| exact HIN2| exact AUX2| exact SPB| exact ST3| exact CEIL| exact MI2| exact IM2| exact GM2| exact RAE].
      all: first [unfold CFREE_STACK, RFREE_STACK; lia | rewrite errno_RATP; exact ERR2]. }
    intros [ms4 mo4] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m4 & s4' &
                    -> & KREL4 & MP4 & MI4 & ST4 & ERR4 & AUX4 & XP4 & HEAP4 & IM4 & GM4).
    rewrite errno_RATP in ERR4.
    unfold efree_post. cbn [cfg_ms cfg_model].
    exists v0, v1, v2, c0, c1, c2, c3, c4, c5, c6, c7, v3, v4, v5, v6, m4, s4', (hs_lb_remove H (ex_id x) LB2).
    split; [reflexivity|]. split; [exact KREL4|]. split; [eapply (mpres_trans H HH); [exact MP2| exact MP4]|]. split; [exact MI4|]. split; [exact ST4|].
    split; [rewrite errno_RATP; exact ERR4|]. split; [exact AUX4|].
    split.
    { unfold blocks_EXT. cbn [app]. eapply Permutation_trans; [| exact PERM2].
      eapply Permutation_trans; [apply Permutation_middle|]. apply Permutation_app_head.
      eapply (lb_remove_perm H HH); [exact HEAP2| exact HIN2]. }
    split; [exact HEAP4|].
    split.
    { eapply xpres_trans; [| eapply xpres_trans; [| exact XP4]].
      - eapply xpres_weaken; [exact XP1| lia| intros b Hb; apply SUB2; eapply SUBL; exact Hb| auto].
      - eapply xpres_weaken; [exact XP2| lia| intros b Hb; eapply SUBL; exact Hb| auto]. }
    split; [exact IM4|]. split; [exact GM4|].
    eapply GOT_echfree_xpres; [exact XP4| constructor| exact GG2].
  Qed.

  (* [comment removed for export] *)
  Lemma popfree_exts_spec : popfree_exts_stmt H.
  Proof. unfold popfree_exts_stmt. apply (skpopfree_spec H HH). Qed.
End W.
