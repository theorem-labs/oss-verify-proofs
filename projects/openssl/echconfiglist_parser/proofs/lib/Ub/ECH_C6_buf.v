(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Rep ECH_LibState ECH_C1_stmt ECH_C1_malloc ECH_C1_free ECH_C6_stmt ECH_UbKit.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From Stdlib Require Import Sorting.Permutation.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.
  Definition BUF_FILE : Z := 0x11d48.        (* [comment removed for export] *)
  Definition BN_RA : Z := 0x115cd4.   (* [comment removed for export] *)
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  Lemma buf_zero_recut : forall m A, rw_cells usegs m A [CB (Z.to_nat 32) (zeros (Z.to_nat 32))] -> rw_cells usegs m A (buf_cells (mkBUF 0 0 0 0)).
  Proof. intros m A HB. eapply rw_cells_recut; [exact HB| vm_compute; repeat split; reflexivity| vm_compute; reflexivity]. Qed.

  (* [comment removed for export] *)
  Lemma bn_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1 j,
          ms' = MS (mkR (Z_to_bv 64 BN_RA) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 0)
                       (Z_to_bv 64 32) (Z_to_bv 64 BUF_FILE) (Z_to_bv 64 35) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_zalloc) fc None m1 (seg_rom usegs)
          /\ munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (bv_unsigned sp + -32)
          /\ rw_cells usegs m1 (bv_unsigned sp + -32) (cz_frame j s1 s0 ra))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BUF_MEM_new) fc None m (seg_rom usegs)).
  Proof.
    intros until lo. intros ST CEIL LO MI. hcb. unfold P_BUF_MEM_new, P_CRYPTO_zalloc, BN_RA, BUF_FILE.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 32%nat ST.
    do 11 step. finish. exact FR.
  Qed.

  (* [comment removed for export] *)
  Lemma bn_seg2 :
    forall (sp gp tp t0 t1 t2 s0x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A : Z) (j : list byte),
      0 < A -> A + 32 <= bv_unsigned sp + -32 -> A mod 16 = 0 ->   (* [comment removed for export] *)
      rw_cells usegs m A (buf_cells (mkBUF 0 0 0 0)) ->
      rw_cells usegs m (bv_unsigned sp + -32) (cz_frame j s1 s0 ra) -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1,
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 0) (* [comment removed for export] *) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m1 (seg_rom usegs)
          /\ munch [(A, A + 32)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ rw_cells usegs m1 A (buf_cells (mkBUF 0 0 0 0)))
        (MS (mkR (Z_to_bv 64 BN_RA) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0x (Z_to_bv 64 0) (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 BN_RA)) fc None m (seg_rom usegs)).
  Proof.
    intros until j. intros HA HS AL BLK FR MI. unfold BN_RA.
    replace (ret_pc (Z_to_bv 64 0x115cd4)) with (Z_to_bv 64 0x115cd4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR. unfold buf_cells, wz in BLK. cbn [bm_len bm_data bm_max bm_flags] in BLK. unfold cz_frame in FR.
    pose proof (munch_refl [(A, A + 32)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    step. ubal_by AL. step. if_lit.   (* [comment removed for export] *)
    st1. do 5 step. finish.
  Qed.

  Definition BF_FILE_RA : Z := 0x115da0.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma bf_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a lo len mx fl : Z),
      rw_cells usegs m a (buf_cells (mkBUF len 0 mx fl)) -> 0 < a -> a mod 16 = 0 (* [comment removed for export] *) -> a + 32 <= lo -> 0 <= len < 2^64 -> 0 <= mx < 2^64 -> 0 <= fl < 2^64 ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1,
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 BUF_FILE) (Z_to_bv 64 51) a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m1 (seg_rom usegs)
          /\ munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (bv_unsigned sp)
          /\ rw_cells usegs m1 a (buf_cells (mkBUF len 0 mx fl)))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BUF_MEM_free) fc None m (seg_rom usegs)).
  Proof.
    intros until fl. intros BC POS AL BL LR MR FLR ST CEIL LO MI. unfold P_BUF_MEM_free, P_CRYPTO_free, BUF_FILE.
    unfold buf_cells, wz in BC. cbn [bm_len bm_data bm_max bm_flags] in BC.
    pose proof (rw_cells_bound _ _ _ _ BC) as BB. cbn [cells_size csize Nat.add] in BB.
    hcb. pose proof (word_range sp) as SPR. pose proof (word_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    (* [comment removed for export] *)
    carve_frame 32%nat ST.
    do 5 st1. step. if_cases K0; zify_cond K0; [kill K0|]; clear K0.
    step. step. ubal_by AL. step. if_lit.
    st1. step. try if_true.
    step. step. step. step. st1. st1. st1. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.
End S.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.

  Local Ltac errno_across ERR MU WM :=
    eapply (rw_cells_transport usegs _ _ _ _ _ ERR MU WM); unfold RERRNO; hcb; cbn; lia.

  (* [comment removed for export] *)
  Lemma bufnew_spec : bufnew_stmt H.
  Proof.
    unfold bufnew_stmt. intros until errv.
    intros A0 HP KREL BUD BUDC BUDB AUX SPB ST CEIL LO ERR MI TP MF IM GM RAE. subst a0.
    unfold BUFNEW_STACK, FR_BUF_MEM_new, CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, RMALLOC_STACK, BUFMEM_SIZE in *.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    eapply (sr_evt_krel H HH); [exact KREL| eapply bn_seg1; [exact ST| exact CEIL| lia| exact MI]|].
    intros ms1 (m1 & j & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (XP1 : xpres LB (bv_unsigned sp) memflag_foot m m1).
    { eapply xpres_of_munch; [exact MU1| exact WM1| | exact HB]. constructor; [left; cbn; lia| constructor]. }
    pose proof (czalloc_spec H HH) as CZ. unfold czalloc_stmt, czalloc_stmt_gen in CZ.
    eapply (sr_seq H HH).
    { eapply CZ with (lo := lo) (B := B) (LB := LB) (s := s) (v := v) (num := 32) (size := 1); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try (unfold CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, RMALLOC_STACK; lia).
      all: try first [exact KREL| exact ST1| exact CEIL| exact MI1| exact TP].
      all: lazymatch goal with
           | |- hs_RHEAP _ _ _ _ => eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]; constructor; [left; cbn; lia| constructor]
           | |- lb_bytes _ + _ <= _ => lia
           | |- lb_big _ + _ <= _ => rewrite big1_small by (unfold BIGB; lia); lia
           | |- hs_rauxv_ok _ _ _ => eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]; unfold RAUXV_CELL; constructor; [cbn; lia| constructor]
           | |- rw_cells _ _ _ _ => subst tp; rewrite errno_RATP in *; errno_across ERR MU1 WM1
           | |- MEMFLAG _ _ => eapply MEMFLAG_across; [exact MU1| exact WM1| unfold A_mem_inited; cbn; lia| exact MF]
           | |- IMPL_mem _ => eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]
           | |- GOT_mem _ => eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]
           end. }
    intros [ms2 mo2] PO. unfold czalloc_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A & p & s' &
                    -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & XP2 & BR & HEAP2 & BLK & MF2 & IM2 & GM2).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST2, XP2 by lia. change (32 * 1) with 32 in BR, HEAP2, BLK.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
    eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2) in FR1; [| left; cbn; lia| unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]].
    apply buf_zero_recut in BLK.
    eapply (sr_evt_krel H HH); [exact KREL2| eapply bn_seg2; [lia| lia| exact BR2| exact BLK| exact FR1| exact MI2]|].
    intros ms3 (m3 & -> & MU3 & WM3 & MI3 & HDR3).
    apply (sr_done H HH).
    unfold bufnew_post. cbn [cfg_ms cfg_model].
    exists u0, u1, u2, (Z_to_bv 64 0), b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m3, errv2, A, p, s'.
    split; [reflexivity|]. split; [exact KREL2|]. split; [exact MP2|]. split; [exact MI3|].
    split. { apply (stk_transport_disjoint usegs _ m2 m3 _ _ ST2) in MU3 as ST3; [| exact WM3| cbn; lia].
             apply (rw_cells_transport usegs _ m2 m3 _ _ FR1) in MU3 as FR3; [| exact WM3| cbn; lia].
             eapply stk_release in FR3; [| exact ST3| lia]. unfold cz_frame in FR3. cbn [cells_size csize Nat.add] in FR3.
             replace (bv_unsigned sp + -32 + 32) with (bv_unsigned sp) in FR3 by lia. exact FR3. }
    split. { eapply rw_cells_transport; [exact ERR2| exact MU3| exact WM3| subst tp; rewrite errno_RATP; unfold RERRNO; cbn; lia]. }
    split. { eapply (HH_rauxv_frame H HH); [exact AUX2| exact MU3| exact WM3|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor]. }
    split. { eapply xpres_trans; [exact XP1|]. eapply xpres_trans; [eapply (xpres_weaken LB LB _ _ memflag_foot); [exact XP2| lia| auto| auto]|].
             eapply (xpres_of_munch_fresh H HH); [exact HEAP2| lia| exact MU3| exact WM3|]. constructor; [right; left; cbn; lia| constructor]. }
    split; [exact BR|].
    split. { eapply (HH_RHEAP_frame H HH); [exact HEAP2| exact MU3| exact WM3|]. constructor; [| constructor]. right; right. exists (p, A, 32). split; [left; reflexivity| cbn; lia]. }
    split; [exact HDR3|].
    split; [eapply MEMFLAG_across; [exact MU3| exact WM3| unfold A_mem_inited; cbn; lia| exact MF2]|].
    split; [eapply IMPL_across; [exact MU3| exact WM3| unfold A_malloc_impl; cbn; lia| exact IM2]|].
    eapply GOT_across; [exact MU3| exact WM3| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM2].
  Qed.

  Lemma buffree_spec : buffree_stmt H.
  Proof.
    unfold buffree_stmt. intros until errv.
    intros A0 HIN BC LR MR FLR HP KREL AUX SPB ST CEIL LO ERR MI TP IM GM RAE. subst a0.
    unfold BUFFREE_STACK, FR_BUF_MEM_free, CFREE_STACK, RFREE_STACK, BUFMEM_SIZE in *.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    pose proof (HB _ HIN) as ABL. cbn [blk_addr blk_size fst snd] in ABL.
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP HIN) as BR. cbn [blk_addr blk_size fst snd] in BR. pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
    eapply (sr_evt_krel H HH); [exact KREL| eapply bf_seg1 with (lo := lo); [exact BC| lia| exact BR2| lia| exact LR| exact MR| exact FLR| exact ST| exact CEIL| lia| exact MI]|].
    intros ms1 (m1 & -> & MU1 & WM1 & MI1 & ST1 & BC1).
    assert (HP1 : hs_RHEAP H s LB m1).
    { eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (AUX1 : hs_rauxv_ok H m1 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]. unfold RAUXV_CELL. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    subst tp. rewrite errno_RATP in ERR.
    apply (rw_cells_transport usegs _ m m1 _ _ ERR) in MU1 as ERR1; [| exact WM1| unfold RERRNO; cbn; lia].
    assert (IM1 : IMPL_mem m1) by (eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]).
    assert (GM1 : GOT_mem m1) by (eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]).
    assert (XP1 : xpres LB (bv_unsigned sp) [] m m1).
    { eapply xpres_of_munch; [exact MU1| exact WM1| | exact HB]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    pose proof (cfree_spec H HH) as CF. unfold cfree_stmt in CF.
    eapply (sr_mono H HH).
    { eapply CF with (lo := lo) (B := B) (LB := LB) (s := s) (p := p) (n := 32); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact HP1| exact KREL| exact HIN| exact AUX1| exact ST1| exact CEIL| exact MI1| exact IM1| exact GM1| exact RAE].
      all: first [exact SPB | unfold CFREE_STACK, RFREE_STACK; lia
                 | replace (bv_unsigned (Z_to_bv 64 RATP) + -164) with RERRNO by (unfold RATP, RERRNO; rewrite unsigned_lit by lia; reflexivity); exact ERR1]. }
    intros [ms2 mo2] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & s2' &
                    -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & XP2 & HEAP2 & IM2 & GM2).
    unfold buffree_post. cbn [cfg_ms cfg_model].
    exists u0, u1, u2, b0, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, errv, s2'.
    split; [reflexivity|]. split; [exact KREL2|]. split; [exact MP2|]. split; [exact MI2|]. split; [exact ST2|].
    split; [rewrite errno_RATP; exact ERR2|]. split; [exact AUX2|].
    split. { eapply xpres_trans; [| exact XP2]. eapply (xpres_weaken LB _ _ _ []); [exact XP1| lia| | auto].
             intros b Hb. eapply (proj2 (proj2 (HH_lb_remove H HH))). exact Hb. }
    split; [exact HEAP2|]. split; [exact IM2| exact GM2].
  Qed.
End W.
