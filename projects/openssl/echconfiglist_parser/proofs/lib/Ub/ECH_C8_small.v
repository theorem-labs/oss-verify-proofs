(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_Rep ECH_KitH ECH_LibState ECH_B64 ECH_C1_stmt ECH_C1_malloc ECH_C1_free ECH_C8_stmt ECH_UbKit.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition ENC_FILE : Z := 0x1f61d.       (* [comment removed for export] *)
Definition EN_T1 : Z := 0xe2f74.   (* [comment removed for export] *)
Definition EF_T1 : Z := 0xe3fa4.   (* [comment removed for export] *)

Section S.
  Context {HCEIL : HeapCeil}.

  (* [comment removed for export] *)
  Lemma en_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1,
          ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 EN_T1) t2 s0 s1 (Z_to_bv 64 92) (Z_to_bv 64 ENC_FILE) (Z_to_bv 64 112) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_zalloc) fc None m1 (seg_rom usegs)
          /\ munch [(bv_unsigned sp + -16, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_EVP_ENCODE_CTX_new) fc None m (seg_rom usegs)).
  Proof.
    intros until lo. intros ST LO MI. hcb. unfold P_EVP_ENCODE_CTX_new, P_CRYPTO_zalloc, ENC_FILE, EN_T1.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 16%nat ST.
    do 8 step. do 2 st1. step. step. step.   (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.

  (* [comment removed for export] *)
  Lemma ef_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1,
          ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 EF_T1) t2 s0 s1 a0 (Z_to_bv 64 ENC_FILE) (Z_to_bv 64 117) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m1 (seg_rom usegs)
          /\ munch [(bv_unsigned sp + -16, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_EVP_ENCODE_CTX_free) fc None m (seg_rom usegs)).
  Proof.
    intros until lo. intros ST LO MI. hcb. unfold P_EVP_ENCODE_CTX_free, P_CRYPTO_free, ENC_FILE, EF_T1.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 16%nat ST.
    do 7 step. do 2 st1. step. step. step.   (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.

  (* [comment removed for export] *)
  Lemma di_seg :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a lo : Z) (old : list byte),
      rw_cells usegs m a [CB 92 old] -> 0 < a -> a mod 16 = 0 -> a + 92 <= lo ->
      stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> mem_inv usegs m -> bv_unsigned ra mod 2 = 0 ->
      evt usegs (fun ms' => exists m1,
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m1 (seg_rom usegs)
          /\ munch [(bv_unsigned sp + -16, bv_unsigned sp); (a, a + 92)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (bv_unsigned sp)
          /\ rw_cells usegs m1 a [C4 (wz 0); CB 80 (firstn 80 (skipn 4 old)); C4 (wz 0); C4 (wz 0)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_EVP_DecodeInit) fc None m (seg_rom usegs)).
  Proof.
    intros until old. intros BLK POS PAL BL ST LO MI RAE. unfold P_EVP_DecodeInit.
    pose proof (rw_cells_bound _ _ _ _ BLK) as HB. cbn [cells_size csize Nat.add length] in HB.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -16, bv_unsigned sp); (a, a + 92)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 16%nat ST.
    do 4 step.
    step. ub_dead_by (clear - POS). step. ubal_by PAL. step. if_lit.   (* [comment removed for export] *)
    do 3 st1. do 2 st1. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
    all: unfold wz; exact BLK.
  Qed.
End S.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.

  Local Ltac errno_across ERR MU WM :=
    eapply (rw_cells_transport usegs _ _ _ _ _ ERR MU WM); unfold RERRNO; hcb; cbn; lia.

  Lemma encnew_spec : encnew_stmt H.
  Proof.
    unfold encnew_stmt. intros until errv.
    intros HP KREL BUD BUDC BUDB AUX SPB ST CEIL LO ERR MI TP MF IM GM RAE.
    unfold ENCNEW_STACK, FR_EVP_ENCODE_CTX_new, CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, RMALLOC_STACK in LO.
    unfold ENCCTX_SIZE in BUD.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    eapply (sr_evt_krel H HH); [exact KREL| eapply en_seg1; [exact ST| lia| exact MI]|].
    intros ms1 (m1 & -> & MU1 & WM1 & MI1 & ST1).
    assert (XP1 : xpres LB (bv_unsigned sp) memflag_foot m m1).
    { eapply xpres_of_munch; [exact MU1| exact WM1| | exact HB]. constructor; [left; cbn; lia| constructor]. }
    pose proof (czalloc_spec H HH) as CZ. unfold czalloc_stmt, czalloc_stmt_gen in CZ.
    eapply (sr_mono H HH).
    { eapply CZ with (lo := lo) (B := B) (LB := LB) (s := s) (v := v) (num := 92) (size := 1); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try (unfold CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, RMALLOC_STACK; lia).
      all: try first [exact KREL| exact ST1| exact CEIL| exact MI1| exact TP| exact SPB].
      all: lazymatch goal with
           | |- hs_RHEAP _ _ _ _ => eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]; constructor; [left; cbn; lia| constructor]
           | |- lb_bytes _ + _ <= _ => lia
           | |- Z.of_nat _ + _ <= _ => lia
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
    change (92 * 1) with 92 in BR, HEAP2, BLK.
    unfold encnew_post. cbn [cfg_ms cfg_model].
    exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, errv2, A, p, s'.
    split; [reflexivity|]. split; [exact KREL2|]. split; [exact MP2|]. split; [exact MI2|]. split; [exact ST2|].
    split; [exact ERR2|]. split; [exact AUX2|].
    split; [eapply xpres_trans; [exact XP1| exact XP2]|].
    split; [exact HEAP2|].
    split.
    { unfold ENCCTX, ENCCTX_SIZE. exists (zeros 80), 0.
      split; [reflexivity|]. split; [reflexivity|].
      split. { eapply rw_cells_recut; [exact BLK| vm_compute; repeat split; reflexivity| vm_compute; reflexivity]. }
      split; [lia|]. split; [left; reflexivity|]. split; [exact BR|].
      unfold du_inv. split; [constructor| cbn; lia]. }
    split; [exact MF2|]. split; [exact IM2|]. exact GM2.
  Qed.

  Lemma encfree_spec : encfree_stmt H.
  Proof.
    unfold encfree_stmt. intros until errv.
    intros A0 EO HP KREL AUX SPB ST CEIL LO ERR MI TP IM GM RAE.
    unfold ENCFREE_STACK, FR_EVP_ENCODE_CTX_free, CFREE_STACK, RFREE_STACK in LO.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    destruct EO as (raw & line & L80 & FD & EC & LR & EIN & EBR & DI).
    eapply (sr_evt_krel H HH); [exact KREL| eapply ef_seg1; [exact ST| lia| exact MI]|].
    intros ms1 (m1 & -> & MU1 & WM1 & MI1 & ST1).
    assert (XP1 : xpres LB (bv_unsigned sp) [] m m1).
    { eapply xpres_of_munch; [exact MU1| exact WM1| | exact HB]. constructor; [left; cbn; lia| constructor]. }
    assert (HP1 : hs_RHEAP H s LB m1).
    { eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]. constructor; [left; cbn; lia| constructor]. }
    assert (AUX1 : hs_rauxv_ok H m1 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor]. }
    subst tp. rewrite errno_RATP in ERR.
    apply (rw_cells_transport usegs _ m m1 _ _ ERR) in MU1 as ERR1; [| exact WM1| unfold RERRNO; cbn; lia].
    assert (IM1 : IMPL_mem m1) by (eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]).
    assert (GM1 : GOT_mem m1) by (eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]).
    pose proof (cfree_spec H HH) as CF. unfold cfree_stmt in CF.
    eapply (sr_mono H HH).
    { eapply CF with (lo := lo) (B := B) (LB := LB) (s := s) (p := p) (n := ENCCTX_SIZE); try reflexivity.
      all: try first [exact A0| exact HP1| exact KREL| exact EIN| exact AUX1| exact SPB| exact ST1| exact CEIL| exact MI1| exact IM1| exact GM1| exact RAE].
      all: first [unfold CFREE_STACK, RFREE_STACK; lia | rewrite errno_RATP; exact ERR1]. }
    intros [ms2 mo2] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (z0 & z1 & z2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & z3 & z4 & z5 & z6 & m2 & s2' &
                    -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & XP2 & HEAP2 & IM2 & GM2).
    unfold encfree_post. cbn [cfg_ms cfg_model].
    exists z0, z1, z2, e0, e1, e2, e3, e4, e5, e6, e7, z3, z4, z5, z6, m2, errv, s2'.
    split; [reflexivity|]. split; [exact KREL2|]. split; [exact MP2|]. split; [exact MI2|]. split; [exact ST2|].
    split; [exact ERR2|]. split; [exact AUX2|].
    split.
    { eapply xpres_trans; [| exact XP2]. eapply xpres_weaken; [exact XP1| lia| | auto].
      intros b Hb. eapply (proj2 (proj2 (HH_lb_remove H HH))). exact Hb. }
    split; [exact HEAP2|]. split; [exact IM2|]. exact GM2.
  Qed.
End W.

(* [comment removed for export] *)
Section P.
  Context {HCEIL : HeapCeil}.

  Lemma decinit_spec : decinit_stmt.
  Proof.
    unfold decinit_stmt. intros until old. intros A0 BLK EIN BR BL ST LO MI RAE. subst a0.
    unfold DECINIT_STACK, FR_EVP_DecodeInit in LO. unfold ENCCTX_SIZE in *.
    pose proof BR as (BR1 & BR2 & _).
    eapply evt_mono; [eapply di_seg with (lo := lo); [exact BLK| exact BR1| exact BR2| exact BL| exact ST| exact LO| exact MI| exact RAE]|].
    intros ms' (m1 & -> & MU1 & WM1 & MI1 & ST1 & BLK1). unfold c8_post.
    exists t0, t1, t2, (Z_to_bv 64 a), (Z_to_bv 64 0), a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m1.
    split; [reflexivity|]. split; [rewrite unsigned_lit by (pose proof (rw_cells_bound _ _ _ _ BLK) as HB; cbn in HB; lia); reflexivity|].
    split. { unfold ENCCTX_foot, ENCCTX_SIZE. eapply munch_weaken; [| exact MU1]. intros x Hx. pose proof (word_range sp). cbn in Hx |- *. lia. }
    split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
    split; [| exact I].
    unfold ENCCTX. exists (firstn 80 (skipn 4 old)), 0.
    pose proof (rw_cells_bound _ _ _ _ BLK) as HB.
    assert (L92 : length old = 92%nat) by (destruct BLK as [[WF _] _]; cbn in WF; destruct WF as [L _]; exact L).
    split; [rewrite length_firstn, length_skipn, L92; reflexivity|]. split; [reflexivity|].
    split; [exact BLK1|]. split; [lia|]. split; [exact EIN|]. split; [exact BR|].
    unfold du_inv. split; [constructor| cbn; lia].
  Qed.
End P.
