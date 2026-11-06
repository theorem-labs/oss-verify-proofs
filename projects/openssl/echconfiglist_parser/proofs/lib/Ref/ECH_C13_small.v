(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Rep ECH_LibState
     ECH_C1_stmt ECH_C1_malloc ECH_C5_stmt ECH_C13_stmt.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  Definition ECH_FILE : Z := 0x364d2.        (* [comment removed for export] *)
  Definition SN_RA : Z := 0x26c1b8.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sn_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists m1 j,
          ms' = MS (mkR (Z_to_bv 64 SN_RA) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp s1
                       (Z_to_bv 64 24) (Z_to_bv 64 ECH_FILE) (Z_to_bv 64 658) a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_zalloc) fc None m1 (seg_rom rsegs)
          /\ munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ stk rsegs m1 lo (bv_unsigned sp + -48)
          /\ rw_cells rsegs m1 (bv_unsigned sp + -48) [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_OSSL_ECHSTORE_new) fc None m (seg_rom rsegs)).
  Proof.
    intros until lo. intros ST CEIL LO MI. hcb. unfold P_OSSL_ECHSTORE_new, P_CRYPTO_zalloc, SN_RA, ECH_FILE.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    carve_frame 48%nat ST.
    do 15 step. finish. exact FR.
  Qed.

  (* [comment removed for export] *)
  Lemma sn_seg2 :
    forall (sp gp tp t0 t1 t2 s0x a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A : Z) (j : list byte),
      0 < A -> A + 24 <= bv_unsigned sp + -48 ->
      rw_cells rsegs m A [C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
      rw_cells rsegs m (bv_unsigned sp + -48) [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists m1,
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m1 (seg_rom rsegs)
          /\ munch [(A, A + 24)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ rw_cells rsegs m1 A [C8 (wz 0); C8 (wz 0); C8 (wz 0)])
        (MS (mkR (Z_to_bv 64 SN_RA) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0x s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 0) (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 SN_RA)) fc None m (seg_rom rsegs)).
  Proof.
    intros until j. intros HA HS BLK FR MI. unfold SN_RA.
    replace (ret_pc (Z_to_bv 64 0x26c1b8)) with (Z_to_bv 64 0x26c1b8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR. unfold wz in BLK.
    pose proof (munch_refl [(A, A + 24)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    step. if_cases K0; zify_cond K0. { kill K0. } clear K0.
    step. st1. step. try if_lit.
    step. do 5 st1. step. step. finish.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma thunk_gen : forall th,
    th = P_sk_OSSL_ECHEXT_freefunc_thunk \/ th = P_sk_OSSL_ECHSTORE_ENTRY_freefunc_thunk \/ th = P_sk_X509_BUFFER_freefunc_thunk ->
    thunk_stmt_at th.
  Proof.
    intros th CASES. unfold thunk_stmt_at. intros until lo. intros A0 A1 FR FE ST LO MI. subst a0 a1.
    unfold FR_sk_freefunc_thunk in LO.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    destruct CASES as [-> |[-> | ->]]; unfold P_sk_OSSL_ECHEXT_freefunc_thunk, P_sk_OSSL_ECHSTORE_ENTRY_freefunc_thunk, P_sk_X509_BUFFER_freefunc_thunk.
    all: carve_frame 16%nat ST; do 4 st1; step; step; st1; st1; step; step.
    all: replace (ret_pc (Z_to_bv 64 f)) with (Z_to_bv 64 f) by (symmetry; apply ret_pc_even; [lia| exact FE]).
    all: release_frame FR0 ST (bv_unsigned sp); finish.
  Qed.
  Lemma thunk_ext_spec : thunk_ext_stmt.     Proof. apply thunk_gen. left. reflexivity. Qed.
  Lemma thunk_entry_spec : thunk_entry_stmt. Proof. apply thunk_gen. right; left. reflexivity. Qed.
  Lemma thunk_xbuf_spec : thunk_xbuf_stmt.   Proof. apply thunk_gen. right; right. reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma entryfree_null_spec : entryfree_null_stmt.
  Proof.
    unfold entryfree_null_stmt, nullret_stmt_at. intros until lo. intros ST LO MI RAE. unfold P_ossl_echstore_entry_free.
    pose proof (word_range sp) as SPR. pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    step. try if_lit. step. finish.
  Qed.
  Lemma extfree_null_spec : extfree_null_stmt.
  Proof.
    unfold extfree_null_stmt, nullret_stmt_at. intros until lo. intros ST LO MI RAE. unfold P_ossl_echext_free.
    pose proof (word_range sp) as SPR. pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    step. try if_lit. step. finish.
  Qed.
  Lemma pkeyfree_null_spec : pkeyfree_null_stmt.
  Proof.
    unfold pkeyfree_null_stmt, nullret_stmt_at. intros until lo. intros ST LO MI RAE. unfold P_EVP_PKEY_free, FR_EVP_PKEY_free in *.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    carve_frame 32%nat ST. do 4 st1. step. step. try if_lit. do 3 st1. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.
End S.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.

  Local Ltac errno_across ERR MU WM :=
    eapply (rw_cells_transport rsegs _ _ _ _ _ ERR MU WM); unfold RERRNO; hcb; cbn; lia.

  Lemma storenew_spec : storenew_stmt H.
  Proof.
    unfold storenew_stmt. intros until errv.
    intros A0 A1 HP KREL BUD BUDC BUDB AUX SPB ST CEIL LO ERR MI TP MF IM GM RAE. subst a0 a1.
    unfold STORENEW_STACK, FR_OSSL_ECHSTORE_new, CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, RMALLOC_STACK in LO.
    unfold STORE_SIZE in BUD.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    eapply (sr_evt_krel H HH); [exact KREL| eapply sn_seg1; [exact ST| exact CEIL| lia| exact MI]|].
    intros ms1 (m1 & j & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (XP1 : xpres LB (bv_unsigned sp) memflag_foot m m1).
    { eapply xpres_of_munch; [exact MU1| exact WM1| | exact HB]. constructor; [left; cbn; lia| constructor]. }
    pose proof (czalloc_spec H HH) as CZ. unfold czalloc_stmt, czalloc_stmt_gen in CZ.
    eapply (sr_seq H HH).
    { eapply CZ with (lo := lo) (B := B) (LB := LB) (s := s) (v := v) (num := 24) (size := 1); rewrite ?unsigned_lit by lia; try reflexivity.
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
    rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST2, XP2 by lia. change (24 * 1) with 24 in BR, HEAP2, BLK.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
    eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2) in FR1; [| left; cbn; lia| unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]].
    assert (BLK' : rw_cells rsegs m2 A [C8 (wz 0); C8 (wz 0); C8 (wz 0)]).
    { eapply rw_cells_recut; [exact BLK| vm_compute; repeat split; reflexivity| vm_compute; reflexivity]. }
    eapply (sr_evt_krel H HH); [exact KREL2| eapply sn_seg2; [lia| lia| exact BLK'| exact FR1| exact MI2]|].
    intros ms3 (m3 & -> & MU3 & WM3 & MI3 & HDR3).
    apply (sr_done H HH).
    unfold storenew_post. cbn [cfg_ms cfg_model].
    apply (rw_cells_transport rsegs _ m2 m3 _ _ FR1) in MU3 as FR3; [| exact WM3| cbn; lia].
    exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m3, errv2, A, p, s'.
    split; [reflexivity|]. split; [exact KREL2|]. split; [exact MP2|]. split; [exact MI3|].
    split. { apply (stk_transport_disjoint rsegs _ m2 m3 _ _ ST2) in MU3 as ST3; [| exact WM3| cbn; lia].
             eapply stk_release in FR3; [| exact ST3| lia]. cbn [cells_size csize Nat.add] in FR3.
             replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) in FR3 by lia. exact FR3. }
    split. { eapply rw_cells_transport; [exact ERR2| exact MU3| exact WM3| subst tp; rewrite errno_RATP; unfold RERRNO; cbn; lia]. }
    split. { eapply (HH_rauxv_frame H HH); [exact AUX2| exact MU3| exact WM3|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor]. }
    split. { eapply xpres_trans; [exact XP1|]. eapply xpres_trans; [eapply (xpres_weaken LB LB _ _ memflag_foot); [exact XP2| lia| auto| auto]|].
             eapply (xpres_of_munch_fresh H HH); [exact HEAP2| lia| exact MU3| exact WM3|]. constructor; [right; left; cbn; lia| constructor]. }
    split; [exact BR|].
    split. { eapply (HH_RHEAP_frame H HH); [exact HEAP2| exact MU3| exact WM3|]. constructor; [| constructor]. right; right. exists (p, A, 24). split; [left; reflexivity| cbn; lia]. }
    split.
    { unfold STOREobj, STORE_SIZE. cbn [es_entries es_id es_entries_o store_empty ENTRIES]. split; [exact HDR3|]. split; [left; reflexivity| reflexivity]. }
    split; [eapply MEMFLAG_across; [exact MU3| exact WM3| unfold A_mem_inited; cbn; lia| exact MF2]|].
    split; [eapply IMPL_across; [exact MU3| exact WM3| unfold A_malloc_impl; cbn; lia| exact IM2]|].
    eapply GOT_across; [exact MU3| exact WM3| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM2].
  Qed.
End W.
