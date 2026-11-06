(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Rep ECH_LibState ECH_C1_stmt ECH_C1_malloc ECH_C5_stmt ECH_UbKit.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.

  Definition SK_FILE : Z := 0x2a3a6.        (* [comment removed for export] *)
  Definition SN_RA : Z := 0xe3000.   Definition SNC_RA : Z := 0xe30fc.

  (* [comment removed for export] *)
  Lemma SKobj_hdr : forall LB m a K, SKobj LB m a K -> exists pad, length pad = 4%nat /\ rw_cells usegs m a (sk_hdr_cells K pad).
  Proof. intros LB m a K (H1 & _). exact H1. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma skset_thunks_null_spec : skset_thunks_null_stmt.
  Proof.
    unfold skset_thunks_null_stmt, sknull_stmt_at. intros until lo. intros ST LO LO48 MI. unfold P_OPENSSL_sk_set_thunks.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 16%nat ST.
    do 4 step. step. try if_true. do 4 step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.

  Lemma sk_num_null_spec : sk_num_null_stmt.
  Proof.
    unfold sk_num_null_stmt, sknull_stmt_at. intros until lo. intros ST LO LO48 MI. unfold P_OPENSSL_sk_num.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 16%nat ST.
    do 4 step. step. try if_true. step. do 4 step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.

  Lemma sk_free_null_spec : sk_free_null_stmt.
  Proof.
    unfold sk_free_null_stmt, sknull_stmt_at. intros until lo. intros ST LO LO48 MI. unfold P_OPENSSL_sk_free.
    (* [comment removed for export] *)
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 32%nat ST.
    do 6 step. step. try if_true. do 6 step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.

  Lemma sk_pop_free_null_spec : sk_pop_free_null_stmt.
  Proof.
    unfold sk_pop_free_null_stmt, sknull_stmt_at. intros until lo. intros ST LO LO48 MI. unfold P_OPENSSL_sk_pop_free.
    (* [comment removed for export] *)
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 48%nat ST.
    do 8 step. step. try if_true. do 8 step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma u64arr_across : forall W m m' A ws,
    munch W m m' -> wmono usegs m m' -> disjoint_from W A (8 * Z.of_nat (length ws)) -> u64arr usegs m A ws -> u64arr usegs m' A ws.
  Proof. intros W m m' A ws MU WM DJ AR. eapply u64arr_transport; [exact AR| exact MU| exact WM| exact DJ]. Qed.

  (* [comment removed for export] *)
  Lemma SKobj_rehdr : forall LB m m' a K K' pad W,
    SKobj LB m a K ->
    sk_elems K' = sk_elems K -> sk_data K' = sk_data K -> sk_cap K' = sk_cap K -> sk_id K' = sk_id K -> sk_did K' = sk_did K ->
    0 <= sk_sorted K' <= 1 ->
    length pad = 4%nat -> rw_cells usegs m' a (sk_hdr_cells K' pad) ->
    munch W m m' -> wmono usegs m m' -> (sk_cap K = 0 \/ disjoint_from W (sk_data K) (8 * sk_cap K)) ->
    SKobj LB m' a K'.
  Proof.
    intros LB m m' a K K' pad W SO E1 E2 E3 E4 E5 SRT PL HDR MU WM DJ.
    destruct SO as (_ & POS & IN & NC & CAP & _ & EL & DAT). unfold SKobj, sk_num in *. rewrite E1, E2, E3, E4, E5.
    split; [exists pad; split; [exact PL| exact HDR]|]. split; [exact POS|]. split; [exact IN|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact EL|].
    destruct DAT as [D0|(D1 & D2 & D3 & D4 & AR & junk & JK)]; [left; exact D0| right].
    destruct DJ as [DJ|DJ]; [lia|]. unfold zlength in *.
    split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact D4|]. split.
    - eapply u64arr_across; [exact MU| exact WM| | exact AR]. rewrite length_map. eapply disjoint_from_mono; [exact DJ| lia].
    - exists junk. eapply rw_cells_transport; [exact JK| exact MU| exact WM|]. cbn [cells_size csize Nat.add].
      eapply disjoint_from_sub; [exact DJ| lia| lia| lia].
  Qed.

  Lemma skset_gen : forall entry which,
    (entry = P_OPENSSL_sk_set_thunks /\ which = O_SK_FREETH) \/ (entry = P_OPENSSL_sk_set_cmp_thunks /\ which = O_SK_CMPTH)
    \/ (entry = P_OPENSSL_sk_set_copy_thunks /\ which = O_SK_COPYTH) ->
    skset_stmt_at entry which.
  Proof.
    intros entry which CASES. unfold skset_stmt_at; intros until K; intros A0 A1 HF AL SO [BL1 BL2] ST LO MI.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (SKobj_hdr _ _ _ _ SO) as (pad & PL & HDR). unfold sk_hdr_cells, wz in HDR.
    pose proof (rw_cells_bound _ _ _ _ HDR) as HB. cbn [cells_size csize Nat.add] in HB. unfold SK_SIZE in *.
    pose proof SO as SO'. destruct SO' as (_ & POS & _ & NC & CAP & SRT & EL & DAT).
    pose proof (munch_refl [(lo, bv_unsigned sp); (a, a + 56)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    subst a0 a1. carve_frame 16%nat ST.
    destruct CASES as [[-> ->]|[[-> ->]|[-> ->]]]; unfold P_OPENSSL_sk_set_thunks, P_OPENSSL_sk_set_cmp_thunks, P_OPENSSL_sk_set_copy_thunks.
    all: do 4 step; step; if_cases K0; zify_cond K0; [exfalso; revert K0; rewrite ?unsigned_lit by lia; lia|]; clear K0;
         step; ubal_by AL; step; if_lit;   (* [comment removed for export] *)
         st1; do 4 step;
         release_frame FR ST (bv_unsigned sp); finish.
    all: eapply (SKobj_rehdr LB m _ a K _ pad); [exact SO| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| cbn; lia| exact PL| | exact MU| exact WM|].
    all: lazymatch goal with
         | |- rw_cells _ _ _ _ =>
             unfold sk_hdr_cells, sk_with_thunk, O_SK_CMPTH, O_SK_FREETH, O_SK_COPYTH, wz;
             cbn [sk_elems sk_data sk_cap sk_sorted sk_comp sk_cmp_thunk sk_free_thunk sk_copy_thunk Z.eqb Pos.eqb]; unfold sk_num; cbn [sk_elems]; exact HDR
         | |- _ => destruct DAT as [[Z0 _]|(D1 & D2 & D3 & _)]; [left; exact Z0| right; unfold SK_SIZE in D3; clear - BL2 D1 D2 D3 LO SPR; cbn; lia]
         end.
  Qed.

  Lemma skset_thunks_spec : skset_thunks_stmt.
  Proof. apply skset_gen. left. split; reflexivity. Qed.
  Lemma skset_cmp_thunks_spec : skset_cmp_thunks_stmt.
  Proof. apply skset_gen. right; left. split; reflexivity. Qed.
  Lemma skset_copy_thunks_spec : skset_copy_thunks_stmt.
  Proof. apply skset_gen. right; right. split; reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sknum_spec : sknum_stmt.
  Proof.
    unfold sknum_stmt. intros until K; intros A0 AL SO [BL1 BL2] ST LO MI. unfold P_OPENSSL_sk_num.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (SKobj_hdr _ _ _ _ SO) as (pad & PL & HDR). unfold sk_hdr_cells, wz in HDR.
    pose proof (rw_cells_bound _ _ _ _ HDR) as HB. cbn [cells_size csize Nat.add] in HB. unfold SK_SIZE in *.
    pose proof SO as SO'. destruct SO' as (_ & POS & _ & NC & CAP & SRT & EL & DAT).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    subst a0. carve_frame 16%nat ST.
    do 4 step. step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    step. ubal_by AL. step. if_lit.   (* [comment removed for export] *)
    st1. rewrite sx32_wz by lia. unfold wz. do 5 step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.

  Lemma skvalue_spec : skvalue_stmt.
  Proof.
    unfold skvalue_stmt. intros until K; intros A0 A1 HI NTH AL ALD SO [BL1 BL2] ST LO MI. unfold P_OPENSSL_sk_value.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (SKobj_hdr _ _ _ _ SO) as (pad & PL & HDR). unfold sk_hdr_cells, wz in HDR.
    pose proof (rw_cells_bound _ _ _ _ HDR) as HB. cbn [cells_size csize Nat.add] in HB. unfold SK_SIZE in *.
    pose proof SO as SO'. destruct SO' as (_ & POS & _ & NC & CAP & SRT & EL & DAT).
    unfold sk_num, zlength in *. pose proof (nth_error_lt _ _ _ NTH) as IL.
    destruct DAT as [[Z0 _]|(D1 & D2 & D3 & D4 & AR & junk & JK)]; [lia|]. destruct BL2 as [Z0|BL2]; [lia|]. clear JK.
    pose proof (proj1 (Forall_forall _ _) EL p ltac:(eapply nth_error_In; exact NTH)) as PR. cbn in PR.
    pose proof (u64arr_bound _ _ _ _ AR) as ARB. rewrite length_map in ARB.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    (* [comment removed for export] *)
    pose proof AR as AR'. clear AR. change (id (u64arr usegs m (sk_data K) (map wz (sk_elems K)))) in AR'.
    subst a0 a1. carve_frame 16%nat ST.
    (* [comment removed for export] *)
    do 4 step. step.
    step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit, ?signed_lit by lia. lia. } clear K0.
    step. ubal_by AL. step. if_lit.
    st1. rewrite sx32_wz by lia. unfold wz. step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit, ?signed_lit by lia. lia. } clear K0.
    step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (AR : u64arr usegs mx (sk_data K) (map wz (sk_elems K)))
        by (unfold id in AR'; eapply u64arr_across; [exact MU| exact WM| rewrite length_map; cbn; lia| exact AR']) end.
    clear AR'.
    zstep. zstep. rewrite (Z.shiftl_mul_pow2 i 3) by lia. change (2^3) with 8.
    step. ub_dead_by (clear - D2 ARB HI).
    zstep. zstep. zstep. rewrite ub_nullcons by lia. step. if_lit.
    step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    step. ubal_by ALD. step. if_lit.
    pose proof (u64arr_read usegs _ _ _ i (wz p) (wa (sk_data K + i * 8)) AR ltac:(rewrite nth_error_map, NTH; reflexivity) ltac:(lia) ltac:(f_equal; lia)) as RD.
    unfold wz in RD. step. step. step.
    do 4 step. release_frame FR ST (bv_unsigned sp). finish.
  Qed.
End S.
