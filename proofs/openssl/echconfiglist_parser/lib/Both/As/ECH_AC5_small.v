(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C5 ECH_AKit ECH_AsKit.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.   (* [comment removed for export] *)

  Lemma SKobj_hdr : forall LB m a K, SKobj LB m a K -> exists pad, length pad = 4%nat /\ rw_cells asegs m a (sk_hdr_cells K pad).
  Proof. intros LB m a K (H1 & _). exact H1. Qed.

  Lemma ACONST_stack_frame5 : forall m m' lo hi, ACONST m -> munch [(lo, hi)] m m' -> wmono asegs m m' -> aceil <= lo -> ACONST m'.
  Proof.
    intros m m' lo hi AC MU WM CE. eapply ACONST_frame; [exact AC| exact MU| exact WM|].
    constructor; [| constructor]. apply aconst_ok_high; cbn [fst snd]; acb; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia.
  Qed.

  Lemma ub_nullcons : forall d x, 0 < d -> 0 < x -> Z.lxor (Z.b2z (0 <? d)) (Z.b2z (x <? 1)) = 1.
  Proof.
    intros d x Hd Hx. replace (0 <? d) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (x <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac null_pre ST :=
    let SPR := fresh "SPR" in let LO0 := fresh "LO0" in
    lazymatch type of ST with stk _ ?m ?lo (bv_unsigned ?sp) =>
      pose proof (aword_range sp) as SPR; assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption);
      pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU; pose proof (wmono_refl asegs m) as WM
    end.
  Local Ltac null_post ST AC MU WM CEIL :=
    lazymatch type of ST with stk _ _ _ (bv_unsigned ?sp + _) =>
      lazymatch goal with FR : rw_cells _ _ _ _ |- _ => release_frame FR ST (bv_unsigned sp) end end;
    unfold sknull_post; finish;
    eapply ACONST_stack_frame5; [exact AC| exact MU| exact WM| exact CEIL].

  Lemma askset_thunks_null_spec : skset_thunks_null_stmt.
  Proof.
    unfold skset_thunks_null_stmt, sknull_stmt_at. unfold P_OPENSSL_sk_set_thunks. intros until lo; intros ST CEIL LO MI AC; acb. null_pre ST.
    carve_frame 16%nat ST. do 4 step. step. try if_true. try if_lit. do 4 step. null_post ST AC MU WM CEIL.
  Qed.
  Lemma ask_num_null_spec : sk_num_null_stmt.
  Proof.
    unfold sk_num_null_stmt, sknull_stmt_at. unfold P_OPENSSL_sk_num. intros until lo; intros ST CEIL LO MI AC; acb. null_pre ST.
    carve_frame 16%nat ST. do 4 step. step. try if_true. try if_lit. step. do 4 step. null_post ST AC MU WM CEIL.
  Qed.
  Lemma ask_free_null_spec : sk_free_null_stmt.
  Proof.
    unfold sk_free_null_stmt, sknull_stmt_at. unfold P_OPENSSL_sk_free, FR_sk_free. intros until lo; intros ST CEIL LO MI AC; acb. null_pre ST.
    carve_frame 32%nat ST. do 6 step. step. try if_true. try if_lit. do 6 step. null_post ST AC MU WM CEIL.
  Qed.
  Lemma ask_pop_free_null_spec : sk_pop_free_null_stmt.
  Proof.
    unfold sk_pop_free_null_stmt, sknull_stmt_at. unfold P_OPENSSL_sk_pop_free, FR_sk_pop_free. intros until lo; intros ST CEIL LO MI AC; acb. null_pre ST.
    carve_frame 112%nat ST. do 15 step. step. try if_true. try if_lit. do 15 step. null_post ST AC MU WM CEIL.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma u64arr_across : forall W m m' A ws,
    munch W m m' -> wmono asegs m m' -> disjoint_from W A (8 * Z.of_nat (length ws)) -> u64arr asegs m A ws -> u64arr asegs m' A ws.
  Proof. intros W m m' A ws MU WM DJ AR. eapply u64arr_transport; [exact AR| exact MU| exact WM| exact DJ]. Qed.

  (* [comment removed for export] *)
  Lemma SKobj_rehdr : forall LB m m' a K K' pad W,
    SKobj LB m a K ->
    sk_elems K' = sk_elems K -> sk_data K' = sk_data K -> sk_cap K' = sk_cap K -> sk_id K' = sk_id K -> sk_did K' = sk_did K ->
    0 <= sk_sorted K' <= 1 ->
    length pad = 4%nat -> rw_cells asegs m' a (sk_hdr_cells K' pad) ->
    munch W m m' -> wmono asegs m m' -> (sk_cap K = 0 \/ disjoint_from W (sk_data K) (8 * sk_cap K)) ->
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

  Lemma askset_gen : forall entry which,
    (entry = P_OPENSSL_sk_set_thunks /\ which = O_SK_FREETH) \/ (entry = P_OPENSSL_sk_set_cmp_thunks /\ which = O_SK_CMPTH)
    \/ (entry = P_OPENSSL_sk_set_copy_thunks /\ which = O_SK_COPYTH) ->
    skset_stmt_at H entry which.
  Proof.
    intros entry which CASES. unfold skset_stmt_at; intros until K; intros A0 A1 HF SO [BL1 BL2] [SH1 SH2] [BR1 BR2] AC ST CEIL LO MI. acb.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (SKobj_hdr _ _ _ _ SO) as (pad & PL & HDR). unfold sk_hdr_cells, wz in HDR.
    pose proof (rw_cells_bound _ _ _ _ HDR) as HB. cbn [cells_size csize Nat.add] in HB. unfold SK_SIZE in *.
    pose proof SO as SO'. destruct SO' as (_ & POS & _ & NC & CAP & SRT & EL & DAT).
    pose proof (ACONST_shbase m AC) as [GSB SHB]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB. rewrite ASHADOW_BASE_val in SHB.
    pose proof BR1 as (_ & _ & _ & _ & _ & _ & AP1). pose proof (aapp_not_shadowland _ _ AP1) as NS1. pose proof (aapp_bounds _ _ AP1 ltac:(lia)) as (_ & _ & AH1 & _). unfold AAPP_HI in AH1.
    pose proof BR1 as (_ & A16 & _). assert (AL : a mod 8 = 0) by (clear - A16; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(lo, bv_unsigned sp); (a, a + 56)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (ACC0 : accessible m a 56) by (eapply addressable_accessible; [exact SH1| lia| lia| unfold AAPP_HI; lia]).
    pose proof ACC0 as ACC'. clear ACC0. change (id (accessible m a 56)) in ACC'.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(lo, bv_unsigned sp); (a, a + 56)]).
    { constructor; [cbn; unfold AHI_LO in *; lia| constructor; [cbn; exact NS1| constructor]]. }
    subst a0 a1. carve_frame 16%nat ST.
    destruct CASES as [[-> ->]|[[-> ->]|[-> ->]]]; unfold P_OPENSSL_sk_set_thunks, P_OPENSSL_sk_set_cmp_thunks, P_OPENSSL_sk_set_copy_thunks.
    all: do 4 step; step; if_cases K0; zify_cond K0; [exfalso; revert K0; rewrite ?unsigned_lit by lia; lia|]; clear K0.
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
           assert (ACC : accessible mx a 56) by (unfold id in ACC'; eapply accessible_across; [exact ACC'| exact MU| exact NSW]) end; clear ACC'.
    (* [comment removed for export] *)
    all: step; ubal_by AL; step; if_lit; step; step; step; zstep; zstep; zstep.
    all: [> ck8_check ACC (a + 40) | ck8_check ACC (a + 32) | ck8_check ACC (a + 48)].
    all: st1; do 4 step; release_frame FR ST (bv_unsigned sp); unfold skset_post; finish.
    all: try (eapply ACONST_frame; [exact AC| exact MU| exact WM|];
              constructor; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| constructor; [eapply aconst_ok_aapp; [exact AP1| cbn; lia| cbn; lia]| constructor]]).
    all: eapply (SKobj_rehdr LB m _ a K _ pad); [exact SO| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| cbn; lia| exact PL| | exact MU| exact WM|].
    all: lazymatch goal with
         | |- rw_cells _ _ _ _ =>
             unfold sk_hdr_cells, sk_with_thunk, O_SK_CMPTH, O_SK_FREETH, O_SK_COPYTH, wz;
             cbn [sk_elems sk_data sk_cap sk_sorted sk_comp sk_cmp_thunk sk_free_thunk sk_copy_thunk Z.eqb Pos.eqb]; unfold sk_num; cbn [sk_elems]; exact HDR
         | |- _ => destruct DAT as [[Z0 _]|(D1 & D2 & D3 & _)]; [left; exact Z0| right; unfold SK_SIZE in D3; clear - BL2 D1 D2 D3 LO SPR; cbn; lia]
         end.
  Qed.
  Lemma askset_thunks_spec : skset_thunks_stmt H.
  Proof. apply askset_gen. left. split; reflexivity. Qed.
  Lemma askset_cmp_thunks_spec : skset_cmp_thunks_stmt H.
  Proof. apply askset_gen. right; left. split; reflexivity. Qed.
  Lemma askset_copy_thunks_spec : skset_copy_thunks_stmt H.
  Proof. apply askset_gen. right; right. split; reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma asknum_spec : sknum_stmt H.
  Proof.
    unfold sknum_stmt. intros until K; intros A0 SO [BL1 BL2] [SH1 SH2] [BR1 BR2] AC ST CEIL LO MI. unfold P_OPENSSL_sk_num. acb.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (SKobj_hdr _ _ _ _ SO) as (pad & PL & HDR). unfold sk_hdr_cells, wz in HDR.
    pose proof (rw_cells_bound _ _ _ _ HDR) as HB. cbn [cells_size csize Nat.add] in HB. unfold SK_SIZE in *.
    pose proof SO as SO'. destruct SO' as (_ & POS & _ & NC & CAP & SRT & EL & DAT).
    pose proof (ACONST_shbase m AC) as [GSB SHB]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB. rewrite ASHADOW_BASE_val in SHB.
    pose proof BR1 as (_ & _ & _ & _ & _ & _ & AP1). pose proof (aapp_bounds _ _ AP1 ltac:(lia)) as (_ & _ & AH1 & _). unfold AAPP_HI in AH1.
    pose proof BR1 as (_ & A16 & _). assert (AL : a mod 8 = 0) by (clear - A16; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (ACC0 : accessible m a 56) by (eapply addressable_accessible; [exact SH1| lia| lia| unfold AAPP_HI; lia]).
    pose proof ACC0 as ACC'. clear ACC0. change (id (accessible m a 56)) in ACC'.
    subst a0. carve_frame 16%nat ST.
    do 4 step. step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACC : accessible mx a 56) by (unfold id in ACC'; eapply accessible_across; [exact ACC'| exact MU|]; constructor; [cbn; unfold AHI_LO in *; lia| constructor]) end.
    clear ACC'.
    (* [comment removed for export] *)
    step. ubal_by AL. step. if_lit. step. step. step. zstep. zstep. ck8_check ACC a.
    st1. rewrite sx32_wz by lia. unfold wz. do 5 step.
    release_frame FR ST (bv_unsigned sp). unfold sknull_post. finish.
    eapply ACONST_stack_frame5; [exact AC| exact MU| exact WM| exact CEIL].
  Qed.

  Lemma askvalue_spec : skvalue_stmt H.
  Proof.
    unfold skvalue_stmt. intros until K; intros A0 A1 HI NTH SO [BL1 BL2] [SH1 SH2] [BR1 BR2] AC ST CEIL LO MI. unfold P_OPENSSL_sk_value. acb.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (SKobj_hdr _ _ _ _ SO) as (pad & PL & HDR). unfold sk_hdr_cells, wz in HDR.
    pose proof (rw_cells_bound _ _ _ _ HDR) as HB. cbn [cells_size csize Nat.add] in HB. unfold SK_SIZE in *.
    pose proof SO as SO'. destruct SO' as (_ & POS & _ & NC & CAP & SRT & EL & DAT).
    unfold sk_num, zlength in *. pose proof (nth_error_lt _ _ _ NTH) as IL.
    destruct DAT as [[Z0 _]|(D1 & D2 & D3 & D4 & AR & junk & JK)]; [lia|]. destruct BL2 as [Z0|BL2]; [lia|]. clear JK.
    specialize (SH2 ltac:(lia)). specialize (BR2 ltac:(lia)).
    pose proof (proj1 (Forall_forall _ _) EL p ltac:(eapply nth_error_In; exact NTH)) as PR. cbn in PR.
    pose proof (u64arr_bound _ _ _ _ AR) as ARB. rewrite length_map in ARB.
    pose proof (ACONST_shbase m AC) as [GSB SHB]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB. rewrite ASHADOW_BASE_val in SHB.
    pose proof BR1 as (_ & _ & _ & _ & _ & _ & AP1). pose proof (aapp_bounds _ _ AP1 ltac:(lia)) as (_ & _ & AH1 & _). unfold AAPP_HI in AH1.
    pose proof BR2 as (_ & _ & _ & _ & _ & _ & AP2). pose proof (aapp_bounds _ _ AP2 ltac:(lia)) as (_ & _ & AH2 & _). unfold AAPP_HI in AH2.
    pose proof BR1 as (_ & A16 & _). assert (AL : a mod 8 = 0) by (clear - A16; Z.div_mod_to_equations; lia).
    pose proof BR2 as (_ & D16 & _).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (ACC0 : accessible m a 56) by (eapply addressable_accessible; [exact SH1| lia| lia| unfold AAPP_HI; lia]).
    assert (ACD0 : accessible m (sk_data K) (8 * sk_cap K)) by (eapply addressable_accessible; [exact SH2| lia| lia| unfold AAPP_HI; lia]).
    (* [comment removed for export] *)
    pose proof AR as AR'. clear AR. change (id (u64arr asegs m (sk_data K) (map wz (sk_elems K)))) in AR'.
    pose proof ACC0 as ACC'. clear ACC0. change (id (accessible m a 56)) in ACC'.
    pose proof ACD0 as ACD'. clear ACD0. change (id (accessible m (sk_data K) (8 * sk_cap K))) in ACD'.
    subst a0 a1. carve_frame 16%nat ST.
    do 4 step. step.
    step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit, ?signed_lit by lia. lia. } clear K0.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (AR : u64arr asegs mx (sk_data K) (map wz (sk_elems K)))
        by (unfold id in AR'; eapply u64arr_across; [exact MU| exact WM| rewrite length_map; cbn; lia| exact AR']);
      assert (ACC : accessible mx a 56) by (unfold id in ACC'; eapply accessible_across; [exact ACC'| exact MU|]; constructor; [cbn; unfold AHI_LO in *; lia| constructor]);
      assert (ACD : accessible mx (sk_data K) (8 * sk_cap K)) by (unfold id in ACD'; eapply accessible_across; [exact ACD'| exact MU|]; constructor; [cbn; unfold AHI_LO in *; lia| constructor])
    end.
    clear AR' ACC' ACD'.
    (* [comment removed for export] *)
    step. ubal_by AL. step. if_lit. step. step. step. zstep. zstep. ck8_check ACC a.
    st1. rewrite sx32_wz by lia. unfold wz.
    step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit, ?signed_lit by lia. lia. } clear K0.
    (* [comment removed for export] *)
    zstep. zstep. zstep. ck8_check ACC (a + 8). step.
    (* [comment removed for export] *)
    zstep. zstep. try (rewrite (Z.shiftl_mul_pow2 i 3) by lia; change (2^3) with 8).
    step. ub_dead.
    zstep. zstep. zstep. try (rewrite (Z.shiftl_mul_pow2 i 3) by lia; change (2^3) with 8). rewrite ub_nullcons by lia. step. if_lit.
    step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    step. ubal_by D16. step. if_lit.
    zstep. zstep. ck8_check ACD (sk_data K + i * 8).
    pose proof (u64arr_read asegs _ _ _ i (wz p) (wa (sk_data K + i * 8)) AR ltac:(rewrite nth_error_map, NTH; reflexivity) ltac:(lia) ltac:(f_equal; lia)) as RD.
    unfold wz in RD. step.
    (* [comment removed for export] *)
    do 6 step. release_frame FR ST (bv_unsigned sp). unfold sknull_post. finish.
    eapply ACONST_stack_frame5; [exact AC| exact MU| exact WM| exact CEIL].
  Qed.
End S.
