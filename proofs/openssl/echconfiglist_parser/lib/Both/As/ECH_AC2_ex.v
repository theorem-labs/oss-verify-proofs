(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface ECH_AKit ECH_AsKit
  ECH_AStmt_C0 ECH_AC0_locks ECH_AStmt_C2 ECH_AC2_small.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition GX_RA1 : Z := 0x1f61c4.  Definition GX_RA2 : Z := 0x1f61dc.  Definition SA_JOIN : Z := 0x25326c.

Ltac ret_lit RA := replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
Ltac ret_lit_any := match goal with |- context [ret_pc (Z_to_bv 64 ?r)] => ret_lit r end.
(* [comment removed for export] *)
Ltac acc_now ACC0 ACC MU NSW :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch type of ACC0 with id (accessible _ ?a ?n) =>
      assert (ACC : accessible mx a n) by (unfold id in ACC0; eapply accessible_across; [exact ACC0| exact MU| exact NSW]) end end.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac killa K := exfalso; revert K; rewrite ?land_7, ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac ltu0 :=
    lazymatch goal with |- evt _ _ (MS _ _ (if bv_ltu ?x (Z_to_bv 64 0) then _ else _) _ _ _ _) =>
      replace (bv_ltu x (Z_to_bv 64 0)) with false
        by (rewrite bv_ltu_Z; symmetry; apply Z.ltb_ge; rewrite (unsigned_lit 0) by lia; pose proof (aword_range x); lia);
      cbv iota end.
  Local Ltac ck4_blt_noandi v V1 V2 K :=
    let Ev := fresh "Ev" in let Nv := fresh "Nv" in let VV := fresh "VV" in let KB := fresh "KB" in
    step; destruct (Z.eq_dec v 0) as [Ev|Nv];
    [ if_false_by (ck1_bnez_false v Ev); apply K
    | if_true_by (ck1_bnez_true v V1 Nv); destruct V2 as [VV|VV]; [exfalso; exact (Nv VV)|];
      zstep; step; if_cases KB; zify_cond KB; [clear KB; apply K | killa KB] ].

  Lemma cgetlocalex_spec : cgetlocalex_stmt.
  Proof.
    unfold cgetlocalex_stmt. intros until c. intros exl lo A0 A1 TP CS ES EC CB LS AC ST CEIL LO MI RAE. subst a0 a1.
    unfold P_CRYPTO_THREAD_get_local_ex, CGETLOCALEX_STACK, FR_get_local_ex, FR_CRYPTO_THREAD_get_local_ex, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock,
      CRYPTO_THREAD_LOCAL_ERR_KEY, CRYPTO_THREAD_NO_CONTEXT in *. acb.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(lo, bv_unsigned sp)])
      by (apply Forall_cons; [cbn [fst snd]; unfold AHI_LO, ALOWSH_LO in *; lia| apply Forall_nil]).
    assert (TOPW : Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) [(lo, bv_unsigned sp)])
      by (apply Forall_cons; [cbn [fst snd]; unfold AIMG_TOP in *; lia| apply Forall_nil]).
    (* [comment removed for export] *)
    pose proof (ACONST_shbase m AC) as [GSB SHB0]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    pose proof ES as (_ & E2 & E3 & E4 & _).
    pose proof EC as (I2 & Z2 & K2 & I3 & Z3 & K3 & I4 & Z4 & K4 & I5 & Z5 & I6 & Z6 & RR).
    pose proof (Forall_inv RR) as R2. pose proof (Forall_inv (Forall_inv_tail RR)) as R3.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail RR))) as R4. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail RR)))) as R5.
    unfold arange in R2, R3, R4, R5. unfold chain_below, ERRST_SIZE in CB.
    (* [comment removed for export] *)
    pose proof (proj1 (Forall_forall _ _) LS _ I2) as ADmk. pose proof (proj1 (Forall_forall _ _) LS _ I3) as ADsa. pose proof (proj1 (Forall_forall _ _) LS _ I4) as ADnd.
    cbv beta in ADmk, ADsa, ADnd. rewrite Z2 in ADmk. rewrite Z3 in ADsa. rewrite Z4 in ADnd.
    set (mk := blk_addr (ec_mkey c)) in *. set (sa := blk_addr (ec_sa c)) in *. set (nd := blk_addr (ec_nodes c)) in *. set (es := blk_addr (ec_es c)) in *.
    unfold AAPP_HI in *.
    assert (ACCmk : id (accessible m mk 72)) by (eapply addressable_accessible; [exact ADmk| lia| lia| unfold AAPP_HI; lia]).
    assert (ACCsa : id (accessible m sa 32)) by (eapply addressable_accessible; [exact ADsa| lia| lia| unfold AAPP_HI; lia]).
    assert (ACCnd : id (accessible m nd 128)) by (eapply addressable_accessible; [exact ADnd| lia| lia| unfold AAPP_HI; lia]).
    clear ADmk ADsa ADnd LS.
    unfold wz, O_MKEY_ERR, sa_cells, LIBKEY0, A_master_once, A_master_key, A_tsd_main in *.
    pose proof (rw_cells_bound _ _ _ _ K2) as KB2. pose proof (rw_cells_bound _ _ _ _ K3) as KB3. pose proof (rw_cells_bound _ _ _ _ K4) as KB4.
    cbn [cells_size csize Nat.add length] in KB2, KB3, KB4.
    carve_frame 48%nat ST.
    do 7 st1.
    (* [comment removed for export] *)
    step. st1. st1. step. step. step. try if_true. step. step. step. step. step. step.
    eapply evt_cut.
    { eapply crunonce_spec with (lo := lo) (rest := []);
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption;
        try (unfold CRUNONCE_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock; lia); try reflexivity. }
    intros ms' PO. unfold c2_post in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU' & WM' & MI' & ST' & _).
    ret_lit_any.
    rewrite unsigned_lit in MU', ST' by lia. carry MU' WM'. extend_munch MU WM MU' WM'. clear MI ST. rename MI' into MI. rename ST' into ST.
    (* [comment removed for export] *)
    step. step. try if_false. step. try if_false. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACx : ACONST mx) by (eapply ACONST_stack_frame; [exact AC| exact MU| exact WM| exact CEIL]);
      assert (ACK : accessible mx 0xbdd040 4)
        by (assert (IN : In (0xbdd040, 4, 8) aglobals) by (unfold aglobals; cbn; tauto);
            pose proof (ACONST_global_addressable mx 0xbdd040 4 8 ACx IN ltac:(lia)) as AD;
            eapply addressable_accessible; [exact AD| lia| lia| unfold AAPP_HI; lia]);
      assert (TD : rw_cells asegs mx A_td_tsd [C8 (wz A_tsd_main)])
        by (apply (ACONST_cell mx _ _ ACx); unfold aconst_cells; cbn; tauto) end.
    eapply evt_cut.
    { eapply cgetlocal_spec with (lo := lo) (rest := []);
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption;
        try (unfold CGETLOCAL_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock, ALOWSH_LO, AHI_LO; lia); try reflexivity. }
    clear ACx ACK TD.
    intros ms' PO. unfold c2_post in PO.
    destruct PO as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m'' & -> & MU'' & WM'' & MI'' & ST'' & _).
    ret_lit_any.
    rewrite unsigned_lit in MU'', ST'' by lia. carry MU'' WM''. extend_munch MU WM MU'' WM''. clear MI ST. rename MI'' into MI. rename ST'' into ST.
    (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [kill K0|]; clear K0.
    step. change (Z.shiftl 3 3) with 24. zstep. step. ub_dead. step. ubal_by R2. step. if_lit. zstep. zstep.
    acc_now ACCmk ACC MU NSW. ck8_check ACC (mk + 24). clear ACC.
    st1. step. if_cases K0; zify_cond K0; [kill K0|]; clear K0.
    step. if_cases K0; zify_cond K0; [kill K0|]; clear K0.
    step. step. do 5 st1. step. step.
    release_frame FR ST (bv_unsigned sp).
    (* [comment removed for export] *)
    carve_frame 16%nat ST.
    do 4 st1. step. if_cases K0; zify_cond K0; [kill K0|]; clear K0.
    step. ubal_by R3. step. if_lit.
    step. st1. st1.
    (* [comment removed for export] *)
    zstep. zstep. zstep. acc_now ACCsa ACC MU NSW. ck8_check ACC (sa + 16).
    st1. step. try if_false.
    (* [comment removed for export] *)
    zstep. zstep. zstep. ck8_check ACC (sa + 8).
    st1. step. first [if_true | if_lit].
    (* [comment removed for export] *)
    zstep. zstep. ck4_load ACC sa sv V1 V2 Hsa.
    lazymatch goal with |- evt _ ?P (MS (mkR ?ra_ ?sp_ ?gp_ ?tp_ ?t0_ ?t1_ ?t2_ ?s0_ ?s1_ ?a0_ ?a1_ _ ?a3_ _ ?a5_ ?a6_ ?a7_ ?s2_ ?s3_ ?s4_ ?s5_ ?s6_ ?s7_ ?s8_ ?s9_ ?s10_ ?s11_ ?t3_ ?t4_ ?t5_ ?t6_) ?F_ _ ?fc_ _ ?mx ?rom) =>
    assert (FIN : forall a2x a4x : word,
      evt asegs P (MS (mkR ra_ sp_ gp_ tp_ t0_ t1_ t2_ s0_ s1_ a0_ a1_ a2x a3_ a4x a5_ a6_ a7_ s2_ s3_ s4_ s5_ s6_ s7_ s8_ s9_ s10_ s11_ t3_ t4_ t5_ t6_)
                       F_ (Z_to_bv 64 SA_JOIN) fc_ None mx rom)) end.
    { intros a2x a4x. unfold SA_JOIN.
      (* [comment removed for export] *)
      st1. change (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1). step. step. if_lit.
      zstep. zstep. zstep. ck8_check ACC (sa + 24). clear ACC.
      st1. step. if_cases K0; zify_cond K0; [kill K0|]; clear K0.
      step. if_lit.
      (* [comment removed for export] *)
      step. if_cases K0; zify_cond K0; [kill K0|]; clear K0.
      step. step. step. step. ltu0. zstep. step. ubal_by R4. step. if_lit. zstep. zstep.
      acc_now ACCnd ACC MU NSW. ck8_check ACC nd. clear ACC.
      st1. st1. st1. step. step.
      release_frame FR ST (bv_unsigned sp). finish.
      - eapply CTX_statics_across; [exact CS| exact MU| exact WM| exact TOPW].
      - eapply ERR_statics_across; [exact ES| exact MU| exact WM| exact TOPW].
      - unfold ERR_chain. subst mk sa nd es. unfold O_MKEY_ERR, sa_cells, wz.
        repeat match goal with |- _ /\ _ => split end; try assumption. }
    ck4_blt_noandi sv V1 V2 FIN.
  Qed.
End S.
