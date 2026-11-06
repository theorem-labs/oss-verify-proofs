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
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_Rep ECH_LibState ECH_C0_stmt ECH_C0_locks ECH_C1_stmt ECH_C2_stmt ECH_C2_small ECH_C2_ex ECH_LibFrame ECH_C4_stmt ECH_C4_frame ECH_UbKit.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac unfold_lib_addrs := unfold wz, O_MKEY_ERR, A_master_once_ret, A_tsd_main, A_stopped, A_base_once, A_load_strings_once, A_optsdone, A_destructor_key,
  A_err_string_once, A_tevent_once, A_keys, A_next_key, A_key_lock, A_td_cancelbuf, A_td_tsd_used, A_base_inited, A_in_init_config_key, A_optsdone_lock,
  A_defctx_inited, A_defctx_exlock, A_defctx_exmeth_bio, A_td_tsd, A_defctx in *.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  Lemma egs_ready_spec : egs_ready_stmt.
  Proof.
    unfold egs_ready_stmt. intros until errv. intros A0 SV TP ERR CS ES EC CB ST CEIL LO MI RAE. subst a0.
    unfold P_ossl_err_get_state_int, EGS_STACK, FR_ossl_err_get_state_int, CINITCRYPTO_STACK, FR_OPENSSL_init_crypto, FR_CRYPTO_THREAD_wrap,
      FR_CRYPTO_THREAD_read_lock in *. hcb.
    pose proof (word_range sp) as SPR. pose proof (word_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    subst tp. rewrite errno_RATP in *. unfold RERRNO in *.
    pose proof (munch_refl [(lo, bv_unsigned sp); (3366900, 3366900 + 4)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof CS as CS0. pose proof ES as ES0. pose proof EC as EC0.
    assert (ESR : 0 < blk_addr (ec_es c) /\ blk_addr (ec_es c) + 904 <= lo).
    { destruct EC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RR).
      pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail RR)))) as R5. unfold rblock_range in R5.
      unfold chain_below, ERRST_SIZE in CB. lia. }
    carve_frame 48%nat ST. do 6 st1. step. step. step.
    if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      subst save. step. step. step. step.
      pose proof (ERR_statics_munch _ _ _ _ ES0 MU WM ltac:(libx_windows)) as ESc.
      eapply evt_cut.
      { spec_as Q cinitcrypto_spec. eapply Q with (lo := lo) (c := c); clear Q; try reflexivity; try (rewrite unsigned_lit by lia); try eassumption;
          try (unfold CINITCRYPTO_STACK, FR_OPENSSL_init_crypto, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock; lia). }
      land MU WM. clear ESc.
      (* [comment removed for export] *)
      step. try if_lit. step. step. step.
      pose proof (CTX_statics_munch _ _ _ _ CS0 MU WM ltac:(libx_windows)) as CSc.
      pose proof (ERR_statics_munch _ _ _ _ ES0 MU WM ltac:(libx_windows)) as ESc.
      pose proof (ERR_chain_munch _ _ _ _ _ _ EC0 CB MU WM ltac:(chain_windows)) as ECc.
      eapply evt_cut.
      { spec_as Q cgetlocalex_spec. eapply Q with (lo := lo) (c := c) (exl := exl) (LIB := LB); clear Q; try reflexivity; try (rewrite unsigned_lit by lia); try eassumption;
          try (unfold CGETLOCALEX_STACK, FR_get_local_ex, FR_CRYPTO_THREAD_get_local_ex, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock; lia). }
      land MU WM. clear CSc ESc ECc.
      (* [comment removed for export] *)
      step. step. if_cases K1; zify_cond K1; [kill K1|]; clear K1.
      step. step. if_cases K1; zify_cond K1; [|kill K1]; clear K1.
      step. if_lit.
      step. do 5 st1. step. step.
      release_frame FR ST (bv_unsigned sp). finish.
    - (* [comment removed for export] *)
      step. step.
      eapply evt_cut.
      { spec_as Q errnoloc_spec. eapply Q; clear Q; try reflexivity; try eassumption. }
      intros ms' ->. replace (ret_pc (Z_to_bv 64 935976)) with (Z_to_bv 64 935976) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold RERRNO.
      step. try if_lit. step. step. try if_lit.   (* [comment removed for export] *)
      st1. step.
      (* [comment removed for export] *)
      step. step. step.
      pose proof (ERR_statics_munch _ _ _ _ ES0 MU WM ltac:(libx_windows)) as ESc.
      eapply evt_cut.
      { spec_as Q cinitcrypto_spec. eapply Q with (lo := lo) (c := c); clear Q; try reflexivity; try (rewrite unsigned_lit by lia); try eassumption;
          try (unfold CINITCRYPTO_STACK, FR_OPENSSL_init_crypto, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock; lia). }
      land MU WM. clear ESc.
      step. try if_lit. step. step. step.
      pose proof (CTX_statics_munch _ _ _ _ CS0 MU WM ltac:(libx_windows)) as CSc.
      pose proof (ERR_statics_munch _ _ _ _ ES0 MU WM ltac:(libx_windows)) as ESc.
      pose proof (ERR_chain_munch _ _ _ _ _ _ EC0 CB MU WM ltac:(chain_windows)) as ECc.
      eapply evt_cut.
      { spec_as Q cgetlocalex_spec. eapply Q with (lo := lo) (c := c) (exl := exl) (LIB := LB); clear Q; try reflexivity; try (rewrite unsigned_lit by lia); try eassumption;
          try (unfold CGETLOCALEX_STACK, FR_get_local_ex, FR_CRYPTO_THREAD_get_local_ex, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock; lia). }
      land MU WM. clear CSc ESc ECc.
      step. step. if_cases K1; zify_cond K1; [kill K1|]; clear K1.
      step. step. if_cases K1; zify_cond K1; [|kill K1]; clear K1.
      (* [comment removed for export] *)
      step. if_cases K1; zify_cond K1; [kill K1|]; clear K1.
      step. step.
      eapply evt_cut.
      { spec_as Q errnoloc_spec. eapply Q; clear Q; try reflexivity; try eassumption. }
      intros ms' ->. replace (ret_pc (Z_to_bv 64 936148)) with (Z_to_bv 64 936148) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold RERRNO.
      step. try if_lit. step. step. try if_lit.   (* [comment removed for export] *)
      st1. step.
      step. do 5 st1. step. step.
      release_frame FR ST (bv_unsigned sp). finish.
      + rewrite unsigned_lit by (unfold RATP; lia). unfold RATP. apply (rw_cells_C4_sx32 usegs _ _ [] errv []). exact ERR.
      + eapply CTX_statics_munch; [exact CS0| exact MU| exact WM| libx_windows].
      + eapply ERR_statics_munch; [exact ES0| exact MU| exact WM| libx_windows].
      + eapply ERR_chain_munch; [exact EC0| exact CB| exact MU| exact WM| chain_windows].
  Qed.
End S.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.
  Hypothesis O3 : egs_fresh_stmt H.

  Lemma egs_spec : egs_stmt H.
  Proof.
    intros ph E. destruct ph as [|c].
    { unfold egs_stmt_for. intros until errv. intros A0 SV SVF HP KREL BY CN BG AUX SPB SPA ST CEIL LO ERR MI TP MF IM GM RL EP EX EB CP RAE.
      cbn [ERRX] in EX. subst E. eapply O3; eassumption || (cbn [ERRX]; reflexivity). }
    unfold egs_stmt_for. intros until errv. intros A0 SV SVF HP KREL BY CN BG AUX SPB SPA ST CEIL LO ERR MI TP MF IM GM RL EP EX EB CP RAE.
    cbn [ERRPH ERRX errph_below errph_stack CTXPH] in *. destruct EP as [ES EC]. destruct CP as [CS CBK].
    assert (STK0 : 0 <= EGS_STACK) by (unfold EGS_STACK, FR_ossl_err_get_state_int, CINITCRYPTO_STACK, FR_OPENSSL_init_crypto, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock; lia).
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (SUB : forall b, In b LB -> In b (blocks_ERRST E ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
    assert (RBL : forall b, In b LB -> rblock_range (blk_addr b) (blk_size b)).
    { intros b Hb. eapply (HH_RHEAP_block_range H HH); [exact HP| apply SUB; exact Hb]. }
    eapply (sr_evt_krel H HH); [exact KREL| eapply egs_ready_spec with (lo := lo) (c := c) (exl := x) (LB := LB) (save := save) (errv := errv); eassumption|].
    intros ms1 PO. unfold egsr_post in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1 & ST1 & ERR1 & CS1 & ES1 & EC1).
    assert (FW : Forall stack_or_errno [(lo, bv_unsigned sp); (RERRNO, RERRNO + 4)]).
    { constructor; [left; cbn; lia|]. constructor; [right; cbn; lia| constructor]. }
    assert (CW1 : C4W LB m1 (ErrReady c) x).
    { eapply C4W_stack; [| exact MU1| exact WM1| exact FW| exact RBL]. unfold C4W. cbn [ERRPH CTXPH]. tauto. }
    destruct CW1 as (MF1 & IM1 & GM1 & RL1 & EP1 & CP1).
    assert (ESB : 0 < blk_addr (ec_es c) /\ blk_addr (ec_es c) + 904 <= lo /\ (blk_addr (ec_es c) + 904 <= 65536 \/ 3506176 <= blk_addr (ec_es c))).
    { destruct EC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _). pose proof (RBL _ I5) as R5. unfold rblock_range in R5. rewrite Z5 in R5.
      unfold chain_below, ERRST_SIZE in *. lia. }
    apply (sr_done H HH). unfold egs_post. cbn [cfg_ms cfg_model].
    exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m1, errv, s, (@nil block), c.
    split; [reflexivity|]. split; [apply (mpres_refl H HH)|].
    split.
    { unfold c4_frame. cbn [app cfg_model]. split; [exact KREL|]. split; [exact MI1|]. split; [exact ST1|].
      split. { eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]. unfold RAUXV_CELL, RERRNO.
               constructor; [cbn; lia|]. constructor; [cbn; lia| constructor]. }
      split. { eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|].
               constructor; [left; cbn; lia|]. constructor; [| constructor]. right; left. unfold RERRNO, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RVMLOCK. cbn. lia. }
      tauto. }
    split; [exact ERR1|]. split; [intros _; reflexivity|].
    split; [cbn [errph_delta]; split; reflexivity|].
    cbn [app]. split; [exact EP1|]. split; [exact CP1|].
    split.
    { eapply ERRST_munch; [exact EX| exact MU1| exact WM1|]. unfold ERRST_SIZE, RERRNO. cbn. lia. }
    eapply xpres_of_munch_gen; [exact MU1| exact WM1|].
    intros a Ha [HC _]. unfold RERRNO. cbn. split; [| split; [| exact I]].
    - destruct HC as [K|[[K _]|(b & Hb & Hr)]]; [lia| lia|]. pose proof (RBL b Hb) as RB. unfold rblock_range in RB. lia.
    - destruct HC as [K|[[_ K]|(b & Hb & Hr)]]; [lia| unfold ralloc_static, RERRNO in K; lia|]. pose proof (RBL b Hb) as RB. unfold rblock_range in RB. lia.
  Qed.
End W.
