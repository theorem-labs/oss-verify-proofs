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
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_Rep ECH_LibState ECH_C0_stmt ECH_C1_stmt ECH_C2_stmt ECH_LibFrame ECH_C4_stmt ECH_C4_rep ECH_C4_egs ECH_UbKit.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  Lemma errseterr_spec : errseterr_stmt.
  Proof.
    unfold errseterr_stmt. intros until errv. intros A0 A1 A2 LIBR LIB2 REAS TP ERR CS ES EC CB CSEP EST ST CEIL LO MI RAE. subst a0 a1 a2.
    unfold P_ERR_set_error, ERRSETERR_STACK, FR_ERR_set_error, FR_ERR_vset_error, EGS_STACK, FR_ossl_err_get_state_int, CINITCRYPTO_STACK, FR_OPENSSL_init_crypto,
      FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock in *. hcb.
    pose proof (word_range sp) as SPR. pose proof (word_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    subst tp. rewrite errno_RATP in *. unfold RERRNO in *.
    pose proof CS as CS0. pose proof ES as ES0. pose proof EC as EC0.
    assert (ESR : 0 < blk_addr (ec_es c) /\ blk_addr (ec_es c) + 904 <= lo /\ (blk_addr (ec_es c) + 904 <= 65536 \/ 3506176 <= blk_addr (ec_es c))).
    { destruct EC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Z5 & _ & _ & RR).
      pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail RR)))) as R5. unfold rblock_range in R5. rewrite Z5 in R5.
      unfold chain_below, ERRST_SIZE in *. lia. }
    assert (ESAL : blk_addr (ec_es c) mod 8 = 0).
    { destruct EC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Z5 & _ & _ & RR).
      pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail RR)))) as R5. unfold rblock_range in R5. clear - R5. lia. }
    set (es := blk_addr (ec_es c)) in *.
    pose proof (munch_refl [(lo, bv_unsigned sp); (3366900, 3366900 + 4); (es, es + ERRST_SIZE)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold ERRST_SIZE in MU.
    (* [comment removed for export] *)
    pose proof EST as EST0. unfold ERRST in EST. fold es in EST.
    destruct EST as (SL & TR & BR & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & TB & OWN).
    unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP in *.
    set (top := es_top E) in *. arr_lens SL.
    (* [comment removed for export] *)
    carve_frame 80%nat ST. do 3 st1. step. do 5 st1. step. st1. step.
    (* [comment removed for export] *)
    carve_frame 96%nat ST. do 13 st1. step. step. step. step. step. step. step.
    pose proof (CTX_statics_munch _ _ _ _ CS0 MU WM ltac:(libx_windows)) as CSc.
    pose proof (ERR_statics_munch _ _ _ _ ES0 MU WM ltac:(libx_windows)) as ESc.
    pose proof (ERR_chain_munch _ _ _ _ _ _ EC0 CB MU WM ltac:(chain_windows)) as ECc.
    eapply evt_cut.
    { spec_as Q egs_ready_spec. eapply Q with (lo := lo) (c := c) (exl := exl) (LB := LB) (save := 1) (errv := errv); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia;
        try (unfold EGS_STACK, FR_ossl_err_get_state_int, CINITCRYPTO_STACK, FR_OPENSSL_init_crypto, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock; lia).
    }
    intros ms_ PO_; unfold egsr_post, RERRNO in PO_; revert ms_ PO_.
    land MU WM. clear CSc ESc ECc. fold es.
    match goal with K : rw_cells _ _ (bv_unsigned (Z_to_bv 64 RATP) + -164) _ |- _ => change (bv_unsigned (Z_to_bv 64 RATP) + -164) with 3366900 in K; rename K into ERR end.
    (* [comment removed for export] *)
    step. if_cases K1; zify_cond K1; [kill K1|]; clear K1.
    step. step. ubal_by ESAL. step. if_lit.
    st1. rewrite sx32_wz by lia. unfold wz. zstep. zstep. step. try if_lit. step. step. step. step.
    (* [comment removed for export] *)
    step. step. ub_dead_by (clear - TR). zstep. shl_norm. zstep. step. ub_dead_by (clear - TR ESR LO SPR).
    replace (es + 512 + top * 4) with (es + 512 + top * 4) by lia.
    pose proof (zero16_byte_m _ _ top F6 TR) as RD. replace (es + 512 + top * 4) with (es + 512 + top * 4) in RD by lia. step. clear RD. nrm. unfold wz.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shl_norm. zstep. step. try if_lit.
    (* [comment removed for export] *)
    step. ubnot. step. ub_dead_by (clear - TR ESR LO SPR). step. ubnot.
    arr_store64 F4 top (wz 0). rewrite upd_zero16 in F4 by lia.
    step. ub_dead_by (clear - TR ESR LO SPR). step. zstep.
    arr_store64 F5 top (wz 0). rewrite upd_zero16 in F5 by lia.
    step. ub_dead2.
    (* [comment removed for export] *)
    arr_store32 F6 top (wz 0). rewrite upd_zero16 in F6 by lia.
    st1. rewrite sx32_wz by lia. unfold wz. step. step.
    if_cases K1; zify_cond K1; [|kill K1]; clear K1.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. shl_norm.
    (* [comment removed for export] *)
    step. step. ub_dead_by (clear - TR). zstep. zstep. shl_norm. step. ubnot. step. ub_dead_by (clear - TR ESR LO SPR). zstep.
    zstep. zstep. shl_norm.
    rewrite (err_pack_reg lib reason) by lia.
    arr_store64 F3 top (wz (ERR_PACK lib reason)).
    (* [comment removed for export] *)
    step. try if_lit. do 12 st1. step. step.
    release_frame FR0 ST (bv_unsigned sp + -80).
    do 2 st1. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
    - eapply CTX_statics_munch; [exact CS0| exact MU| exact WM|]. subst es. libx_windows.
    - eapply ERR_statics_munch; [exact ES0| exact MU| exact WM|]. subst es. libx_windows.
    - eapply ERR_chain_munch; [exact EC0| exact CB| exact MU| exact WM|]. subst es. chain_windows.
    - (* [comment removed for export] *)
      assert (TN : (Z.to_nat top < length (es_slots E))%nat) by lia.
      unfold ERRST, errst_seterr. fold es. fold top. cbn [es_slots es_top es_bottom].
      unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP.
      rewrite !map_slot_upd by exact TN. cbn [sl_flags sl_buffer sl_file sl_line sl_func].
      rewrite (upd_same (map (fun s => wz (sl_flags s)) (es_slots E))), (upd_same (map (fun s => wz (sl_file s)) (es_slots E))),
              (upd_same (map (fun s => wz (sl_line s)) (es_slots E))), (upd_same (map (fun s => wz (sl_func s)) (es_slots E)))
        by (apply slot_nth; [exact SL| lia]).
      split; [rewrite slot_upd_length by exact TN; exact SL|]. split; [exact TR|]. split; [exact BR|].
      repeat match goal with |- _ /\ _ => split end; try assumption.
      apply own_slot_upd; [exact OWN|].
      pose proof (slot_at_own _ E top OWN SL TR) as (O1 & O2 & O3 & O4 & O5). cbn [sl_flags sl_buffer sl_file sl_file_o sl_line sl_func sl_func_o].
      pose proof (err_pack_range lib reason LIBR REAS). repeat split; try assumption; lia.
  Qed.
End S.
