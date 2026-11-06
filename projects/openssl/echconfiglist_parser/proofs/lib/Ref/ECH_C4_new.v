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
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_Rep ECH_LibState
     ECH_C0_stmt ECH_C1_stmt ECH_C1_malloc ECH_C1_free ECH_C1_freeopt ECH_C2_stmt ECH_LibFrame ECH_C4_stmt ECH_C4_rep ECH_C4_frame ECH_C4_egs.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  Definition en_frame (s2 s1 s0 ra : word) : list cell := [C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition EN_RA1 : Z := 0xdef10.   (* [comment removed for export] *)
  Definition EN_L1 : Z := 0xdef64.    (* [comment removed for export] *)
  Definition EN_RA2 : Z := 0xdefd0.   (* [comment removed for export] *)
  Definition EN_RA3 : Z := 0xdefe4.   (* [comment removed for export] *)
  Definition EN_FILE : Z := 0x33ad3.  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition en_E0 (E : errst) : errst :=
    let t := err_next (es_top E) in mkERRST (es_slots E) t (if t =? es_bottom E then err_next (es_bottom E) else es_bottom E).

  (* [comment removed for export] *)
  Lemma en_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 EN_RA1) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_ossl_err_get_state_int) fc None m1 (seg_rom rsegs)
          /\ munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ stk rsegs m1 lo (bv_unsigned sp + -32)
          /\ rw_cells rsegs m1 (bv_unsigned sp + -32) (en_frame s2 s1 s0 ra))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_ERR_new) fc None m (seg_rom rsegs)).
  Proof.
    intros until lo. intros ST CEIL LO MI. unfold P_ERR_new, P_ossl_err_get_state_int, EN_RA1, en_frame. hcb.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    carve_frame 32%nat ST. do 5 st1. step. step. step. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma en_seg2a :
    forall (ra0 sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (es : Z) (E : errst),
      ERRSTm m es E -> 0 < es -> es + 904 < 2^64 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists a1' a3' m1,
          ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 es) a1' (Z_to_bv 64 (err_next (es_top E))) a3' a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 EN_L1) fc None m1 (seg_rom rsegs)
          /\ munch [(es, es + 904)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\ ERRSTm m1 es (en_E0 E))
        (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 es) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 EN_RA1)) fc None m (seg_rom rsegs)).
  Proof.
    intros until E. intros EST POS BL MI. unfold EN_RA1, EN_L1.
    replace (ret_pc (Z_to_bv 64 0xdef10)) with (Z_to_bv 64 0xdef10) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (munch_refl [(es, es + 904)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    unfold ERRSTm in EST. destruct EST as (SL & TR & BR & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & TB & RG).
    unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP in *.
    set (top := es_top E) in *. set (bot := es_bottom E) in *. arr_lens SL.
    step. if_cases K1; zify_cond K1; [kill K1|]; clear K1.
    st1. rewrite sx32_wz by lia. st1. rewrite sx32_wz by lia. unfold wz.
    zstep. zstep. zstep. zstep. zstep. zstep.
    rewrite (err_next_reg top) by lia. pose proof (err_next_range top TR) as TR'. set (t' := err_next top) in *.
    st1. step.
    if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      finish. unfold ERRSTm, en_E0. fold top. fold bot. fold t'. cbn [es_slots es_top es_bottom].
      replace (t' =? bot) with false by (symmetry; apply Z.eqb_neq; exact K1).
      unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP, wz.
      repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      rewrite (err_next_reg8 t') by lia. st1.
      finish. unfold ERRSTm, en_E0. fold top. fold bot. fold t'. cbn [es_slots es_top es_bottom].
      replace (t' =? bot) with true by (symmetry; apply Z.eqb_eq; exact K1). rewrite <- K1.
      pose proof (err_next_range t' TR').
      unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP, wz.
      repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma en_seg2b :
    forall (ra0 sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (es t : Z) (E : errst),
      ERRSTm m es E -> 0 <= t < 16 -> 0 < es -> es + 904 < 2^64 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists a3' m1,
          ms' = MS (mkR (Z_to_bv 64 EN_RA2) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 EN_FILE) (Z_to_bv 64 (sl_file (slot_at E t))) (Z_to_bv 64 EN_FILE)
                       (Z_to_bv 64 112) a3' a4 a5 a6 a7 (Z_to_bv 64 (es + t * 8)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m1 (seg_rom rsegs)
          /\ munch [(es, es + 904)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ ERRSTm m1 es (es_with_slot E t (slot_wipe (slot_at E t))))
        (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 es) a1 (Z_to_bv 64 t) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 EN_L1) fc None m (seg_rom rsegs)).
  Proof.
    intros until E. intros EST TR' POS BL MI. unfold EN_RA2, EN_L1, EN_FILE, P_CRYPTO_free.
    pose proof (munch_refl [(es, es + 904)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    unfold ERRSTm in EST. destruct EST as (SL & TR & BR & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & TB & RG).
    unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP in *.
    arr_lens SL.
    (* [comment removed for export] *)
    zstep. zstep. shl_norm.
    pose proof (zero16_byte_m _ _ t F6 TR') as RD. step. clear RD. nrm. unfold wz.
    zstep. zstep. zstep. shl_norm. step. try if_lit.
    (* [comment removed for export] *)
    step. arr_store64 F4 t (wz 0). rewrite upd_zero16 in F4 by lia.
    arr_store64 F5 t (wz 0). rewrite upd_zero16 in F5 by lia.
    step. arr_store32 F6 t (wz 0). rewrite upd_zero16 in F6 by lia.
    step. arr_store32 F8 t (Z_to_bv 64 (-1)). apply (u32arr_upd_le4 _ _ _ _ _ _ le4_minus1) in F8.
    (* [comment removed for export] *)
    pose proof (u64arr_read_m _ _ _ t _ F7 (slot_nth E t (fun s => wz (sl_file s)) SL TR') ltac:(lia)) as RD. step. clear RD.
    arr_store32 F2 t (wz 0). rewrite upd_zero16 in F2 by lia.
    arr_store32 F1 t (wz 0). arr_store64 F3 t (wz 0).
    (* [comment removed for export] *)
    step. step. step. step. step.
    finish.
    eapply (ERRSTm_with_slot _ es E t (slot_wipe (slot_at E t))); try eassumption; try reflexivity;
      try (upd_keep_tac E t SL TR'); cbn [slot_wipe sl_flags sl_buffer sl_line]; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma en_seg3 :
    forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (es t : Z) (E : errst),
      ERRSTm m es E -> 0 <= t < 16 -> 0 < es -> es + 904 < 2^64 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 EN_RA3) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 EN_FILE) (Z_to_bv 64 (sl_func (slot_at E t))) (Z_to_bv 64 EN_FILE)
                       (Z_to_bv 64 114) a3 a4 a5 a6 a7 (Z_to_bv 64 (es + t * 8)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m1 (seg_rom rsegs)
          /\ munch [(es, es + 904)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ ERRSTm m1 es (es_with_slot E t (slot_file0 (slot_at E t))))
        (MS (mkR (Z_to_bv 64 EN_RA2) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 EN_FILE) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (es + t * 8))
                 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 EN_RA2)) fc None m (seg_rom rsegs)).
  Proof.
    intros until E. intros EST TR' POS BL MI. unfold EN_RA2, EN_RA3, EN_FILE, P_CRYPTO_free.
    replace (ret_pc (Z_to_bv 64 0xdefd0)) with (Z_to_bv 64 0xdefd0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (munch_refl [(es, es + 904)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    unfold ERRSTm in EST. destruct EST as (SL & TR & BR & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & TB & RG).
    unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP in *.
    arr_lens SL.
    pose proof (u64arr_read_m _ _ _ t _ F9 (slot_nth E t (fun s => wz (sl_func s)) SL TR') ltac:(lia)) as RD. step. clear RD.
    arr_store64 F7 t (wz 0).
    step. step. step.
    finish.
    pose proof (slot_at_own _ E t RG SL TR') as (O1 & O2 & O3).
    eapply (ERRSTm_with_slot _ es E t (slot_file0 (slot_at E t))); try eassumption; try reflexivity;
      try (upd_keep_tac E t SL TR'); cbn [slot_file0 sl_flags sl_buffer sl_line]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma en_seg4 :
    forall (sp gp tp t0 t1 t2 s0x a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (es t lo : Z) (E : errst),
      ERRSTm m es E -> 0 <= t < 16 -> 0 < es -> es + 904 <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv rsegs m ->
      stk rsegs m lo (bv_unsigned sp + -32) -> rw_cells rsegs m (bv_unsigned sp + -32) (en_frame s2 s1 s0 ra) ->
      evt rsegs (fun ms' => exists m1,
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m1 (seg_rom rsegs)
          /\ munch [(es, es + 904)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\ stk rsegs m1 lo (bv_unsigned sp)
          /\ ERRSTm m1 es (es_with_slot E t (slot_func0 (slot_at E t))))
        (MS (mkR (Z_to_bv 64 EN_RA3) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0x (Z_to_bv 64 EN_FILE) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 (es + t * 8)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 EN_RA3)) fc None m (seg_rom rsegs)).
  Proof.
    intros until E. intros EST TR' POS BL LO MI ST FR. unfold EN_RA3, EN_FILE, en_frame in *.
    replace (ret_pc (Z_to_bv 64 0xdefe4)) with (Z_to_bv 64 0xdefe4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(es, es + 904)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    unfold ERRSTm in EST. destruct EST as (SL & TR & BR & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & TB & RG).
    unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP in *.
    arr_lens SL.
    arr_store64 F9 t (wz 0).
    do 4 st1. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
    pose proof (slot_at_own _ E t RG SL TR') as (O1 & O2 & O3).
    eapply (ERRSTm_with_slot _ es E t (slot_func0 (slot_at E t))); try eassumption; try reflexivity;
      try (upd_keep_tac E t SL TR'); cbn [slot_func0 sl_flags sl_buffer sl_line]; lia.
  Qed.
End S.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HX : heap_sr_hyps_x H.
  Hypothesis EGS : egs_stmt H.
  Let HH : heap_sr_hyps H := proj1 HX.
  Let PERM : RHEAP_perm_law H := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HX))))).

  Lemma errnew_spec : errnew_stmt H.
  Proof.
    unfold errnew_stmt. intros until errv. intros HP KREL BY CN BG AUX SPB SPA ST CEIL LO ERR MI TP MF IM GM RL EP EX EB CP RAE.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (STK1 : 32 + errph_stack ph <= bv_unsigned sp - lo /\ 32 + 8208 <= bv_unsigned sp - lo).
    { unfold ERRNEW_STACK, FR_ERR_new, CFREE_STACK, RFREE_STACK in LO. destruct ph; cbn [errph_stack] in *;
        unfold ERRINIT_STACK, EGS_STACK, FR_ossl_err_get_state_int, CINITCRYPTO_STACK, FR_OPENSSL_init_crypto, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock, RREALLOC_STACK in *; lia. }
    set (SB := blocks_ERRST E) in *.
    assert (SUBx : forall b, In b LB -> In b (SB ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
    assert (RBL : forall b, In b LB -> rblock_range (blk_addr b) (blk_size b)).
    { intros b Hb. eapply (HH_RHEAP_block_range H HH); [exact HP| apply SUBx; exact Hb]. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply en_seg1 with (lo := lo); [exact ST| exact CEIL| lia| exact MI]|].
    intros ms1 (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (HP1 : hs_RHEAP H s (SB ++ LB) m1).
    { eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (AUX1 : hs_rauxv_ok H m1 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]. unfold RAUXV_CELL. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    subst tp. rewrite errno_RATP in ERR.
    apply (rw_cells_transport rsegs _ m m1 _ _ ERR) in MU1 as ERR1; [| exact WM1| unfold RERRNO; cbn; lia].
    assert (CW1 : C4W LB m1 ph x).
    { eapply C4W_stack; [| exact MU1| exact WM1| | exact RBL]; [unfold C4W; tauto|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    destruct CW1 as (MF1 & IM1 & GM1 & RL1 & EP1 & CP1).
    assert (EX1 : ERRX m1 ph E).
    { destruct ph as [|c0]; cbn [ERRX errph_below] in *; [exact EX|].
      eapply ERRST_munch; [exact EX| exact MU1| exact WM1|]. unfold chain_below, ERRST_SIZE in *. cbn. lia. }
    assert (XP01 : xpres LB (bv_unsigned sp) (ERR_X ++ errph_foot ph) m m1).
    { eapply xpres_of_munch; [exact MU1| exact WM1| |]; [apply Forall_cons; [left; cbn; lia| apply Forall_nil]|].
      intros b Hb. pose proof (RBL b Hb) as RB. unfold rblock_range in RB. lia. }
    (* [comment removed for export] *)
    eapply (sr_seq H HH).
    { eapply (EGS ph E) with (save := 1) (lo := lo) (B := B) (LB := LB) (s := s) (x := x) (errv := errv);
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia;
        first [ intros _; right; reflexivity | apply mod16_sub32; exact SPA | rewrite errno_RATP; exact ERR1 ]. }
    intros [ms2 mo2] PO. unfold egs_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & s2' & LBN & c &
                    -> & MP2 & (KREL2 & MI2 & ST2 & AUX2 & HP2 & MF2 & IM2 & GM2 & RL2) & ERR2 & ERRV2 & DL & EP2 & CP2 & EST2 & XP2).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST2, XP2 by lia. rewrite errno_RATP in ERR2.
    (* [comment removed for export] *)
    assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -32) (en_frame s2 s1 s0 ra)).
    { eapply xpres_rw_cells'; [exact XP2| exact FR1| left; cbn; lia|].
      unfold ERR_X, A_err_string_once, A_defctx_inited, A_tevent_once, A_load_strings_once, A_optsdone, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, A_tsd_main.
      repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
    (* [comment removed for export] *)
    set (es := blk_addr (ec_es c)) in *.
    pose proof EP2 as [ES2 EC2]. pose proof EC2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
    assert (SUB2 : forall b, In b (LBN ++ LB) -> In b (SB ++ LBN ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP2 (SUB2 _ I5)) as RB5. unfold rblock_range in RB5. rewrite Z5 in RB5. fold es in RB5. unfold ERRST_SIZE in RB5.
    apply ERRST_split in EST2. destruct EST2 as [EM2 OWN].
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL2| eapply en_seg2a with (es := es) (E := E); [exact EM2| lia| lia| exact MI2]|].
    intros ms3 (a1' & a3' & m3 & -> & MU3 & WM3 & MI3 & EM3).
    pose proof EM2 as (SL & TR & _). pose proof (err_next_range _ TR) as TR'. set (t' := err_next (es_top E)) in *.
    eapply (sr_evt_krel H HH); [exact KREL2| eapply en_seg2b with (es := es) (t := t') (E := en_E0 E); [exact EM3| exact TR'| lia| lia| exact MI3]|].
    intros ms4 (a3'' & m4 & -> & MU4 & WM4 & MI4 & EM4).
    assert (CW2 : C4W (LBN ++ LB) m2 (ErrReady c) x) by (unfold C4W; tauto).
    destruct (es_world H HH _ _ _ _ m4 _ _ _ _ _ _ _ _ HP2 SUB2 CW2 AUX2 ERR2 ST2 FR2 CEIL ltac:(lia) ltac:(lia)
                (munch_trans _ _ _ _ MU3 MU4) (wmono_trans _ _ _ _ WM3 WM4)) as (HP4 & CW4 & AUX4 & ERR4 & ST4 & FR4).
    (* [comment removed for export] *)
    set (sl := slot_at E t') in *.
    change (slot_at (en_E0 E) t') with sl in *.
    pose proof (slot_at_own _ E t' OWN SL TR') as [OF OG]. fold sl in OF, OG.
    eapply (sr_seq H HH).
    { eapply (cfree_opt_spec H HH) with (P := sl_file sl) (o := sl_file_o sl) (LB := SB ++ LBN ++ LB) (lo := lo) (B := B) (s := s2') (errv := errv2);
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia; try (unfold CFREE_STACK, RFREE_STACK; lia);
        try (rewrite errno_RATP; exact ERR4); try (destruct CW4 as (_ & K1 & K2 & _); assumption).
      destruct (sl_file_o sl) as [[idf nf]|]; cbn [ofield] in OF; [destruct OF as (_ & _ & OF); apply in_or_app; left; exact OF| exact OF]. }
    intros [ms5 mo5] PO. unfold cfree_opt_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m5 & s5' & L5 &
                    -> & KREL5 & MP5 & MI5 & ST5 & ERR5 & AUX5 & PM5 & SUB5 & XP5 & HP5 & IM5 & GM5).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST5, XP5 by lia. rewrite errno_RATP in ERR5.
    (* [comment removed for export] *)
    pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ HP2) as ND2.
    assert (KEEP : forall Fr L', Permutation (Fr ++ L') (SB ++ LBN ++ LB) -> (forall b, In b Fr -> In b SB) -> forall b, In b (LBN ++ LB) -> In b L').
    { intros Fr L' PM FS b Hb. eapply perm_keep; [exact PM| apply SUB2; exact Hb|]. intros K.
      eapply (nodup_map_app_excl blk_id SB (LBN ++ LB) b); [exact ND2| apply FS; exact K| exact Hb]. }
    assert (FSf : forall b, In b (blocks_of (sl_file sl) (sl_file_o sl)) -> In b SB).
    { intros b Hb. destruct (sl_file_o sl) as [[idf nf]|]; cbn [blocks_of ofield] in *; [| contradiction]. destruct Hb as [<-|[]]. tauto. }
    assert (FSg : forall b, In b (blocks_of (sl_func sl) (sl_func_o sl)) -> In b SB).
    { intros b Hb. destruct (sl_func_o sl) as [[idg ng]|]; cbn [blocks_of ofield] in *; [| contradiction]. destruct Hb as [<-|[]]. tauto. }
    pose proof (KEEP _ _ PM5 FSf) as SUBK5.
    destruct (free_world _ _ _ m5 _ _ _ _ _ _ CW4 XP5 SUBK5 FR4 ltac:(lia) EM4 ltac:(fold es; lia) ltac:(fold es; unfold ERRST_SIZE; lia)) as (CW5 & FR5 & EM5).
    fold es in EM5.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL5| eapply en_seg3 with (es := es) (t := t') (E := es_with_slot (en_E0 E) t' (slot_wipe sl)); [exact EM5| exact TR'| lia| lia| exact MI5]|].
    intros ms6 (m6 & -> & MU6 & WM6 & MI6 & EM6).
    assert (SL0 : length (es_slots (en_E0 E)) = 16%nat) by exact SL.
    rewrite (slot_at_upd (en_E0 E) t' _ SL0 TR') in EM6 |- *. rewrite (es_with_slot_twice (en_E0 E) t' _ _ SL0 TR') in EM6.
    cbn [slot_wipe sl_func] in *.
    assert (SUB5' : forall b, In b (LBN ++ LB) -> In b L5) by exact SUBK5.
    destruct (es_world H HH _ _ _ _ m6 _ _ _ _ _ _ _ _ HP5 SUB5' CW5 AUX5 ERR5 ST5 FR5 CEIL ltac:(lia) ltac:(lia) MU6 WM6) as (HP6 & CW6 & AUX6 & ERR6 & ST6 & FR6).
    (* [comment removed for export] *)
    eapply (sr_seq H HH).
    { eapply (cfree_opt_spec H HH) with (P := sl_func sl) (o := sl_func_o sl) (LB := L5) (lo := lo) (B := B) (s := s5') (errv := errv2);
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia; try (unfold CFREE_STACK, RFREE_STACK; lia);
        try (rewrite errno_RATP; exact ERR6); try (destruct CW6 as (_ & K1 & K2 & _); assumption).
      destruct (sl_func_o sl) as [[idg ng]|] eqn:EG; cbn [ofield] in OG; [| exact OG]. destruct OG as (_ & _ & OG).
      eapply perm_keep; [exact PM5| apply in_or_app; left; exact OG|]. intros K.
      (* [comment removed for export] *)
      pose proof (blocks_slots_split (es_slots E) (Z.to_nat t') (slot_clear 0) ltac:(lia)) as SPL. fold (slot_at E t') in SPL. fold sl in SPL.
      unfold blocks_slot in SPL. rewrite EG in SPL.
      assert (NDS : List.NoDup (map blk_id SB)) by (rewrite map_app in ND2; eapply NoDup_app_remove_r; exact ND2).
      unfold SB in NDS. rewrite blocks_ERRST_slots, SPL in NDS.
      eapply (nodup_mid_excl blk_id _ _ _ _ _ NDS K). cbn. left. reflexivity. }
    intros [ms7 mo7] PO. unfold cfree_opt_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m7 & s7' & L7 &
                    -> & KREL7 & MP7 & MI7 & ST7 & ERR7 & AUX7 & PM7 & SUB7 & XP7 & HP7 & IM7 & GM7).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST7, XP7 by lia. rewrite errno_RATP in ERR7.
    assert (SUBK7 : forall b, In b (LBN ++ LB) -> In b L7).
    { intros b Hb. eapply perm_keep; [exact PM7| apply SUBK5; exact Hb|]. intros K.
      eapply (nodup_map_app_excl blk_id SB (LBN ++ LB) b); [exact ND2| apply FSg; exact K| exact Hb]. }
    destruct (free_world _ _ _ m7 _ _ _ _ _ _ CW6 XP7 SUBK7 FR6 ltac:(lia) EM6 ltac:(fold es; lia) ltac:(fold es; unfold ERRST_SIZE; lia)) as (CW7 & FR7 & EM7).
    fold es in EM7.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL7| eapply en_seg4 with (es := es) (t := t') (lo := lo) (E := es_with_slot (en_E0 E) t' (slot_file0 (slot_wipe sl)));
                                 [exact EM7| exact TR'| lia| lia| lia| exact MI7| exact ST7| exact FR7]|].
    intros ms8 (m8 & -> & MU8 & WM8 & MI8 & ST8 & EM8).
    rewrite (slot_at_upd (en_E0 E) t' _ SL0 TR') in EM8. rewrite (es_with_slot_twice (en_E0 E) t' _ _ SL0 TR') in EM8.
    unfold slot_func0, slot_file0, slot_wipe in EM8. cbn [sl_flags sl_buffer sl_file sl_file_o sl_line sl_func sl_func_o] in EM8.
    change (es_with_slot (en_E0 E) t' (mkSLOT 0 0 0 None (2 ^ 32 - 1) 0 None)) with (errst_new E) in EM8.
    (* [comment removed for export] *)
    assert (HP8 : hs_RHEAP H s7' L7 m8 /\ C4W (LBN ++ LB) m8 (ErrReady c) x /\ hs_rauxv_ok H m8 B /\ rw_cells rsegs m8 RERRNO [C4 errv2]).
    { destruct (es_world H HH _ _ _ _ m8 _ _ _ _ _ _ _ _ HP7 SUBK7 CW7 AUX7 ERR7 ST7 FR7 CEIL ltac:(lia) ltac:(lia) MU8 WM8) as (K1 & K2 & K3 & K4 & _). tauto. }
    destruct HP8 as (HP8 & CW8 & AUX8 & ERR8). destruct CW8 as (MF8 & IM8 & GM8 & RL8 & EP8 & CP8).
    (* [comment removed for export] *)
    assert (PMF : Permutation L7 (blocks_ERRST (errst_new E) ++ LBN ++ LB)).
    { pose proof (blocks_slots_clear_perm (es_slots E) (Z.to_nat t') (2 ^ 32 - 1) (slot_clear 0) ltac:(lia)) as PC.
      fold (slot_at E t') in PC. fold sl in PC. unfold blocks_slot in PC.
      set (bf := blocks_of (sl_file sl) (sl_file_o sl)) in *. set (bg := blocks_of (sl_func sl) (sl_func_o sl)) in *.
      change (blocks_ERRST (errst_new E)) with (blocks_slots (slot_upd (es_slots E) (Z.to_nat t') (slot_clear (2 ^ 32 - 1)))).
      set (SB' := blocks_slots (slot_upd (es_slots E) (Z.to_nat t') (slot_clear (2 ^ 32 - 1)))) in *.
      apply (Permutation_app_inv_l (bf ++ bg)).
      rewrite <- (app_assoc bf bg L7).
      eapply Permutation_trans; [apply Permutation_app_head; exact PM7|].
      eapply Permutation_trans; [exact PM5|].
      rewrite (app_assoc (bf ++ bg) SB' (LBN ++ LB)). apply Permutation_app_tail. exact PC. }
    apply (sr_done H HH). unfold errnew_post. cbn [cfg_ms cfg_model].
    exists w0, w1, w2, d0, d1, d2, d3, d4, d5, d6, d7, w3, w4, w5, w6, m8, errv2, s7', LBN, c.
    split; [reflexivity|]. split; [eapply (mpres_trans H HH); [exact MP2| eapply (mpres_trans H HH); [exact MP5| exact MP7]]|].
    split. { unfold c4_frame. cbn [cfg_model]. split; [exact KREL7|]. split; [exact MI8|]. split; [exact ST8|]. split; [exact AUX8|].
             split; [eapply PERM; [exact HP8| exact PMF]|]. tauto. }
    split; [rewrite errno_RATP; exact ERR8|]. split; [exact DL|]. split; [exact EP8|]. split; [exact CP8|].
    split.
    { apply ERRST_split. split; [exact EM8|]. destruct E as [ss top bot]. unfold errst_new. cbn [es_slots es_top es_bottom].
      eapply ERROWN_upd; [exact OWN|]. intros LBx _. cbn [slot_clear sl_file sl_file_o sl_func sl_func_o ofield]. split; reflexivity. }
    (* [comment removed for export] *)
    set (X := ERR_X ++ errph_foot ph).
    assert (XES : forall ma mb, munch [(es, es + 904)] ma mb -> wmono rsegs ma mb -> xpres LB (bv_unsigned sp) X ma mb).
    { intros ma mb MUx WMx. eapply xpres_of_munch_gen; [exact MUx| exact WMx|].
      intros a Ha [HC HXn]. cbn. split; [| exact I]. intros Hr.
      destruct HC as [K|[[K _]|(b & Hb & Hrb)]]; [lia| lia|].
      assert (NN : ~ (blk_id b <> blk_id (ec_es c))).
      { intros NE. pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ _ _ HP2 (SUB2 _ (in_or_app _ _ _ (or_intror Hb))) (SUB2 _ I5) NE) as DJ.
        rewrite Z5 in DJ. fold es in DJ. unfold ERRST_SIZE in DJ. lia. }
      apply NN. intros EQid.
      pose proof (nodup_id_inj _ _ _ ND2 (SUB2 _ (in_or_app _ _ _ (or_intror Hb))) (SUB2 _ I5) EQid) as EQB. subst b.
      destruct ph as [|cq]; cbn [errph_delta errph_foot] in *.
      - destruct DL as (_ & _ & _ & FA). pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail FA)))) as IN5.
        assert (NDx : List.NoDup (map blk_id (LBN ++ LB))) by (rewrite map_app in ND2; eapply NoDup_app_remove_l; exact ND2).
        eapply (nodup_map_app_excl blk_id LBN LB (ec_es c)); [exact NDx| exact IN5| exact Hb].
      - destruct DL as [-> _]. apply HXn. unfold X. apply rin_ivs_app. right. cbn. left. fold es. unfold ERRST_SIZE. lia. }
    assert (XFR : forall L' ma mb, xpres L' (bv_unsigned sp + -32) [] ma mb -> (forall b, In b (LBN ++ LB) -> In b L') -> xpres LB (bv_unsigned sp) X ma mb).
    { intros L' ma mb XPx SUBx'. eapply xpres_weaken; [exact XPx| lia| intros b Hb; apply SUBx'; apply in_or_app; right; exact Hb| intros a []]. }
    eapply xpres_trans; [exact XP01|].
    eapply xpres_trans; [eapply xpres_weaken; [exact XP2| lia| auto| intros a Ka; unfold X; apply rin_ivs_app; left; exact Ka]|].
    eapply xpres_trans; [apply (XES _ _ (munch_trans _ _ _ _ MU3 MU4) (wmono_trans _ _ _ _ WM3 WM4))|].
    eapply xpres_trans; [apply (XFR _ _ _ XP5 SUBK5)|].
    eapply xpres_trans; [apply (XES _ _ MU6 WM6)|].
    eapply xpres_trans; [apply (XFR _ _ _ XP7 SUBK7)|].
    apply (XES _ _ MU8 WM8).
  Qed.
End W.
