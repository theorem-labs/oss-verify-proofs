(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_Rep ECH_LibState ECH_C0_stmt ECH_C1_stmt ECH_C1_malloc ECH_C1_free ECH_C1_freeopt ECH_C2_stmt ECH_LibFrame ECH_C4_stmt ECH_C4_rep ECH_C4_frame ECH_C4_egs ECH_UbKit.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  (* [comment removed for export] *)
  Definition EC_LOOP : Z := 0xe47b8.   Definition EC_EXIT : Z := 0xe47d0.
  Definition EC_RA0 : Z := 0xe47a8.    (* [comment removed for export] *)
  Definition ECL_RA : Z := 0xe47c8.    (* [comment removed for export] *)
  Definition EC_RA1 : Z := 0xe4378.    (* [comment removed for export] *)
  Definition EC_RA2 : Z := 0xe43a0.    (* [comment removed for export] *)
  Definition EC_FILE : Z := 0x33a89.
  Definition P_err_clear : Z := 0xe423c.
  Definition ec_frame (j : list byte) (s3 s2 s1 s0 ra : word) : list cell := [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  (* [comment removed for export] *)
  Definition ecl_frame (s6 s5 s4 : word) (i es : Z) (s0 : word) : list cell :=
    [C8 s6; C8 s5; C8 s4; C8 (Z_to_bv 64 16); C8 (Z_to_bv 64 i); C8 (Z_to_bv 64 es); C8 s0; C8 (Z_to_bv 64 ECL_RA)].

  (* [comment removed for export] *)
  Definition ECL_BODY : Z := 0xe4264.
  Lemma ec_segA0 :
    forall (ra0 : word) (spx : Z) (gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (es i lo : Z),
      0 <= es < 2^64 -> 0 <= i < 16 -> spx < 2^64 ->
      stk usegs m lo spx -> hceil <= lo -> lo <= spx - 64 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 ECL_RA) (Z_to_bv 64 (spx + -64)) gp tp t0 t1 t2 (Z_to_bv 64 spx) (Z_to_bv 64 es) (Z_to_bv 64 es) (Z_to_bv 64 i) (Z_to_bv 64 0)
                       a3 a4 a5 a6 a7 (Z_to_bv 64 i) (Z_to_bv 64 16) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 ECL_BODY) fc None m1 (seg_rom usegs)
          /\ munch [(spx + -64, spx)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (spx + -64)
          /\ rw_cells usegs m1 (spx + -64) (ecl_frame s6 s5 s4 i es s0))
        (MS (mkR ra0 (Z_to_bv 64 spx) gp tp t0 t1 t2 s0 (Z_to_bv 64 es) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 i) (Z_to_bv 64 16)
                 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 EC_LOOP) fc None m (seg_rom usegs)).
  Proof.
    intros until lo. intros ESR IR SPX ST CEIL LO MI. unfold ECL_RA, ECL_BODY, EC_LOOP, ecl_frame. hcb.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(spx + -64, spx)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    (* [comment removed for export] *)
    step. step. step. step.
    carve_frame 64%nat ST. do 9 st1. zstep. rewrite ?Z.add_0_r.
    finish.
  Qed.

  (* [comment removed for export] *)
  Lemma ec_segA1 :
    forall (spi gp tp t0 t1 t2 s0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (es i : Z) (E : errst),
      es mod 8 = 0 ->
      ERRSTm m es E -> 0 <= i < 16 -> 0 < es -> es + 904 < 2^64 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists a3' a4' a5' m1,
          ms' = MS (mkR (Z_to_bv 64 EC_RA1) spi gp tp t0 t1 t2 s0 (Z_to_bv 64 es) (Z_to_bv 64 (sl_file (slot_at E i))) (Z_to_bv 64 EC_FILE)
                       (Z_to_bv 64 112) a3' a4' a5' a6 a7 (Z_to_bv 64 (i * 8)) (Z_to_bv 64 (es + 576 + i * 8)) (Z_to_bv 64 (es + i * 4)) (Z_to_bv 64 (es + i * 4 + 512)) s6
                       s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m1 (seg_rom usegs)
          /\ munch [(es, es + 904)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ ERRSTm m1 es (es_with_slot E i (slot_wipe (slot_at E i))))
        (MS (mkR (Z_to_bv 64 ECL_RA) spi gp tp t0 t1 t2 s0 (Z_to_bv 64 es) (Z_to_bv 64 es) (Z_to_bv 64 i) (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3
                 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ECL_BODY) fc None m (seg_rom usegs)).
  Proof.
    intros until E. intros ESAL EST TR' POS BL MI. unfold EC_RA1, ECL_BODY, EC_FILE, P_CRYPTO_free.
    pose proof (munch_refl [(es, es + 904)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold ERRSTm in EST. destruct EST as (SL & TR & BR & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & TB & RG).
    unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP in *.
    arr_lens SL.
    (* [comment removed for export] *)
    step. ub_dead_by (clear - POS). step. step. ubal_by ESAL. step. if_lit.
    step. step. ub_dead_by (clear - TR'). zstep. shl_norm. zstep. zstep. step. ub_dead_by (clear - TR' POS BL).
    pose proof (zero16_byte_m _ _ i F6 TR') as RD. replace (es + 512 + i * 4) with (es + i * 4 + 512) in RD by lia. step. clear RD. nrm. unfold wz.
    (* [comment removed for export] *)
    zstep. zstep. shl_norm. step. try if_lit.
    (* [comment removed for export] *)
    zstep. step. ubnot. step. ub_dead_by (clear - TR' POS BL). zstep. zstep. step. ubnot.
    arr_store64 F4 i (wz 0). rewrite upd_zero16 in F4 by lia.
    step. ub_dead2.
    (* [comment removed for export] *)
    zstep. arr_store64 F5 i (wz 0). rewrite upd_zero16 in F5 by lia.
    step. ub_dead_by (clear - TR' POS BL). step.
    arr_store32 F6 i (wz 0). rewrite upd_zero16 in F6 by lia.
    (* [comment removed for export] *)
    zstep. step. ubnot. step. ub_dead_by (clear - TR' POS BL). zstep. step. ubnot.
    arr_store32 F2 i (wz 0). rewrite upd_zero16 in F2 by lia.
    step. ub_dead_by (clear - TR' POS BL).
    (* [comment removed for export] *)
    zstep. step. ubnot.
    arr_store32 F1 i (wz 0).
    step. ub_dead_by (clear - TR' POS BL). zstep. zstep. step. ubnot.
    arr_store64 F3 i (wz 0).
    step. ub_dead_by (clear - TR' POS BL).
    (* [comment removed for export] *)
    zstep. step. zstep. zstep.
    arr_store32 F8 i (Z_to_bv 64 (-1)). apply (u32arr_upd_le4 _ _ _ _ _ _ le4_minus1) in F8.
    step. ub_dead_by (clear - TR' POS BL).
    pose proof (u64arr_read_m _ _ _ i _ F7 (slot_nth E i (fun s => wz (sl_file s)) SL TR') ltac:(lia)) as RD.
    replace (es + 576 + i * 8) with (es + 576 + i * 8) in RD by lia. step. clear RD.
    step. step. step. step.
    finish.
    eapply (ERRSTm_with_slot _ es E i (slot_wipe (slot_at E i))); try eassumption; try reflexivity;
      try (upd_keep_tac E i SL TR'); cbn [slot_wipe sl_flags sl_buffer sl_line]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ec_segB :
    forall (spi gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (es i : Z) (E : errst),
      ERRSTm m es E -> 0 <= i < 16 -> 0 < es -> es + 904 < 2^64 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 EC_RA2) spi gp tp t0 t1 t2 s0 (Z_to_bv 64 (es + 768 + i * 8)) (Z_to_bv 64 (sl_func (slot_at E i))) (Z_to_bv 64 EC_FILE)
                       (Z_to_bv 64 114) a3 a4 a5 a6 a7 (Z_to_bv 64 (i * 8)) (Z_to_bv 64 (es + 576 + i * 8)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m1 (seg_rom usegs)
          /\ munch [(es, es + 904)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ ERRSTm m1 es (es_with_slot E i (slot_file0 (slot_at E i))))
        (MS (mkR (Z_to_bv 64 EC_RA1) spi gp tp t0 t1 t2 s0 (Z_to_bv 64 es) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (i * 8)) (Z_to_bv 64 (es + 576 + i * 8))
                 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 EC_RA1)) fc None m (seg_rom usegs)).
  Proof.
    intros until E. intros EST TR' POS BL MI. unfold EC_RA1, EC_RA2, EC_FILE, P_CRYPTO_free.
    replace (ret_pc (Z_to_bv 64 0xe4378)) with (Z_to_bv 64 0xe4378) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (munch_refl [(es, es + 904)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold ERRSTm in EST. destruct EST as (SL & TR & BR & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & TB & RG).
    unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP in *.
    arr_lens SL.
    (* [comment removed for export] *)
    step. ub_dead_by (clear - TR' POS BL). zstep. zstep.
    arr_store64 F7 i (wz 0).
    step. ub_dead_by (clear - TR' POS BL).
    pose proof (u64arr_read_m _ _ _ i _ F9 (slot_nth E i (fun s => wz (sl_func s)) SL TR') ltac:(lia)) as RD.
    replace (es + 768 + i * 8) with (es + 768 + i * 8) in RD by lia. step. clear RD.
    step. step. step. step.
    finish.
    pose proof (slot_at_own _ E i RG SL TR') as (O1 & O2 & O3).
    eapply (ERRSTm_with_slot _ es E i (slot_file0 (slot_at E i))); try eassumption; try reflexivity;
      try (upd_keep_tac E i SL TR'); cbn [slot_file0 sl_flags sl_buffer sl_line]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ec_segC :
    forall (spx : Z) (gp tp t0 t1 t2 s0x a0 a1 a2 a3 a4 a5 a6 a7 x3 s4x s5x s6x s7 s8 s9 s10 s11 t3 t4 t5 t6 s0 s4 s5 s6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (es i lo : Z) (E : errst),
      ERRSTm m es E -> 0 <= i < 16 -> 0 < es -> es + 904 <= lo -> lo <= spx - 64 -> spx < 2^64 -> mem_inv usegs m ->
      stk usegs m lo (spx + -64) -> rw_cells usegs m (spx + -64) (ecl_frame s6 s5 s4 i es s0) ->
      evt usegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 ECL_RA) (Z_to_bv 64 spx) gp tp t0 t1 t2 s0 (Z_to_bv 64 es) a0 a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 (i + 1)) (Z_to_bv 64 16) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 (if i + 1 <? 16 then EC_LOOP else EC_EXIT)) fc None m1 (seg_rom usegs)
          /\ munch [(es, es + 904)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1 /\ stk usegs m1 lo spx
          /\ ERRSTm m1 es (es_with_slot E i (slot_func0 (slot_at E i))))
        (MS (mkR (Z_to_bv 64 EC_RA2) (Z_to_bv 64 (spx + -64)) gp tp t0 t1 t2 s0x (Z_to_bv 64 (es + 768 + i * 8)) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 (i * 8)) x3 s4x s5x s6x s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 EC_RA2)) fc None m (seg_rom usegs)).
  Proof.
    intros until E. intros EST TR' POS BL LO SPX MI ST FR. unfold ecl_frame in *. unfold EC_RA2, ECL_RA, EC_LOOP, EC_EXIT in *.
    replace (ret_pc (Z_to_bv 64 0xe43a0)) with (Z_to_bv 64 0xe43a0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). hcb.
    pose proof (munch_refl [(es, es + 904)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold ERRSTm in EST. destruct EST as (SL & TR & BR & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & TB & RG).
    unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP in *.
    arr_lens SL.
    (* [comment removed for export] *)
    step. ub_dead_by (clear - TR' POS BL LO SPX).
    arr_store64 F9 i (wz 0).
    do 8 st1. zstep. rewrite ?Z.add_0_r. step.
    release_frame FR ST spx.
    zstep. step.
    pose proof (slot_at_own _ E i RG SL TR') as (O1 & O2 & O3).
    if_cases K1; zify_cond K1.
    - replace (i + 1 <? 16) with true by (symmetry; apply Z.ltb_lt; lia).
      finish.
      eapply (ERRSTm_with_slot _ es E i (slot_func0 (slot_at E i))); try eassumption; try reflexivity;
        try (upd_keep_tac E i SL TR'); cbn [slot_func0 sl_flags sl_buffer sl_line]; lia.
    - replace (i + 1 <? 16) with false by (symmetry; apply Z.ltb_ge; lia).
      finish.
      eapply (ERRSTm_with_slot _ es E i (slot_func0 (slot_at E i))); try eassumption; try reflexivity;
        try (upd_keep_tac E i SL TR'); cbn [slot_func0 sl_flags sl_buffer sl_line]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ec_segD :
    forall (sp gp tp t0 t1 t2 s0x a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra0 ra s0 s1 s2 s3 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (es lo : Z) (E : errst) (j : list byte),
      es mod 8 = 0 ->
      ERRSTm m es E -> 0 < es -> es + 904 <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv usegs m ->
      stk usegs m lo (bv_unsigned sp + -48) -> rw_cells usegs m (bv_unsigned sp + -48) (ec_frame j s3 s2 s1 s0 ra) ->
      evt usegs (fun ms' => exists a0' m1,
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m1 (seg_rom usegs)
          /\ munch [(es, es + 904)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1 /\ stk usegs m1 lo (bv_unsigned sp)
          /\ ERRSTm m1 es (mkERRST (es_slots E) 0 0))
        (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0x (Z_to_bv 64 es) a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 EC_EXIT) fc None m (seg_rom usegs)).
  Proof.
    intros until j. intros ESAL EST POS BL LO MI ST FR. unfold EC_EXIT, ec_frame in *.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(es, es + 904)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold ERRSTm in EST. destruct EST as (SL & TR & BR & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & TB & RG).
    unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP in *.
    arr_lens SL.
    (* [comment removed for export] *)
    apply rw_cells_forget in TB. destruct TB as [jk TB]. cbn [cells_size csize Nat.add] in TB.
    step. ubal_by ESAL. step. if_lit.
    st1.
    do 5 st1. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
    unfold ERRSTm, O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP. cbn [es_slots es_top es_bottom].
    repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
    eapply rw_cells_recut; [eassumption| cbn; tauto| reflexivity].
  Qed.
  (* [comment removed for export] *)
  Lemma ec_seg0 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1 j,
          ms' = MS (mkR (Z_to_bv 64 EC_RA0) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_ossl_err_get_state_int) fc None m1 (seg_rom usegs)
          /\ munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (bv_unsigned sp + -48)
          /\ rw_cells usegs m1 (bv_unsigned sp + -48) (ec_frame j s3 s2 s1 s0 ra))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_ERR_clear_error) fc None m (seg_rom usegs)).
  Proof.
    intros until lo. intros ST CEIL LO MI. unfold P_ERR_clear_error, P_ossl_err_get_state_int, EC_RA0, ec_frame. hcb.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 48%nat ST. do 6 st1. step. step. step. finish. exact FR.
  Qed.

  (* [comment removed for export] *)
  Lemma ec_seg1 :
    forall (ra0 sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (es : Z),
      0 < es -> es + 904 < 2^64 -> mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 es) (Z_to_bv 64 es) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 16)
                       s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 EC_LOOP) fc None m (seg_rom usegs))
        (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 es) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 EC_RA0)) fc None m (seg_rom usegs)).
  Proof.
    intros until es. intros POS BL MI. unfold EC_RA0, EC_LOOP.
    replace (ret_pc (Z_to_bv 64 0xe47a8)) with (Z_to_bv 64 0xe47a8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. if_cases K1; zify_cond K1; [kill K1|]; clear K1.
    step. step. step.
    apply evt_done. reflexivity.
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

  (* [comment removed for export] *)
  Section Loop.
    Variables (sp gp tp s0 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
    Variables (f3 f2 f1 f0 fra : word) (fj : list byte).         (* [comment removed for export] *)
    Variables (E : errst) (c : errchain) (x : ctxinfo) (LBx LB0 : list block) (SP lo B : Z) (X : list (Z * Z)) (errv : word).
    Variables (m_in : mem) (mo_in : Model).
    Let es := blk_addr (ec_es c).
    Let spx := bv_unsigned sp + -48.
    Hypothesis TPV : tp = Z_to_bv 64 RATP.
    Hypothesis SL : length (es_slots E) = 16%nat.
    Hypothesis OWN : ERROWN (blocks_ERRST E) E.
    Hypothesis SUB0 : forall b, In b LB0 -> In b LBx.
    Hypothesis NCL : forall a, es <= a < es + 904 -> ~ xclient LB0 SP X a.
    Hypothesis CEIL : hceil <= lo.
    Hypothesis LOB : lo <= bv_unsigned sp - (112 + 8208).   (* [comment removed for export] *)
    Hypothesis ESAL : es mod 8 = 0.
    Hypothesis SPB : bv_unsigned sp <= B.
    Hypothesis SPS : bv_unsigned sp <= SP.

    Definition ec_inv (i : Z) : config -> Prop :=
      fun k => exists ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m (s : PState),
        cfg_ms k = MS (mkR ra0 (Z_to_bv 64 spx) gp tp t0 t1 t2 s0 (Z_to_bv 64 es) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 i) (Z_to_bv 64 16)
                           s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 (if i <? 16 then EC_LOOP else EC_EXIT)) fc None m (seg_rom usegs)
        /\ hs_KREL H s (cfg_model k) /\ hs_MPRES H mo_in (cfg_model k) /\ mem_inv usegs m /\ stk usegs m lo spx
        /\ rw_cells usegs m RERRNO [C4 errv] /\ hs_rauxv_ok H m B
        /\ hs_RHEAP H s (blocks_slots (skipn (Z.to_nat i) (es_slots E)) ++ LBx) m /\ C4W LBx m (ErrReady c) x
        /\ ERRSTm m es (clr E i) /\ rw_cells usegs m spx (ec_frame fj f3 f2 f1 f0 fra)
        /\ xpres LB0 SP X m_in m.

    Lemma ec_trip : forall i, 0 <= i < 16 -> forall k, ec_inv i k -> hs_SR H (ec_inv (i + 1)) k.
    Proof.
      intros i Hi [ms mo] (ra0 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & s &
                           EQ & KREL & MP & MI & ST & ERR & AUX & HP & CW & EM & FR & XP).
      cbn [cfg_ms cfg_model] in *. subst ms. replace (i <? 16) with true by (symmetry; apply Z.ltb_lt; lia).
      hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
      set (ss := es_slots E) in *. set (SBi := blocks_slots (skipn (Z.to_nat i) ss)) in *.
      assert (SUBx : forall b, In b LBx -> In b (SBi ++ LBx)) by (intros b Hb; apply in_or_app; right; exact Hb).
      pose proof CW as (_ & _ & _ & _ & [_ EC] & _). cbn [ERRPH] in EC. destruct EC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
      pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP (SUBx _ I5)) as RB5. unfold rblock_range in RB5. rewrite Z5 in RB5. fold es in RB5. unfold ERRST_SIZE in RB5.
      assert (SLc : length (es_slots (clr E i)) = 16%nat) by (unfold clr; cbn [es_slots]; rewrite clr_slots_length; exact SL).
      set (sl := slot_at E i) in *.
      pose proof (slot_at_own _ E i OWN SL Hi) as [OF OG]. fold sl in OF, OG.
      (* [comment removed for export] *)
      assert (SPL : SBi = (blocks_of (sl_file sl) (sl_file_o sl) ++ blocks_of (sl_func sl) (sl_func_o sl)) ++ blocks_slots (skipn (S (Z.to_nat i)) ss)).
      { unfold SBi. rewrite (skipn_cons_nth ss (Z.to_nat i) (slot_clear 0)) by lia. reflexivity. }
      (* [comment removed for export] *)
      assert (RBL : forall b, In b LBx -> rblock_range (blk_addr b) (blk_size b)).
      { intros b Hb. eapply (HH_RHEAP_block_range H HH); [exact HP| apply SUBx; exact Hb]. }
      eapply (sr_evt_krel H HH); [exact KREL| eapply ec_segA0 with (es := es) (i := i) (lo := lo); [lia| exact Hi| unfold spx; lia| exact ST| exact CEIL| unfold spx; lia| exact MI]|].
      intros ms0 (m0 & -> & MU0 & WM0 & MI0 & ST0 & FRI0).
      assert (W0 : hs_RHEAP H s (SBi ++ LBx) m0 /\ C4W LBx m0 (ErrReady c) x /\ hs_rauxv_ok H m0 B /\ rw_cells usegs m0 RERRNO [C4 errv]
                   /\ rw_cells usegs m0 spx (ec_frame fj f3 f2 f1 f0 fra) /\ ERRSTm m0 es (clr E i)).
      { split. { eapply (HH_RHEAP_frame H HH); [exact HP| exact MU0| exact WM0|]. apply Forall_cons; [left; cbn; unfold spx; lia| apply Forall_nil]. }
        split. { eapply C4W_stack; [exact CW| exact MU0| exact WM0| | exact RBL]. apply Forall_cons; [left; cbn; unfold spx; lia| apply Forall_nil]. }
        split. { eapply (HH_rauxv_frame H HH); [exact AUX| exact MU0| exact WM0|]. unfold RAUXV_CELL. apply Forall_cons; [cbn; unfold spx; lia| apply Forall_nil]. }
        split. { eapply rw_cells_transport; [exact ERR| exact MU0| exact WM0|]. unfold RERRNO. cbn. unfold spx. lia. }
        split. { eapply rw_cells_transport; [exact FR| exact MU0| exact WM0|]. cbn. unfold spx. lia. }
        eapply ERRSTm_munch; [exact EM| exact MU0| exact WM0|]. unfold ERRST_SIZE. cbn. unfold spx. lia. }
      assert (XST : xpres LB0 SP X m m0).
      { eapply xpres_of_munch_gen; [exact MU0| exact WM0|]. intros a Ha [HC HXn]. cbn. split; [| exact I]. intros Hr.
        destruct HC as [K|[[K _]|(b & Hb & Hrb)]]; [unfold spx in Hr; lia| unfold spx in Hr; hcb; lia|].
        pose proof (RBL b (SUB0 b Hb)) as RB. unfold rblock_range in RB. unfold spx in Hr. hcb. lia. }
      clear HP CW AUX ERR FR EM. destruct W0 as (HP & CW & AUX & ERR & FR & EM).
      (* [comment removed for export] *)
      eapply (sr_evt_krel H HH); [exact KREL| eapply ec_segA1 with (es := es) (i := i) (E := clr E i); [exact ESAL| exact EM| exact Hi| lia| lia| exact MI0]|].
      intros ms1 (a3' & a4' & a5' & m1 & -> & MU1 & WM1 & MI1 & EM1). rewrite (slot_at_clr E i SL Hi) in EM1 |- *. fold sl in EM1 |- *.
      destruct (es_world H HH _ _ _ _ m1 _ _ _ _ _ _ _ _ HP SUBx CW AUX ERR ST0 FRI0 CEIL ltac:(unfold spx; lia) ltac:(lia) MU1 WM1) as (HP1 & CW1 & AUX1 & ERR1 & ST1 & FRI1).
      assert (FR1 : rw_cells usegs m1 spx (ec_frame fj f3 f2 f1 f0 fra)) by (eapply rw_cells_transport; [exact FR| exact MU1| exact WM1| cbn; unfold spx; lia]).
      (* [comment removed for export] *)
      eapply (sr_seq H HH).
      { eapply (cfree_opt_spec H HH) with (P := sl_file sl) (o := sl_file_o sl) (LB := SBi ++ LBx) (lo := lo) (B := B) (s := s) (errv := errv);
          try reflexivity; try (rewrite unsigned_lit by (unfold spx; lia)); try eassumption; try (unfold spx; lia); try (unfold spx, CFREE_STACK, RFREE_STACK; lia);
          try (rewrite TPV, errno_RATP; exact ERR1); try (destruct CW1 as (_ & K1 & K2 & _); assumption).
        destruct (sl_file_o sl) as [[idf nf]|]; cbn [ofield] in OF; [| exact OF]. rewrite SPL. cbn [blocks_of app]. left. reflexivity. }
      intros [ms2 mo2] PO. unfold cfree_opt_post in PO. cbn [cfg_ms cfg_model] in PO.
      destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & s2' & L2 &
                      -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & PM2 & SUB2 & XP2 & HP2 & IM2 & GM2).
      rewrite (unsigned_lit (spx + -64)) in ST2, XP2 by (unfold spx; lia). rewrite TPV, errno_RATP in ERR2.
      (* [comment removed for export] *)
      pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ HP) as ND.
      assert (KEEP : forall Fr L', Permutation (Fr ++ L') (SBi ++ LBx) -> (forall b, In b Fr -> In b SBi) -> forall b, In b LBx -> In b L').
      { intros Fr L' PM FS b Hb. eapply perm_keep; [exact PM| apply SUBx; exact Hb|]. intros K.
        eapply (nodup_map_app_excl blk_id SBi LBx b); [exact ND| apply FS; exact K| exact Hb]. }
      assert (FSf : forall b, In b (blocks_of (sl_file sl) (sl_file_o sl)) -> In b SBi) by (intros b Hb; rewrite SPL; apply in_or_app; left; apply in_or_app; left; exact Hb).
      assert (FSg : forall b, In b (blocks_of (sl_func sl) (sl_func_o sl)) -> In b SBi) by (intros b Hb; rewrite SPL; apply in_or_app; left; apply in_or_app; right; exact Hb).
      pose proof (KEEP _ _ PM2 FSf) as SUBK2.
      destruct (free_world _ _ _ m2 _ _ _ _ _ _ CW1 XP2 SUBK2 FRI1 ltac:(lia) EM1 ltac:(fold es; lia) ltac:(fold es; unfold ERRST_SIZE; lia)) as (CW2 & FRI2 & EM2).
      assert (FR2 : rw_cells usegs m2 spx (ec_frame fj f3 f2 f1 f0 fra)) by (eapply xpres_rw_cells'; [exact XP2| exact FR1| left; unfold spx; lia| constructor]).
      fold es in EM2.
      (* [comment removed for export] *)
      eapply (sr_evt_krel H HH); [exact KREL2| eapply ec_segB with (es := es) (i := i) (E := es_with_slot (clr E i) i (slot_wipe sl)); [exact EM2| exact Hi| lia| lia| exact MI2]|].
      intros ms3 (m3 & -> & MU3 & WM3 & MI3 & EM3).
      rewrite (slot_at_upd (clr E i) i _ SLc Hi) in EM3 |- *. rewrite (es_with_slot_twice (clr E i) i _ _ SLc Hi) in EM3. cbn [slot_wipe sl_func] in *.
      destruct (es_world H HH _ _ _ _ m3 _ _ _ _ _ _ _ _ HP2 SUBK2 CW2 AUX2 ERR2 ST2 FRI2 CEIL ltac:(unfold spx; lia) ltac:(lia) MU3 WM3) as (HP3 & CW3 & AUX3 & ERR3 & ST3 & FRI3).
      assert (FR3 : rw_cells usegs m3 spx (ec_frame fj f3 f2 f1 f0 fra)) by (eapply rw_cells_transport; [exact FR2| exact MU3| exact WM3| cbn; unfold spx; lia]).
      (* [comment removed for export] *)
      eapply (sr_seq H HH).
      { eapply (cfree_opt_spec H HH) with (P := sl_func sl) (o := sl_func_o sl) (LB := L2) (lo := lo) (B := B) (s := s2') (errv := errv);
          try reflexivity; try (rewrite unsigned_lit by (unfold spx; lia)); try eassumption; try (unfold spx; lia); try (unfold spx, CFREE_STACK, RFREE_STACK; lia);
          try (rewrite TPV, errno_RATP; exact ERR3); try (destruct CW3 as (_ & K1 & K2 & _); assumption).
        destruct (sl_func_o sl) as [[idg ng]|] eqn:EG; cbn [ofield] in OG; [| exact OG].
        eapply perm_keep; [exact PM2| apply in_or_app; left; rewrite SPL; apply in_or_app; left; apply in_or_app; right; cbn; left; reflexivity|]. intros K.
        assert (NDS : List.NoDup (map blk_id SBi)) by (rewrite map_app in ND; eapply NoDup_app_remove_r; exact ND).
        rewrite SPL in NDS.
        eapply (nodup_mid_excl blk_id [] _ _ _ _ NDS K). rewrite ?EG. cbn. left. reflexivity. }
      intros [ms4 mo4] PO. unfold cfree_opt_post in PO. cbn [cfg_ms cfg_model] in PO.
      destruct PO as (w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m4 & s4' & L4 &
                      -> & KREL4 & MP4 & MI4 & ST4 & ERR4 & AUX4 & PM4 & SUB4 & XP4 & HP4 & IM4 & GM4).
      rewrite (unsigned_lit (spx + -64)) in ST4, XP4 by (unfold spx; lia). rewrite TPV, errno_RATP in ERR4.
      assert (SUBK4 : forall b, In b LBx -> In b L4).
      { intros b Hb. eapply perm_keep; [exact PM4| apply SUBK2; exact Hb|]. intros K.
        eapply (nodup_map_app_excl blk_id SBi LBx b); [exact ND| apply FSg; exact K| exact Hb]. }
      destruct (free_world _ _ _ m4 _ _ _ _ _ _ CW3 XP4 SUBK4 FRI3 ltac:(lia) EM3 ltac:(fold es; lia) ltac:(fold es; unfold ERRST_SIZE; lia)) as (CW4 & FRI4 & EM4).
      assert (FR4 : rw_cells usegs m4 spx (ec_frame fj f3 f2 f1 f0 fra)) by (eapply xpres_rw_cells'; [exact XP4| exact FR3| left; unfold spx; lia| constructor]).
      fold es in EM4.
      (* [comment removed for export] *)
      eapply (sr_evt_krel H HH); [exact KREL4| eapply ec_segC with (es := es) (i := i) (lo := lo) (E := es_with_slot (clr E i) i (slot_file0 (slot_wipe sl)));
                                   [exact EM4| exact Hi| lia| lia| unfold spx; lia| unfold spx; lia| exact MI4| exact ST4| exact FRI4]|].
      intros ms5 (m5 & -> & MU5 & WM5 & MI5 & ST5 & EM5).
      rewrite (slot_at_upd (clr E i) i _ SLc Hi) in EM5. rewrite (es_with_slot_twice (clr E i) i _ _ SLc Hi) in EM5.
      unfold slot_func0, slot_file0, slot_wipe in EM5. cbn [sl_flags sl_buffer sl_file sl_file_o sl_line sl_func sl_func_o] in EM5.
      change (mkSLOT 0 0 0 None (2 ^ 32 - 1) 0 None) with (slot_clear (2 ^ 32 - 1)) in EM5. rewrite (clr_step E i SL Hi) in EM5.
      destruct (es_world H HH _ _ _ _ m5 _ _ _ _ _ _ _ _ HP4 SUBK4 CW4 AUX4 ERR4 ST4 FR4 CEIL ltac:(unfold spx; lia) ltac:(lia) MU5 WM5) as (HP5 & CW5 & AUX5 & ERR5 & _ & FR5).
      (* [comment removed for export] *)
      assert (PMF : Permutation L4 (blocks_slots (skipn (Z.to_nat (i + 1)) ss) ++ LBx)).
      { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
        set (bf := blocks_of (sl_file sl) (sl_file_o sl)) in *. set (bg := blocks_of (sl_func sl) (sl_func_o sl)) in *.
        set (SBn := blocks_slots (skipn (S (Z.to_nat i)) ss)) in *.
        apply (Permutation_app_inv_l (bf ++ bg)). rewrite <- (app_assoc bf bg L4).
        eapply Permutation_trans; [apply Permutation_app_head; exact PM4|].
        eapply Permutation_trans; [exact PM2|]. rewrite SPL. rewrite <- (app_assoc (bf ++ bg) SBn LBx). apply Permutation_refl. }
      (* [comment removed for export] *)
      assert (XES : forall ma mb, munch [(es, es + 904)] ma mb -> wmono usegs ma mb -> xpres LB0 SP X ma mb).
      { intros ma mb MUx WMx. eapply xpres_of_munch_gen; [exact MUx| exact WMx|]. intros a Ha HC. cbn. split; [| exact I]. intros Hr. exact (NCL a Hr HC). }
      assert (XFR : forall L' ma mb, xpres L' (spx + -64) [] ma mb -> (forall b, In b LBx -> In b L') -> xpres LB0 SP X ma mb).
      { intros L' ma mb XPx SUBx'. eapply xpres_weaken; [exact XPx| unfold spx; lia| intros b Hb; apply SUBx'; apply SUB0; exact Hb| intros a []]. }
      apply (sr_done H HH). unfold ec_inv. cbn [cfg_ms cfg_model].
      exists (Z_to_bv 64 ECL_RA), w0, w1, w2, d0, d1, d2, d3, d4, d5, d6, d7, w3, w4, w5, w6, m5, s4'.
      split; [reflexivity|]. split; [exact KREL4|]. split; [eapply (mpres_trans H HH); [exact MP| eapply (mpres_trans H HH); [exact MP2| exact MP4]]|].
      split; [exact MI5|]. split; [exact ST5|]. split; [exact ERR5|]. split; [exact AUX5|].
      split; [eapply PERM; [exact HP5| exact PMF]|]. split; [exact CW5|]. split; [exact EM5|]. split; [exact FR5|].
      eapply xpres_trans; [exact XP|]. eapply xpres_trans; [exact XST|]. eapply xpres_trans; [apply (XES _ _ MU1 WM1)|]. eapply xpres_trans; [apply (XFR _ _ _ XP2 SUBK2)|].
      eapply xpres_trans; [apply (XES _ _ MU3 WM3)|]. eapply xpres_trans; [apply (XFR _ _ _ XP4 SUBK4)|]. apply (XES _ _ MU5 WM5).
    Qed.

    Lemma ec_loop : forall n i, i = 16 - Z.of_nat n -> 0 <= i -> forall k, ec_inv i k -> hs_SR H (ec_inv 16) k.
    Proof.
      induction n as [|n IH]; intros i Ei Hi k INV.
      - replace i with 16 in INV by lia. apply (sr_done H HH). exact INV.
      - eapply (sr_seq H HH); [apply (ec_trip i ltac:(lia) k INV)|]. intros k' INV'. apply (IH (i + 1)); [lia| lia| exact INV'].
    Qed.
  End Loop.

  Lemma errclear_spec : errclear_stmt H.
  Proof.
    unfold errclear_stmt. intros until errv. intros HP KREL BY CN BG AUX SPB SPA ST CEIL LO LO64 ERR MI TP MF IM GM RL EP EX EB CP RAE.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (STK1 : 48 + errph_stack ph <= bv_unsigned sp - lo /\ 112 + 8208 <= bv_unsigned sp - lo).   (* [comment removed for export] *)
    { unfold ERRCLEAR_STACK, FR_ERR_clear_error, CFREE_STACK, RFREE_STACK in LO. destruct ph; cbn [errph_stack] in *;
        unfold ERRCLEAR_STACK, FR_ERR_clear_error, CFREE_STACK, RFREE_STACK, ERRINIT_STACK, EGS_STACK, FR_ossl_err_get_state_int, CINITCRYPTO_STACK, FR_OPENSSL_init_crypto, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock, RREALLOC_STACK in *; lia. }
    set (SB := blocks_ERRST E) in *.
    assert (SUBx : forall b, In b LB -> In b (SB ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
    assert (RBL : forall b, In b LB -> rblock_range (blk_addr b) (blk_size b)).
    { intros b Hb. eapply (HH_RHEAP_block_range H HH); [exact HP| apply SUBx; exact Hb]. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply ec_seg0 with (lo := lo); [exact ST| exact CEIL| lia| exact MI]|].
    intros ms1 (m1 & j & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (HP1 : hs_RHEAP H s (SB ++ LB) m1).
    { eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (AUX1 : hs_rauxv_ok H m1 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]. unfold RAUXV_CELL. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    subst tp. rewrite errno_RATP in ERR.
    apply (rw_cells_transport usegs _ m m1 _ _ ERR) in MU1 as ERR1; [| exact WM1| unfold RERRNO; cbn; lia].
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
    { eapply (EGS ph E) with (save := 0) (lo := lo) (B := B) (LB := LB) (s := s) (x := x) (errv := errv);
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia;
        first [ intros _; left; reflexivity | apply mod16_sub64; exact SPA | rewrite errno_RATP; exact ERR1 ]. }
    intros [ms2 mo2] PO. unfold egs_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & s2' & LBN & c &
                    -> & MP2 & (KREL2 & MI2 & ST2 & AUX2 & HP2 & MF2 & IM2 & GM2 & RL2) & ERR2 & ERRV2 & DL & EP2 & CP2 & EST2 & XP2).
    rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST2, XP2 by lia. rewrite errno_RATP in ERR2.
    assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -48) (ec_frame j s3 s2 s1 s0 ra)).
    { eapply xpres_rw_cells'; [exact XP2| exact FR1| left; cbn; lia|].
      unfold ERR_X, A_err_string_once, A_defctx_inited, A_tevent_once, A_load_strings_once, A_optsdone, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, A_tsd_main.
      repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
    set (es := blk_addr (ec_es c)) in *.
    pose proof EP2 as [ES2 EC2]. pose proof EC2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
    assert (SUB2 : forall b, In b (LBN ++ LB) -> In b (SB ++ LBN ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP2 (SUB2 _ I5)) as RB5. unfold rblock_range in RB5. rewrite Z5 in RB5. fold es in RB5. unfold ERRST_SIZE in RB5.
    apply ERRST_split in EST2. destruct EST2 as [EM2 OWN]. pose proof EM2 as (SL & _).
    pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ HP2) as ND2.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL2| eapply ec_seg1 with (es := es); [lia| lia| exact MI2]|].
    intros ms3 ->.
    assert (ESAL : es mod 8 = 0) by (clear - RB5; lia).
    (* [comment removed for export] *)
    set (X := ERR_X ++ errph_foot ph).
    assert (NCL : forall a, es <= a < es + 904 -> ~ xclient LB (bv_unsigned sp) X a).
    { intros a Hr [HC HXn].
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
    (* [comment removed for export] *)
    assert (CW2 : C4W (LBN ++ LB) m2 (ErrReady c) x) by (unfold C4W; tauto).
    eapply (sr_seq H HH).
    { eapply (ec_loop sp gp (Z_to_bv 64 RATP) sp s4 s5 s6 s7 s8 s9 s10 s11 F fc s3 s2 s1 s0 ra j E c x (LBN ++ LB) LB (bv_unsigned sp) lo B X errv2 m2 mo2
                eq_refl SL OWN ltac:(intros b Hb; apply in_or_app; right; exact Hb) NCL CEIL ltac:(lia) ESAL SPB ltac:(lia) 16%nat 0 ltac:(lia) ltac:(lia)).
      unfold ec_inv. cbn [cfg_ms cfg_model]. fold es.
      exists (Z_to_bv 64 EC_RA0), u0, u1, u2, (Z_to_bv 64 es), b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, s2'.
      split; [reflexivity|]. split; [exact KREL2|]. split; [apply (mpres_refl H HH)|]. split; [exact MI2|]. split; [exact ST2|].
      split; [exact ERR2|]. split; [exact AUX2|]. split; [exact HP2|]. split; [exact CW2|].
      split; [destruct E; exact EM2|]. split; [exact FR2| apply xpres_refl]. }
    intros [ms4 mo4] INV. unfold ec_inv in INV. cbn [cfg_ms cfg_model] in INV. fold es in INV.
    destruct INV as (ra4 & w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m4 & s4' &
                     -> & KREL4 & MP4 & MI4 & ST4 & ERR4 & AUX4 & HP4 & CW4 & EM4 & FR4 & XP4).
    change (16 <? 16) with false in *. cbv iota in *.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL4| eapply ec_segD with (es := es) (lo := lo) (E := clr E 16); [exact ESAL| exact EM4| lia| lia| lia| exact MI4| exact ST4| exact FR4]|].
    intros ms5 (a0'' & m5 & -> & MU5 & WM5 & MI5 & ST5 & EM5).
    assert (SUB4 : forall b, In b (LBN ++ LB) -> In b (blocks_slots (skipn (Z.to_nat 16) (es_slots E)) ++ LBN ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
    assert (ESK : skipn (Z.to_nat 16) (es_slots E) = []) by (apply skipn_all2; lia).
    (* [comment removed for export] *)
    pose proof CW4 as CW4'.
    assert (W5 : hs_RHEAP H s4' (LBN ++ LB) m5 /\ C4W (LBN ++ LB) m5 (ErrReady c) x /\ hs_rauxv_ok H m5 B /\ rw_cells usegs m5 RERRNO [C4 errv2]).
    { destruct (es_world H HH _ _ _ _ m5 _ _ _ _ _ _ _ _ HP4 SUB4 CW4 AUX4 ERR4 ST4 FR4 CEIL ltac:(lia) ltac:(lia) MU5 WM5) as (K1 & K2 & K3 & K4 & _).
      rewrite ESK in K1. cbn [blocks_slots map concat app] in K1. tauto. }
    destruct W5 as (HP5 & CW5 & AUX5 & ERR5). destruct CW5 as (MF5 & IM5 & GM5 & RL5 & EP5 & CP5).
    apply (sr_done H HH). unfold errclear_post. cbn [cfg_ms cfg_model].
    exists w0, w1, w2, a0'', d1, d2, d3, d4, d5, d6, d7, w3, w4, w5, w6, m5, errv2, s4', LBN, c.
    split; [reflexivity|]. split; [eapply (mpres_trans H HH); [exact MP2| exact MP4]|].
    split; [unfold c4_frame; cbn [cfg_model]; tauto|].
    split; [rewrite errno_RATP; exact ERR5|]. split; [exact DL|]. split; [exact EP5|]. split; [exact CP5|].
    split.
    { apply ERRST_split. split.
      - unfold clr in EM5. cbn [es_slots] in EM5. replace (Z.to_nat 16) with (length (es_slots E)) in EM5 by lia.
        rewrite clr_slots_all, SL in EM5. exact EM5.
      - unfold ERROWN, errst_cleared. cbn [es_slots]. apply Forall_forall. intros s0' Hs. apply repeat_spec in Hs. subst s0'. cbn. split; reflexivity. }
    eapply xpres_trans; [exact XP01|].
    eapply xpres_trans; [eapply xpres_weaken; [exact XP2| lia| auto| intros a Ka; unfold X; apply rin_ivs_app; left; exact Ka]|].
    eapply xpres_trans; [exact XP4|].
    eapply xpres_of_munch_gen; [exact MU5| exact WM5|]. intros a Ha HC. cbn. split; [| exact I]. intros Hr. exact (NCL a Hr HC).
  Qed.
End W.
