(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCallX AsWalk AsAtomics ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AKit ECH_AsKit ECH_AKitS ECH_AStmt_C0 ECH_AStmt_C1 ECH_AC1_free ECH_AC1_freeopt ECH_AStmt_C2 ECH_APF_C4 ECH_AStmt_C4 ECH_AC4_rep ECH_AC4_frame ECH_AC4_egs.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition AEC_LOOP : Z := 0x1f25fc.  Definition AEC_EXIT : Z := 0x1f2614.
Definition AEC_RA0 : Z := 0x1f25ec.   (* [comment removed for export] *)
Definition AEC_RA1 : Z := 0x1f1f94.   (* [comment removed for export] *)
Definition AEC_RA2 : Z := 0x1f1fd4.   (* [comment removed for export] *)
Definition AEC_FILE : Z := 0x40b8f.   (* [comment removed for export] *)
Definition SHBv : Z := 0x7fff8000.
Definition AEC_RAL : Z := 0x1f260c.
Definition AEC_ECL : Z := 0x1f1dfc.

Ltac ret_lit RA := replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
Ltac ret_lit_any := match goal with |- context [ret_pc (Z_to_bv 64 ?r)] => ret_lit r end.
Ltac show_goal := match goal with |- evt _ _ (MS ?R _ ?pc _ _ ?mx _) => idtac "PC" pc; idtac R end.
Ltac acc_now ACC BASE MUS NSW :=
  lazymatch type of BASE with accessible _ ?a ?n =>
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACC : accessible mx a n) by (eapply accessible_across; [exact BASE| exact MUS| exact NSW]) end end.
Ltac ck8_now BASE MUS NSW a := let ACC := fresh "ACC" in acc_now ACC BASE MUS NSW; sh_align a; ck8_load ACC a; step;
  first [if_false_by (ck1_bnez_false 0 eq_refl) | if_true_by (@eq_refl bool true)]; clear ACC.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  Definition aec_frame (s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
    [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Definition aecl_frame (j : list byte) (s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 : word) : list cell :=
    [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 (Z_to_bv 64 AEC_RAL)].

  (* [comment removed for export] *)
  Lemma aec_seg0 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      ACONST m -> stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 96 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 AEC_RA0) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                       s2 (Z_to_bv 64 SHBv) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_ossl_err_get_state_int) fc None m1 (seg_rom asegs)
          /\ munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp + -48)
          /\ rw_cells asegs m1 (bv_unsigned sp + -48) (aec_frame s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_ERR_clear_error) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros AC ST CEIL LO MI. unfold P_ERR_clear_error, P_ossl_err_get_state_int, AEC_RA0, SHBv, aec_frame. acb.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (ACONST_shbase m AC) as [GSB SHB0]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 48%nat ST. bgo. step. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma aec_seg1 :
    forall (spx gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (es : Z),
      0 < es < 2^47 ->
      evt asegs (fun ms' => exists a0',
          ms' = MS (mkR (Z_to_bv 64 AEC_RA0) spx gp tp t0 t1 t2 s0 (Z_to_bv 64 es) a0' a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 0) s3 (Z_to_bv 64 16) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 AEC_LOOP) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AEC_RA0) spx gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 es) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AEC_RA0)) fc None m (seg_rom asegs)).
  Proof.
    intros until es. intros ESR. unfold AEC_RA0, AEC_FILE. ret_lit_any.
    bgo_to AEC_LOOP. unfold AEC_LOOP.
    finish.
  Qed.

  Lemma aec_segA0 :
    forall (ra0 spx gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (es i lo : Z) (E : errst),
      ERRSTm m es E -> 0 <= i < 16 -> 0 < es -> es + 904 < 2^47 -> es mod 16 = 0 -> aapp es 904 -> accessible m es 904 -> mem_inv asegs m ->
      stk asegs m lo (bv_unsigned spx) -> aceil <= lo -> lo <= bv_unsigned spx - 96 -> es + 904 <= lo -> ACONST m ->
      evt asegs (fun ms' => exists j a0' m1,
          ms' = MS (mkR (Z_to_bv 64 AEC_RAL) (Z_to_bv 64 (bv_unsigned spx + -96)) gp tp t0 t1 t2 spx (Z_to_bv 64 es) a0' (Z_to_bv 64 i)
                       (Z_to_bv 64 0) a3 a4 a5 a6 a7 (Z_to_bv 64 (es + i * 4)) (Z_to_bv 64 (es + i * 4 + 512)) (Z_to_bv 64 16)
                       (Z_to_bv 64 SHBv) s6 (Z_to_bv 64 (i * 4)) (Z_to_bv 64 (Z.shiftr (es + i * 4 + 512) 3 + SHBv)) s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 AEC_ECL) fc None m1 (seg_rom asegs)
          /\ munch [(bv_unsigned spx + -96, bv_unsigned spx)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned spx + -96)
          /\ rw_cells asegs m1 (bv_unsigned spx + -96) (aecl_frame j s9 s8 s7 s6 s5 (Z_to_bv 64 16) s3 (Z_to_bv 64 i) (Z_to_bv 64 es) s0)
          /\ ERRSTm m1 es E /\ accessible m1 es 904)
        (MS (mkR ra0 spx gp tp t0 t1 t2 s0 (Z_to_bv 64 es) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 i) s3 (Z_to_bv 64 16)
                 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AEC_LOOP) fc None m (seg_rom asegs)).
  Proof.
    intros until E. intros EST TR' POS BL AL AP ACC0 MI ST CEIL LO ESLO AC. unfold AEC_LOOP, SHBv, aecl_frame. acb.
    pose proof (aword_range spx) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned spx + -96, bv_unsigned spx)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(bv_unsigned spx + -96, bv_unsigned spx)])
      by (apply Forall_cons; [cbn [fst snd]; unfold AHI_LO in *; lia| apply Forall_nil]).
    unfold ERRSTm in EST. destruct EST as (SL & TR & BR & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & TB & RG).
    unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP in *.
    arr_lens SL.
    pose proof (ACONST_shbase m AC) as [GSB SHB0]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    carve_frame 96%nat ST. bgo. step. bgo.
    finish.
    + exact FR.
    + unfold ERRSTm. unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP.
      repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
    + eapply accessible_across; [exact ACC0| exact MU| exact NSW].
  Qed.

  (* [comment removed for export] *)
  Lemma aec_segA :
    forall (spx gp tp t0 t1 t2 a0 a3 a4 a5 a6 a7 s6 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (es i : Z) (E : errst),
      ERRSTm m es E -> 0 <= i < 16 -> 0 < es -> es + 904 < 2^47 -> es mod 16 = 0 -> aapp es 904 -> accessible m es 904 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists u0 u1 u2 a3' a4' a5' a6' a7' m1,
          ms' = MS (mkR (Z_to_bv 64 AEC_RA1) (Z_to_bv 64 (bv_unsigned spx + -96)) gp tp u0 u1 u2 spx (Z_to_bv 64 es)
                       (Z_to_bv 64 (sl_file (slot_at E i))) (Z_to_bv 64 AEC_FILE) (Z_to_bv 64 112) a3' a4' a5' a6' a7'
                       (Z_to_bv 64 (es + i * 8 + 576)) (Z_to_bv 64 (Z.shiftr (es + i * 8 + 576) 3 + SHBv)) (Z_to_bv 64 16)
                       (Z_to_bv 64 SHBv) (Z_to_bv 64 (i * 8)) (Z_to_bv 64 (i * 4)) (Z_to_bv 64 (Z.shiftr (es + i * 4 + 512) 3 + SHBv))
                       s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m1 (seg_rom asegs)
          /\ munch [(es, es + 904)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ ERRSTm m1 es (es_with_slot E i (slot_wipe (slot_at E i))) /\ accessible m1 es 904)
        (MS (mkR (Z_to_bv 64 AEC_RAL) (Z_to_bv 64 (bv_unsigned spx + -96)) gp tp t0 t1 t2 spx (Z_to_bv 64 es) a0 (Z_to_bv 64 i)
                 (Z_to_bv 64 0) a3 a4 a5 a6 a7 (Z_to_bv 64 (es + i * 4)) (Z_to_bv 64 (es + i * 4 + 512)) (Z_to_bv 64 16)
                 (Z_to_bv 64 SHBv) s6 (Z_to_bv 64 (i * 4)) (Z_to_bv 64 (Z.shiftr (es + i * 4 + 512) 3 + SHBv)) s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AEC_ECL) fc None m (seg_rom asegs)).
  Proof.
    intros until E. intros EST TR' POS BL AL AP ACC0 MI. unfold AEC_RA1, AEC_ECL, AEC_FILE, P_CRYPTO_free, SHBv.
    pose proof (munch_refl [(es, es + 904)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(es, es + 904)])
      by (apply Forall_cons; [cbn [fst snd]; exact (aapp_not_shadowland _ _ AP)| apply Forall_nil]).
    unfold ERRSTm in EST. destruct EST as (SL & TR & BR & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & TB & RG).
    unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP in *.
    arr_lens SL.
    (* [comment removed for export] *)
    ck8_now ACC0 MU NSW (es + i * 4 + 512).
    pose proof (zero16_byte_m _ _ i F6 TR') as RD. replace (es + 512 + i * 4) with (es + i * 4 + 512) in RD by lia. bgo. clear RD.
    (* [comment removed for export] *)
    bgo. ck8_now ACC0 MU NSW (es + i * 8 + 256). bgo. arr_store64 F4 i (wz 0). rewrite upd_zero16 in F4 by lia.
    bgo. ck8_now ACC0 MU NSW (es + i * 8 + 384). bgo. arr_store64 F5 i (wz 0). rewrite upd_zero16 in F5 by lia.
    (* [comment removed for export] *)
    bgo. ck8_now ACC0 MU NSW (es + i * 4 + 512). bgo. arr_store32 F6 i (wz 0). rewrite upd_zero16 in F6 by lia.
    (* [comment removed for export] *)
    bgo. ck8_now ACC0 MU NSW (es + i * 4 + 64). bgo. arr_store32 F2 i (wz 0). rewrite upd_zero16 in F2 by lia.
    (* [comment removed for export] *)
    bgo. ck8_now ACC0 MU NSW (es + i * 4). bgo. arr_store32 F1 i (wz 0).
    (* [comment removed for export] *)
    bgo. ck8_now ACC0 MU NSW (es + i * 8 + 128). bgo. arr_store64 F3 i (wz 0).
    (* [comment removed for export] *)
    bgo. ck8_now ACC0 MU NSW (es + i * 4 + 704).
    bgo. arr_store32 F8 i (Z_to_bv 64 (-1)). apply (u32arr_upd_le4 _ _ _ _ _ _ le4_minus1) in F8.
    (* [comment removed for export] *)
    bgo. ck8_now ACC0 MU NSW (es + i * 8 + 576).
    pose proof (u64arr_read_m _ _ _ i _ F7 (slot_nth E i (fun s => wz (sl_file s)) SL TR') ltac:(lia)) as RD.
    replace (es + 576 + i * 8) with (es + i * 8 + 576) in RD by lia. bgo. step. clear RD.
    finish.
    + eapply (ERRSTm_with_slot _ es E i (slot_wipe (slot_at E i))); try eassumption; try reflexivity;
        try (upd_keep_tac E i SL TR'); cbn [slot_wipe sl_flags sl_buffer sl_line]; lia.
    + eapply accessible_across; [exact ACC0| exact MU| exact NSW].
  Qed.

  (* [comment removed for export] *)
  Lemma aec_segB :
    forall (spx gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (es i : Z) (E : errst),
      ERRSTm m es E -> 0 <= i < 16 -> 0 < es -> es + 904 < 2^47 -> aapp es 904 -> accessible m es 904 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists u0 u1 u2 a3' a4' a5' a6' a7' m1,
          ms' = MS (mkR (Z_to_bv 64 AEC_RA2) (Z_to_bv 64 (bv_unsigned spx + -96)) gp tp u0 u1 u2 spx (Z_to_bv 64 (es + i * 8 + 768))
                       (Z_to_bv 64 (sl_func (slot_at E i))) (Z_to_bv 64 AEC_FILE) (Z_to_bv 64 114) a3' a4' a5' a6' a7'
                       (Z_to_bv 64 (es + i * 8 + 576)) (Z_to_bv 64 (Z.shiftr (es + i * 8 + 576) 3 + SHBv)) (Z_to_bv 64 16)
                       (Z_to_bv 64 (Z.shiftr (es + i * 8 + 768) 3 + SHBv)) (Z_to_bv 64 (i * 8)) (Z_to_bv 64 (i * 4))
                       (Z_to_bv 64 (Z.shiftr (es + i * 4 + 512) 3 + SHBv)) s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m1 (seg_rom asegs)
          /\ munch [(es, es + 904)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ ERRSTm m1 es (es_with_slot E i (slot_file0 (slot_at E i))) /\ accessible m1 es 904)
        (MS (mkR (Z_to_bv 64 AEC_RA1) (Z_to_bv 64 (bv_unsigned spx + -96)) gp tp t0 t1 t2 spx (Z_to_bv 64 es) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 (es + i * 8 + 576)) (Z_to_bv 64 (Z.shiftr (es + i * 8 + 576) 3 + SHBv)) (Z_to_bv 64 16)
                 (Z_to_bv 64 SHBv) (Z_to_bv 64 (i * 8)) (Z_to_bv 64 (i * 4)) (Z_to_bv 64 (Z.shiftr (es + i * 4 + 512) 3 + SHBv))
                 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AEC_RA1)) fc None m (seg_rom asegs)).
  Proof.
    intros until E. intros EST TR' POS BL AP ACC0 MI. unfold AEC_RA1, AEC_RA2, AEC_FILE, P_CRYPTO_free, SHBv. ret_lit_any.
    pose proof (munch_refl [(es, es + 904)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(es, es + 904)])
      by (apply Forall_cons; [cbn [fst snd]; exact (aapp_not_shadowland _ _ AP)| apply Forall_nil]).
    unfold ERRSTm in EST. destruct EST as (SL & TR & BR & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & TB & RG).
    unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP in *.
    arr_lens SL.
    (* [comment removed for export] *)
    bgo. ck8_now ACC0 MU NSW (es + i * 8 + 576). bgo. arr_store64 F7 i (wz 0).
    bgo. ck8_now ACC0 MU NSW (es + i * 8 + 768).
    pose proof (u64arr_read_m _ _ _ i _ F9 (slot_nth E i (fun s => wz (sl_func s)) SL TR') ltac:(lia)) as RD.
    replace (es + 768 + i * 8) with (es + i * 8 + 768) in RD by lia. bgo. step. clear RD.
    finish.
    + pose proof (slot_at_own _ E i RG SL TR') as (O1 & O2 & O3).
      eapply (ERRSTm_with_slot _ es E i (slot_file0 (slot_at E i))); try eassumption; try reflexivity;
        try (upd_keep_tac E i SL TR'); cbn [slot_file0 sl_flags sl_buffer sl_line]; lia.
    + eapply accessible_across; [exact ACC0| exact MU| exact NSW].
  Qed.

  (* [comment removed for export] *)
  Lemma aec_segC :
    forall (spx gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 s0c s3c s5c s6c s7c s8c : word) (j : list byte)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (es i lo : Z) (E : errst),
      ERRSTm m es E -> 0 <= i < 16 -> 0 < es -> es + 904 < 2^47 -> aapp es 904 -> accessible m es 904 -> mem_inv asegs m ->
      stk asegs m lo (bv_unsigned spx + -96) -> aceil <= lo -> lo <= bv_unsigned spx - 96 -> es + 904 <= lo ->
      rw_cells asegs m (bv_unsigned spx + -96) (aecl_frame j s9 s8c s7c s6c s5c (Z_to_bv 64 16) s3c (Z_to_bv 64 i) (Z_to_bv 64 es) s0c) ->
      evt asegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m1,
          ms' = MS (mkR (Z_to_bv 64 AEC_RAL) spx gp tp t0' t1' t2' s0c (Z_to_bv 64 es) a0' a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 (i + 1)) s3c (Z_to_bv 64 16) s5c s6c s7c s8c s9 s10 s11 t3' t4' t5' t6')
                   F (Z_to_bv 64 (if i + 1 <? 16 then AEC_LOOP else AEC_EXIT)) fc None m1 (seg_rom asegs)
          /\ munch [(es, es + 904)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned spx)
          /\ ERRSTm m1 es (es_with_slot E i (slot_func0 (slot_at E i))) /\ accessible m1 es 904)
        (MS (mkR (Z_to_bv 64 AEC_RA2) (Z_to_bv 64 (bv_unsigned spx + -96)) gp tp t0 t1 t2 spx (Z_to_bv 64 (es + i * 8 + 768))
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 (es + i * 8 + 576)) (Z_to_bv 64 (Z.shiftr (es + i * 8 + 576) 3 + SHBv)) (Z_to_bv 64 16)
                 (Z_to_bv 64 (Z.shiftr (es + i * 8 + 768) 3 + SHBv)) (Z_to_bv 64 (i * 8)) (Z_to_bv 64 (i * 4))
                 (Z_to_bv 64 (Z.shiftr (es + i * 4 + 512) 3 + SHBv)) s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AEC_RA2)) fc None m (seg_rom asegs)).
  Proof.
    intros until E. intros EST TR' POS BL AP ACC0 MI ST CEIL LO ESLO FR.
    unfold AEC_RA2, AEC_RAL, AEC_LOOP, AEC_EXIT, SHBv, aecl_frame in *. acb. ret_lit_any.
    pose proof (aword_range spx) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(es, es + 904)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(es, es + 904)])
      by (apply Forall_cons; [cbn [fst snd]; exact (aapp_not_shadowland _ _ AP)| apply Forall_nil]).
    unfold ERRSTm in EST. destruct EST as (SL & TR & BR & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & TB & RG).
    unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP in *.
    arr_lens SL.
    (* [comment removed for export] *)
    bgo. ck8_now ACC0 MU NSW (es + i * 8 + 768). bgo. arr_store64 F9 i (wz 0).
    bgo. release_frame FR ST (bv_unsigned spx). step. unfold AEC_RAL. ret_lit_any.
    bgo. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *) replace (i + 1 <? 16) with true by (symmetry; apply Z.ltb_lt; lia). finish.
      + pose proof (slot_at_own _ E i RG SL TR') as (O1 & O2 & O3).
        eapply (ERRSTm_with_slot _ es E i (slot_func0 (slot_at E i))); try eassumption; try reflexivity;
          try (upd_keep_tac E i SL TR'); cbn [slot_func0 sl_flags sl_buffer sl_line]; lia.
      + eapply accessible_across; [exact ACC0| exact MU| exact NSW].
    - (* [comment removed for export] *) replace (i + 1 <? 16) with false by (symmetry; apply Z.ltb_ge; lia). finish.
      + pose proof (slot_at_own _ E i RG SL TR') as (O1 & O2 & O3).
        eapply (ERRSTm_with_slot _ es E i (slot_func0 (slot_at E i))); try eassumption; try reflexivity;
          try (upd_keep_tac E i SL TR'); cbn [slot_func0 sl_flags sl_buffer sl_line]; lia.
      + eapply accessible_across; [exact ACC0| exact MU| exact NSW].
  Qed.

  (* [comment removed for export] *)
  Lemma aec_segD :
    forall (rax sp gp tp t0 t1 t2 s0x a0 a1 a2 a3 a4 a5 a6 a7 s2x s4x s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (es lo : Z) (E : errst),
      ERRSTm m es E -> 0 < es -> es mod 16 = 0 -> es + 904 <= lo -> aapp es 904 -> accessible m es 904 -> lo <= bv_unsigned sp - 48 -> mem_inv asegs m ->
      stk asegs m lo (bv_unsigned sp + -48) -> rw_cells asegs m (bv_unsigned sp + -48) (aec_frame s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
      bv_unsigned ra mod 2 = 0 ->
      evt asegs (fun ms' => exists a0' a1' m1,
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m1 (seg_rom asegs)
          /\ munch [(es, es + 904)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (bv_unsigned sp)
          /\ ERRSTm m1 es (mkERRST (es_slots E) 0 0))
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0x (Z_to_bv 64 es) a0 a1 a2 a3 a4 a5 a6 a7
                 s2x (Z_to_bv 64 SHBv) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AEC_EXIT) fc None m (seg_rom asegs)).
  Proof.
    intros until E. intros EST POS AL BL AP ACC0 LO MI ST FR RAE. unfold AEC_EXIT, SHBv, aec_frame in *. acb.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(es, es + 904)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(es, es + 904)])
      by (apply Forall_cons; [cbn [fst snd]; exact (aapp_not_shadowland _ _ AP)| apply Forall_nil]).
    unfold ERRSTm in EST. destruct EST as (SL & TR & BR & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & TB & RG).
    unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP in *.
    arr_lens SL.
    (* [comment removed for export] *)
    bgo.
    replace (Z.shiftr (es + 900) 3) with (Z.shiftr (es + 896) 3) by (rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - AL POS; Z.div_mod_to_equations; lia).
    ck8_now ACC0 MU NSW (es + 896). bgo.
    ck8_now ACC0 MU NSW (es + 896). bgo.
    (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp). step. finish.
    unfold ERRSTm. cbn [es_slots es_top es_bottom].
    unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP, wz.
    repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
  Qed.
End S.
