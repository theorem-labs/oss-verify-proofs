(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame Mem.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX AsAtomics ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C3 ECH_AStmt_C6 ECH_AStmt_C7 ECH_AStmt_C8 ECH_AStmt_C9 ECH_AKit ECH_AsKit ECH_AC7_kit ECH_AC7_free ECH_AC9_new.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj InNth.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac if_lit :=
    match goal with
    | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        tryif (match c with context [?x] => is_var x end) then fail 1 "if_lit: open condition" else
        let v := eval vm_compute in c in replace c with v by (vm_compute; reflexivity); cbv iota
    end.
  Local Ltac reacc ACC0 MU NSW :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch type of ACC0 with accessible _ ?x ?n =>
        let T := fresh "ACC" in
        assert (T : accessible mx x n) by (eapply accessible_across2; [exact ACC0| exact MU| exact NSW])
      end end.

  Definition AFA_RA : Z := R_BIO_free_all_BIO_free_int.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma afa_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a lo : Z) (B : biorep),
      a0 = Z_to_bv 64 a -> aapp a BIO_SIZE -> a mod 8 = 0 ->
      0 <= bio_method B < 2^64 -> 0 <= bio_init B < 2^32 -> 0 <= bio_shutdown B < 2^32 -> 0 <= bio_flags B < 2^32 -> 0 <= bio_retry B < 2^32 -> 0 <= bio_numf B < 2^32 ->
      0 <= bio_ptr B < 2^64 -> 0 <= bio_next B < 2^64 -> 0 <= bio_prev B < 2^64 -> 0 <= bio_refs B < 2^32 -> 0 <= bio_nread B < 2^64 -> 0 <= bio_nwrite B < 2^64 ->
      rw_cells asegs m a (bio_cells B) -> accessible m a BIO_SIZE -> ACONST m ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1 j,
          ms' = MS (mkR (Z_to_bv 64 AFA_RA) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 SHB)
                       (Z_to_bv 64 a) (Z_to_bv 64 (bv_unsigned sp + -36)) (Z_to_bv 64 0) a3 a4 a5 a6 a7 (Z_to_bv 64 (bio_next B)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_free_int) fc None m1 (seg_rom asegs)
          /\ munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (bv_unsigned sp + -48)
          /\ rw_cells asegs m1 (bv_unsigned sp + -48) [CB 12 j] /\ rw_cells asegs m1 (bv_unsigned sp + -36) [C4 (wz 0)]
          /\ rw_cells asegs m1 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BIO_free_all) fc None m (seg_rom asegs)).
  Proof.
    intros until B. intros A0 AAP AAL M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 BC ACCA AC ST CEIL LO MI. subst a0. acb.
    pose proof (aapp_bounds _ _ AAP ltac:(unfold BIO_SIZE; lia)) as (AH & ACE & AHI & AP & _). unfold AIMG_TOP in AH. unfold AAPP_HI in AHI.
    pose proof (aapp_not_shadowland _ _ AAP) as NSA. unfold ALOWSH_LO, AHI_LO in NSA.
    unfold P_BIO_free_all, P_BIO_free_int, AFA_RA, R_BIO_free_all_BIO_free_int, BIO_SIZE, SHB in *.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    unfold bio_cells, wz in BC.
    pose proof (ACONST_shbase _ AC) as [GSB SHB0]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(bv_unsigned sp + -48, bv_unsigned sp)]) by nsw_tac.
    hide NSA.
    (* [comment removed for export] *)
    carve_frame 48%nat ST. step. do 4 st1. step. step. st1. st1.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ ?mx _ [CB 16 ?jj; C8 ?x2; C8 ?x1; C8 ?x0; C8 ?xr] =>
      change ([CB 16 jj; C8 x2; C8 x1; C8 x0; C8 xr]) with ([CB 16 jj] ++ [C8 x2; C8 x1; C8 x0; C8 xr]) in FR end.
    destruct (proj1 (rw_cells_app asegs _ _ _ _) FR) as [FRj FRhi]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRhi.
    lazymatch type of FRj with rw_cells _ ?mx _ [CB 16 ?jj] =>
      assert (FRj' : rw_cells asegs mx (bv_unsigned sp + -48) ([CB 12 (firstn 12 jj)] ++ CB 4 (skipn 12 jj) :: []))
        by (eapply arw_cells_recut; [exact FRj| cbn; pose proof (proj1 (proj1 FRj)) as W; cbn in W; rewrite length_firstn, length_skipn; repeat split; lia
                                     | cbn [cells_bytes cbytes app]; rewrite !app_nil_r; apply firstn_skipn]) end.
    apply rw_cells_CB4_C4 in FRj'. destruct (proj1 (rw_cells_app asegs _ _ [CB 12 _] [C4 _]) FRj') as [FR12 FR4].
    lazymatch type of FR4 with rw_cells _ _ ?adr _ => replace adr with (bv_unsigned sp + -36) in FR4 by (cbn; lia) end.
    lazymatch type of FRhi with rw_cells _ _ ?adr _ => replace adr with (bv_unsigned sp + -32) in FRhi by (cbn; lia) end.
    clear FR FRj FRj'.
    (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    step. ubal_by AAL. step. if_lit.
    zstep. zstep. zstep. reacc ACCA MU NSW. ck8_check ACC (a + 72). clear ACC. st1.
    st1. zstep. step.
    finish; try eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma afa_seg2 :
    forall (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mb lo : Z) (B : biorep),
      0 < mb -> aapp mb BIO_SIZE -> mb mod 8 = 0 ->
      0 <= bio_method B < 2^64 -> 0 <= bio_init B < 2^32 -> 0 <= bio_shutdown B < 2^32 -> 0 <= bio_flags B < 2^32 -> 0 <= bio_retry B < 2^32 -> 0 <= bio_numf B < 2^32 ->
      0 <= bio_ptr B < 2^64 -> 0 <= bio_next B < 2^64 -> 0 <= bio_prev B < 2^64 -> 0 <= bio_refs B < 2^32 -> 0 <= bio_nread B < 2^64 -> 0 <= bio_nwrite B < 2^64 ->
      rw_cells asegs m mb (bio_cells B) -> accessible m mb BIO_SIZE ->
      rw_cells asegs m (bv_unsigned sp + -36) [C4 (wz 0)] ->
      stk asegs m lo (bv_unsigned sp + -48) -> aceil <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 AFA_RA) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 SHB)
                       (Z_to_bv 64 mb) (Z_to_bv 64 (bv_unsigned sp + -36)) (Z_to_bv 64 0) a3 a4 a5 a6 a7 (Z_to_bv 64 (bio_next B)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_free_int) fc None m1 (seg_rom asegs)
          /\ munch [(bv_unsigned sp + -36, bv_unsigned sp + -32)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (bv_unsigned sp + -48)
          /\ rw_cells asegs m1 (bv_unsigned sp + -36) [C4 (wz 0)])
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 SHB) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 mb) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AFA_RA)) fc None m (seg_rom asegs)).
  Proof.
    intros until B. intros MBP MAP MAL M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 BC ACCM SL ST CEIL LO MI. acb.
    pose proof (aapp_bounds _ _ MAP ltac:(unfold BIO_SIZE; lia)) as (MH & MCE & MHI & MP & _). unfold AIMG_TOP in MH. unfold AAPP_HI in MHI.
    pose proof (aapp_not_shadowland _ _ MAP) as NSM. unfold ALOWSH_LO, AHI_LO in NSM.
    unfold P_BIO_free_int, AFA_RA, R_BIO_free_all_BIO_free_int, BIO_SIZE, SHB in *.
    replace (ret_pc (Z_to_bv 64 0x239168)) with (Z_to_bv 64 0x239168) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    unfold bio_cells, wz in BC. unfold wz in SL.
    pose proof (munch_refl [(bv_unsigned sp + -36, bv_unsigned sp + -32)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(bv_unsigned sp + -36, bv_unsigned sp + -32)]) by nsw_tac.
    hide NSM.
    (* [comment removed for export] *)
    st1. step. step. if_lit.
    step. if_cases K1; zify_cond K1; [kill K1|]. clear K1.
    step. ubal_by MAL. step. if_lit.
    zstep. zstep. zstep. reacc ACCM MU NSW. ck8_check ACC (mb + 72). clear ACC. st1.
    st1. zstep. step.
    finish; try eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma afa_seg3 :
    forall (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (s2o s1o s0o rao : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (j : list byte),
      rw_cells asegs m (bv_unsigned sp + -48) [CB 12 j] -> rw_cells asegs m (bv_unsigned sp + -36) [C4 (wz 0)] ->
      rw_cells asegs m (bv_unsigned sp + -32) [C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
      stk asegs m lo (bv_unsigned sp + -48) -> aceil <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv asegs m -> bv_unsigned rao mod 2 = 0 ->
      evt asegs (fun ms' =>
          ms' = MS (mkR rao sp gp tp t0 t1 t2 s0o s1o (Z_to_bv 64 0) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2o s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc rao) fc None m (seg_rom asegs)
          /\ stk asegs m lo (bv_unsigned sp))
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 SHB) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AFA_RA)) fc None m (seg_rom asegs)).
  Proof.
    intros until j. intros FRJ SL FRH ST CEIL LO MI RAE. acb. unfold AFA_RA, R_BIO_free_all_BIO_free_int, SHB in *.
    replace (ret_pc (Z_to_bv 64 0x239168)) with (Z_to_bv 64 0x239168) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). unfold wz in SL.
    (* [comment removed for export] *)
    st1. step. step. if_lit. step. if_lit.
    do 4 st1. step.
    release_frame FRJ ST (bv_unsigned sp + -36). release_frame SL ST (bv_unsigned sp + -32). release_frame FRH ST (bv_unsigned sp).
    step.
    apply evt_done. split; [reflexivity| exact ST].
  Qed.
End S.
