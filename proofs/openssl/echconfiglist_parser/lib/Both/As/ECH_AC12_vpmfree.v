(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C5 ECH_AStmt_C13 ECH_AStmt_C12 ECH_AKit ECH_AsKit ECH_AC1_malloc ECH_AC1_free ECH_AC5_small ECH_AC5_popfree
  ECH_AC13_small ECH_AC13_ext ECH_AC13_entry ECH_AC12_xbuf.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition AVF_R0 : Z := R_X509_VERIFY_PARAM_free_sk_pop_free.     (* [comment removed for export] *)
Definition AVF_R1 : Z := 0x432520.                                  (* [comment removed for export] *)
Definition AVF_R2 : Z := R_X509_VERIFY_PARAM_free_helper_sk_pop_free.   (* [comment removed for export] *)
Definition AVF_R9 : Z := R_X509_VERIFY_PARAM_free_CRYPTO_free.     (* [comment removed for export] *)
Definition AVPMF_FILE : Z := 0xc3200.                               (* [comment removed for export] *)
Definition ASHB12 : Z := 0x7fff8000.
Definition avf_frame (s4 s3 s2 s1 s0 ra : word) : list cell := [C8 s2; C8 s1; C8 s0; C8 ra].
Definition AVF_H : Z := 0x4324cc.
Definition avfh_frame (rh p : Z) (s0h : word) : list cell := [C8 (Z_to_bv 64 ASHB12); C8 (Z_to_bv 64 p); C8 s0h; C8 (Z_to_bv 64 rh)].
(* [comment removed for export] *)
Definition vpm_cells_h (h : Z) : list cell :=
  [CB 36 (zeros 36); C4 (wz 0); C8 (wz (2^64 - 1)); C8 (wz 0); C8 (wz h); C8 (wz 0); C8 (wz 0);
   C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)].
Lemma vpm_cells_h_eq : forall V, vpm_cells V = vpm_cells_h (vp_hosts V).
Proof. intros V. reflexivity. Qed.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac retpc := match goal with |- context [ret_pc (Z_to_bv 64 ?v)] => replace (ret_pc (Z_to_bv 64 v)) with (Z_to_bv 64 v) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
  (* [comment removed for export] *)
  Local Ltac reacc ACC0 MU NSW :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      let A := fresh "ACC" in
      assert (A : accessible mx _ 136) by (unfold id in ACC0; eapply accessible_across; [exact ACC0| exact MU| exact NSW]) end.
  Local Ltac reAC AC0 MU WM AW :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      let A := fresh "ACN" in
      assert (A : ACONST mx) by (unfold id in AC0; eapply ACONST_frame; [exact AC0| exact MU| exact WM| exact AW]) end.
  (* [comment removed for export] *)
  Local Ltac null_call SPEC ST CEIL ACN MU WM :=
    eapply evt_cut;
    [ eapply SPEC; rewrite ?unsigned_lit by lia; [exact ST| exact CEIL| unfold FR_sk_pop_free; lia| | exact ACN];
      lazymatch goal with H : mem_inv _ ?mx |- mem_inv _ ?my => exact H end
    | ];
    let ms' := fresh "ms'" in let PO := fresh "PO" in
    intros ms' PO; unfold sknull_post in PO;
    let m' := fresh "m" in let MU' := fresh "MU'" in let WM' := fresh "WM'" in let MI' := fresh "MI" in let AC' := fresh "ACN" in let ST' := fresh "ST" in
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m' & -> & MU' & WM' & MI' & AC' & ST');
    retpc; rewrite ?unsigned_lit in MU', ST' by lia;
    clear ST ACN; lazymatch goal with H : mem_inv _ ?mx |- _ => lazymatch type of MU' with munch _ mx _ => clear H | _ => idtac end end;
    carry MU' WM'; extend_munch MU WM MU' WM'; rename ST' into ST; rename AC' into ACN.

  (* [comment removed for export] *)
  Lemma avf_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (p h lo : Z),
      rw_cells asegs m p (vpm_cells_h h) -> 0 < p -> p mod 16 = 0 -> p + VPM_SIZE <= lo -> 0 <= h < 2^64 -> aapp p VPM_SIZE -> accessible m p VPM_SIZE ->
      GOT_x509vpm m -> ACONST m ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 64 - FR_sk_pop_free -> mem_inv asegs m ->
      evt asegs (fun ms' => exists u0 u1 u2 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1,
          ms' = MS (mkR (Z_to_bv 64 AVF_R1) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0 u1 u2 (Z_to_bv 64 (bv_unsigned sp + -32)) (Z_to_bv 64 (p + 56))
                       (Z_to_bv 64 h) (Z_to_bv 64 P_sk_X509_BUFFER_freefunc_thunk) b2 b3 b4 b5 b6 b7
                       (Z_to_bv 64 (Z.shiftr (p + 56) 3 + ASHB12)) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                   F (Z_to_bv 64 P_OPENSSL_sk_set_thunks) fc None m1 (seg_rom asegs)
          /\ munch [(lo, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ ACONST m1
          /\ stk asegs m1 lo (bv_unsigned sp + -64)
          /\ rw_cells asegs m1 (bv_unsigned sp + -32) (avf_frame s4 s3 s2 s1 s0 ra)
          /\ rw_cells asegs m1 (bv_unsigned sp + -64) (avfh_frame R_X509_VERIFY_PARAM_free_sk_pop_free_2 p sp)
          /\ rw_cells asegs m1 p (vpm_cells_h h) /\ GOT_x509vpm m1)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_X509_VERIFY_PARAM_free) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros BLK POS PAL BL HR AP ACC0 GG AC0 ST CEIL LO MI.
    unfold P_X509_VERIFY_PARAM_free, P_OPENSSL_sk_set_thunks, P_sk_X509_BUFFER_freefunc_thunk, AVF_R1, ASHB12.
    pose proof (ACONST_shbase m AC0) as [GSB SHB0]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    unfold GOT_x509vpm, A_got_ASN1_OBJECT_free, P_ASN1_OBJECT_free, wz in GG.
    unfold vpm_cells_h, wz in BLK. unfold VPM_SIZE in *.
    acb. pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). unfold FR_sk_pop_free in LO.
    pose proof ACC0 as (_ & AHI & _). unfold AAPP_HI in AHI.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(lo, bv_unsigned sp)])
      by (constructor; [cbn; unfold AHI_LO; lia| constructor]).
    change (id (accessible m p 136)) in ACC0. change (id (ACONST m)) in AC0.
    carve_frame 32%nat ST.
    do 6 step. step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    (* [comment removed for export] *)
    step. step. ubal_by PAL. step. if_lit. step. step. step. zstep. zstep. zstep. reacc ACC0 MU NSW. ck8_check ACC (p + 48). clear ACC.
    (* [comment removed for export] *)
    step. step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACN : ACONST mx) by (unfold id in AC0; eapply ACONST_stack_frame13; [exact AC0| exact MU| exact WM| exact CEIL]) end.
    null_call (ask_pop_free_null_spec) ST CEIL ACN MU WM.
    (* [comment removed for export] *)
    step. step. carve_frame 32%nat ST. do 7 st1. step. ubal_by PAL. step. if_lit.
    step. step. zstep. zstep. zstep. reacc ACC0 MU NSW. ck8_check ACC (p + 56). clear ACC.
    step. step. step. step. step.
    finish. all: try exact FR. all: try exact ACN.
    all: try (unfold avfh_frame, R_X509_VERIFY_PARAM_free_sk_pop_free_2; assumption).
    all: try (unfold id in AC0; eapply ACONST_stack_frame13; [exact AC0| exact MU| exact WM| exact CEIL]).
    all: unfold GOT_x509vpm, A_got_ASN1_OBJECT_free, P_ASN1_OBJECT_free, wz; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma avf_seg3 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv asegs m ->
      evt asegs (fun ms' => exists ra',
          ms' = MS (mkR ra' sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 P_buffer_free) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_OPENSSL_sk_pop_free) fc None m (seg_rom asegs) /\ ra' = Z_to_bv 64 AVF_R2)
        (MS (mkR (Z_to_bv 64 AVF_R1) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AVF_R1)) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros MI. unfold AVF_R1, AVF_R2, R_X509_VERIFY_PARAM_free_helper_sk_pop_free, P_OPENSSL_sk_pop_free, P_buffer_free. retpc.
    step. step. step. step. apply evt_done. eexists. split; reflexivity.
  Qed.

  Lemma avf_segH :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (p off r lo : Z),
      (off = 72 \/ off = 88 \/ off = 104) -> 0 <= r < 2^64 -> r mod 2 = 0 ->
      rw_cells asegs m p (vpm_cells_h 0) -> 0 < p -> p mod 16 = 0 -> p + VPM_SIZE <= lo -> aapp p VPM_SIZE -> accessible m p VPM_SIZE -> ACONST m ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 32 - FR_sk_pop_free -> mem_inv asegs m ->
      evt asegs (fun ms' => exists u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1,
          ms' = MS (mkR (Z_to_bv 64 r) sp gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                   F (ret_pc (Z_to_bv 64 r)) fc None m1 (seg_rom asegs)
          /\ munch [(lo, bv_unsigned sp); (p, p + VPM_SIZE)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ ACONST m1
          /\ stk asegs m1 lo (bv_unsigned sp) /\ rw_cells asegs m1 p (vpm_cells_h 0))
        (MS (mkR (Z_to_bv 64 r) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (p + off)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AVF_H) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros OFFS RR RE BLK POS PAL BL AP ACC0 AC0 ST CEIL LO MI.
    unfold AVF_H, P_OPENSSL_sk_set_thunks, P_OPENSSL_sk_pop_free, P_sk_X509_BUFFER_freefunc_thunk, P_buffer_free.
    pose proof (ACONST_shbase m AC0) as [GSB SHB0]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    unfold vpm_cells_h, wz in BLK. unfold VPM_SIZE in *.
    acb. pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). unfold FR_sk_pop_free in LO.
    pose proof ACC0 as (_ & AHI & _). unfold AAPP_HI in AHI.
    pose proof (munch_refl [(lo, bv_unsigned sp); (p, p + 136)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(lo, bv_unsigned sp); (p, p + 136)]).
    { constructor; [cbn; unfold AHI_LO; lia|]. constructor; [cbn [fst snd]; exact (aapp_not_shadowland _ _ AP)| constructor]. }
    assert (AW : Forall aconst_ok [(lo, bv_unsigned sp); (p, p + 136)]).
    { constructor; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia|].
      constructor; [eapply aconst_ok_aapp; [exact AP| cbn; lia| cbn; lia]| constructor]. }
    change (id (accessible m p 136)) in ACC0. change (id (ACONST m)) in AC0.
    destruct OFFS as [-> |[-> | ->]].
    all: carve_frame 32%nat ST; do 7 st1; step; ubal_by PAL; step; if_lit.
    all: step; step; zstep; zstep; zstep; reacc ACC0 MU NSW.
    1: ck8_check ACC (p + 72). 2: ck8_check ACC (p + 88). 3: ck8_check ACC (p + 104).
    all: clear ACC; step; step; step; step; step.
    all: reAC AC0 MU WM AW; null_call (askset_thunks_null_spec) ST CEIL ACN MU WM.
    all: step; step; step; step; null_call (ask_pop_free_null_spec) ST CEIL ACN MU WM.
    all: reacc ACC0 MU NSW.
    1: ck8_load ACC (p + 72). 2: ck8_load ACC (p + 88). 3: ck8_load ACC (p + 104).
    all: step; if_false_by (ck1_bnez_false 0 eq_refl); clear ACC; st1.
    all: step; step; step; step; step; step.
    all: release_frame FR ST (bv_unsigned sp).
    all: clear ACN; reAC AC0 MU WM AW.
    all: finish. all: try exact ACN.
    all: unfold vpm_cells_h, wz; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma avf_seg4 :
    forall (rax sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (p h lo : Z),
      rw_cells asegs m p (vpm_cells_h h) -> 0 < p -> p mod 16 = 0 -> p + VPM_SIZE <= lo -> 0 <= h < 2^64 -> aapp p VPM_SIZE -> accessible m p VPM_SIZE -> ACONST m ->
      stk asegs m lo (bv_unsigned sp + -64) -> aceil <= lo -> lo <= bv_unsigned sp - 64 - FR_sk_pop_free -> mem_inv asegs m ->
      rw_cells asegs m (bv_unsigned sp + -64) (avfh_frame R_X509_VERIFY_PARAM_free_sk_pop_free_2 p sp) ->
      evt asegs (fun ms' => exists u0 u1 u2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1,
          ms' = MS (mkR (Z_to_bv 64 AVF_R9) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp u0 u1 u2 sp (Z_to_bv 64 p)
                       (Z_to_bv 64 0) (Z_to_bv 64 AVPMF_FILE) (Z_to_bv 64 377) b3 b4 b5 b6 b7
                       (Z_to_bv 64 AVPMF_FILE) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m1 (seg_rom asegs)
          /\ munch [(lo, bv_unsigned sp + -32); (p, p + VPM_SIZE)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ ACONST m1
          /\ stk asegs m1 lo (bv_unsigned sp + -32)
          /\ rw_cells asegs m1 p (vpm_cells_h 0))
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -32)) (Z_to_bv 64 (p + 56)) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 (Z.shiftr (p + 56) 3 + ASHB12)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AVF_R2)) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros BLK POS PAL BL HR AP ACC0 AC0 ST CEIL LO MI FRH.
    unfold AVF_R2, R_X509_VERIFY_PARAM_free_helper_sk_pop_free, AVF_R9, R_X509_VERIFY_PARAM_free_CRYPTO_free, AVPMF_FILE, ASHB12,
      P_CRYPTO_free, P_OPENSSL_sk_set_thunks, P_OPENSSL_sk_pop_free, P_sk_X509_BUFFER_freefunc_thunk, P_buffer_free. retpc.
    unfold avfh_frame, R_X509_VERIFY_PARAM_free_sk_pop_free_2, ASHB12 in FRH.
    unfold vpm_cells_h, wz in BLK |- *. unfold VPM_SIZE in *.
    acb. pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). unfold FR_sk_pop_free in LO.
    pose proof ACC0 as (_ & AHI & _). unfold AAPP_HI in AHI.
    pose proof (munch_refl [(lo, bv_unsigned sp + -32); (p, p + 136)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(lo, bv_unsigned sp + -32); (p, p + 136)]).
    { constructor; [cbn; unfold AHI_LO; lia|]. constructor; [cbn [fst snd]; exact (aapp_not_shadowland _ _ AP)| constructor]. }
    assert (AW : Forall aconst_ok [(lo, bv_unsigned sp + -32); (p, p + 136)]).
    { constructor; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia|].
      constructor; [eapply aconst_ok_aapp; [exact AP| cbn; lia| cbn; lia]| constructor]. }
    change (id (accessible m p 136)) in ACC0. change (id (ACONST m)) in AC0.
    (* [comment removed for export] *)
    reacc ACC0 MU NSW. ck8_load ACC (p + 56). step. if_false_by (ck1_bnez_false 0 eq_refl). clear ACC. st1.
    step. step. step. step. step. step.
    release_frame FRH ST (bv_unsigned sp + -32). try retpc.
    (* [comment removed for export] *)
    Local Ltac h_call o lv ACC0 AC0 MU WM NSW AW ST BLK :=
      reacc ACC0 MU NSW; reAC AC0 MU WM AW;
      eapply evt_cut;
      [ eapply avf_segH with (off := o) (lo := lv); rewrite ?unsigned_lit by lia;
        first [reflexivity| exact ST| exact BLK| assumption
              | lazymatch goal with H : mem_inv _ ?mx |- mem_inv _ ?my => exact H end
              | left; reflexivity| right; left; reflexivity| right; right; reflexivity
              | unfold FR_sk_pop_free; lia| unfold VPM_SIZE; lia| lia
              | match goal with |- ?G => idtac "LEFTH:" G end]
      | ];
      repeat match goal with H : accessible _ _ 136 |- _ => clear H end;
      repeat match goal with H : ACONST _ |- _ => clear H end;
      let ms' := fresh "ms'" in let PO := fresh "PO" in
      intros ms' PO;
      let m' := fresh "m" in let MU' := fresh "MU'" in let WM' := fresh "WM'" in let MI' := fresh "MI" in let AC' := fresh "AC" in
      let ST' := fresh "ST" in let BLK' := fresh "BLK" in
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m' & -> & MU' & WM' & MI' & AC' & ST' & BLK');
      try retpc; rewrite ?unsigned_lit in MU', ST' by lia;
      clear ST BLK; lazymatch goal with H : mem_inv _ ?mx |- _ => lazymatch type of MU' with munch _ mx _ => clear H | _ => idtac end end;
      carry MU' WM'; extend_munch MU WM MU' WM'; rename ST' into ST; rename BLK' into BLK; clear AC';
      unfold vpm_cells_h, wz in BLK.
    step. step. h_call 72 lo ACC0 AC0 MU WM NSW AW ST BLK.
    (* [comment removed for export] *)
    step. step. h_call 88 lo ACC0 AC0 MU WM NSW AW ST BLK.
    (* [comment removed for export] *)
    step. step. h_call 104 lo ACC0 AC0 MU WM NSW AW ST BLK.
    (* [comment removed for export] *)
    zstep. zstep. zstep. reacc ACC0 MU NSW. ck8_check ACC (p + 128). clear ACC.
    step. step. step. step. step. step. step.
    (* [comment removed for export] *)
    reAC AC0 MU WM AW.
    finish. all: try exact ACN.
  Qed.

  (* [comment removed for export] *)
  Lemma avf_seg5 :
    forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (p : Z),
      rw_cells asegs m (bv_unsigned sp + -32) (avf_frame s4 s3 s2 s1 s0 ra) -> mem_inv asegs m ->
      evt asegs (fun ms' => exists u1,
          ms' = MS (mkR ra sp gp tp t0 u1 t2 s0 s1
                       (Z_to_bv 64 p) (Z_to_bv 64 AVPMF_FILE) (Z_to_bv 64 378) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AVF_R9) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 p) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 AVPMF_FILE) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AVF_R9)) fc None m (seg_rom asegs)).
  Proof.
    intros until p. intros FR MI. unfold AVF_R9, R_X509_VERIFY_PARAM_free_CRYPTO_free, AVPMF_FILE, P_CRYPTO_free. unfold avf_frame in FR. retpc.
    pose proof (aword_range sp) as SPR.
    do 10 step. apply evt_done. eexists. reflexivity.
  Qed.
End S.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section XB.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Lemma XBUFobj_LB_mono : forall LB LB' m p X, XBUFobj LB m p X -> (forall b, In b LB -> In b LB') -> XBUFobj LB' m p X.
  Proof. intros LB LB' m p X (HC & HIN & DP & LP & DIN) SUB. split; [exact HC|]. split; [apply SUB; exact HIN|]. split; [exact DP|]. split; [exact LP| apply SUB; exact DIN]. Qed.

  Lemma XBUFs_owned : forall LB m ps bs b,
    Forall2 (fun p X => XBUFobj LB m p X) ps bs -> In b (concat (map (fun px => blocks_XBUF (fst px) (snd px)) (combine ps bs))) -> In b LB.
  Proof.
    intros LB m ps bs b F2. induction F2 as [|p X ps' bs' E F IH]; cbn [concat map combine fst snd]; [intros []|].
    intros Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [| exact (IH Hb)].
    exact (XBUFobj_owned_law LB m p X E b Hb).
  Qed.

  Lemma XBUFs_frame : forall LB LB1 LB' SP m m' ps bs,
    Forall2 (fun p X => XBUFobj LB m p X) ps bs ->
    (forall b, In b (concat (map (fun px => blocks_XBUF (fst px) (snd px)) (combine ps bs))) -> In b LB1) ->
    (forall b, In b LB1 -> In b LB') ->
    xpres H LB1 SP [] m m' ->
    (forall b, In b (concat (map (fun px => blocks_XBUF (fst px) (snd px)) (combine ps bs))) -> blk_addr b + blk_size b <= SP) ->
    Forall2 (fun p X => XBUFobj LB' m' p X) ps bs.
  Proof.
    intros LB LB1 LB' SP m m' ps bs F2. induction F2 as [|p X ps' bs' E F IH]; intros KEEP SUB XP BEL; [constructor|].
    cbn [concat map combine fst snd] in KEEP, BEL.
    constructor.
    - eapply XBUFobj_LB_mono; [| exact SUB]. eapply (XBUFobj_frame_law H); [exact E| | exact XP|].
      + intros b Hb. apply KEEP. apply in_or_app. left. exact Hb.
      + intros b Hb. apply BEL. apply in_or_app. left. exact Hb.
    - apply IH; [| exact SUB| exact XP|]; intros b Hb; [apply KEEP| apply BEL]; apply in_or_app; right; exact Hb.
  Qed.

  Lemma XBUFs_shad_frame : forall LB1 SP m m' ps bs,
    Forall2 (fun p X => XBUF_shad m p X) ps bs ->
    (forall b, In b (concat (map (fun px => blocks_XBUF (fst px) (snd px)) (combine ps bs))) -> In b LB1) ->
    xpres H LB1 SP [] m m' ->
    (forall b, In b (concat (map (fun px => blocks_XBUF (fst px) (snd px)) (combine ps bs))) -> blk_addr b + blk_size b <= SP) ->
    Forall2 (fun p X => XBUF_shad m' p X) ps bs.
  Proof.
    intros LB1 SP m m' ps bs F2. induction F2 as [|p X ps' bs' E F IH]; intros KEEP XP BEL; [constructor|].
    cbn [concat map combine fst snd] in KEEP, BEL.
    constructor.
    - eapply (XBUF_shad_frame_law H); [exact E| | exact XP|].
      + intros b Hb. apply KEEP. apply in_or_app. left. exact Hb.
      + intros b Hb. apply BEL. apply in_or_app. left. exact Hb.
    - apply IH; [| exact XP|]; intros b Hb; [apply KEEP| apply BEL]; apply in_or_app; right; exact Hb.
  Qed.

  Lemma HOSTS_keep : forall LB LB' SP m m' P xs,
    HOSTS LB m P xs -> (forall b, In b (blocks_HOSTS P xs) -> In b LB') -> xpres H LB' SP [] m m' ->
    (forall b, In b (blocks_HOSTS P xs) -> blk_addr b + blk_size b <= SP) -> HOSTS LB' m' P xs.
  Proof.
    intros LB LB' SP m m' P xs XS KEEP XP BEL. revert XS KEEP BEL. unfold HOSTS, blocks_HOSTS.
    destruct xs as [[K bs]|]; intros XS KEEP BEL; [| exact XS].
    destruct XS as (XP0 & SO & LEN & F2). split; [exact XP0|]. split.
    - eapply (SKobj_frame H); [exact SO| intros b Hb; apply KEEP; apply in_or_app; left; exact Hb| exact XP].
    - split; [exact LEN|]. eapply (XBUFs_frame LB LB' LB' SP m m'); [exact F2| intros b Hb; apply KEEP; apply in_or_app; right; exact Hb| auto| exact XP|].
      intros b Hb. apply BEL. apply in_or_app. right. exact Hb.
  Qed.
  Lemma HOSTS_owned : forall LB m P xs b, HOSTS LB m P xs -> In b (blocks_HOSTS P xs) -> In b LB.
  Proof.
    intros LB m P xs b. unfold HOSTS, blocks_HOSTS. destruct xs as [[K bs]|]; intros XS Hb; [| destruct Hb].
    destruct XS as (_ & SO & _ & F2). apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [eapply SKobj_owned; eauto| eapply XBUFs_owned; eauto].
  Qed.
  Lemma HOSTS_shad_keep : forall LB' SP m m' P xs,
    HOSTS_shad m P xs -> (forall b, In b (blocks_HOSTS P xs) -> In b LB') -> xpres H LB' SP [] m m' ->
    (forall b, In b (blocks_HOSTS P xs) -> blk_addr b + blk_size b <= SP) -> HOSTS_shad m' P xs.
  Proof.
    intros LB' SP m m' P xs XSH KEEP XP BEL. revert XSH KEEP BEL. unfold HOSTS_shad, blocks_HOSTS.
    destruct xs as [[K bs]|]; intros XSH KEEP BEL; [| exact I].
    destruct XSH as ((SH & T1 & T2) & F2). split.
    - split; [| split; [exact T1| exact T2]]. destruct SH as [SHH SHD]. split.
      + eapply (addressable_xpres_blk H); [apply KEEP; apply in_or_app; left; left; reflexivity| exact T1| exact SHH| exact XP].
      + intros NC. eapply (addressable_xpres_blk H); [| exact (T2 NC)| exact (SHD NC)| exact XP].
        apply KEEP. apply in_or_app. left. unfold blocks_SK. replace (sk_cap K =? 0) with false by (symmetry; apply Z.eqb_neq; exact NC). right. left. reflexivity.
    - eapply XBUFs_shad_frame; [exact F2| intros b Hb; apply KEEP; apply in_or_app; right; exact Hb| exact XP|].
      intros b Hb. apply BEL. apply in_or_app. right. exact Hb.
  Qed.
End XB.

(* [comment removed for export] *)
Section LAWS.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma VPMobj_owned_law : EP_owned vpmrep VPMobj blocks_VPM.
  Proof.
    unfold EP_owned. intros LB m p x (HC & HIN & HO) b Hb.
    unfold blocks_VPM in Hb. destruct Hb as [<-|Hb]; [exact HIN|]. eapply HOSTS_owned; [exact HO| exact Hb].
  Qed.
  Lemma VPMobj_frame_law : EP_frame H vpmrep VPMobj blocks_VPM.
  Proof.
    unfold EP_frame. intros LB LB' m m' p x SP VO KEEP XP BEL. pose proof VO as (HC & HIN & HO). unfold blocks_VPM in KEEP, BEL.
    unfold VPMobj. split.
    { eapply (xpres_rw_cells' H); [exact XP| exact HC| | constructor].
      right; right; left. exists (vp_id x, p, VPM_SIZE). split; [apply KEEP; left; reflexivity|].
      cbn [blk_addr blk_size fst snd cells_size csize Nat.add vpm_cells]. unfold VPM_SIZE. lia. }
    split; [apply KEEP; left; reflexivity|].
    eapply (HOSTS_keep H); [exact HO| intros b Hb; apply KEEP; right; exact Hb| exact XP| intros b Hb; apply BEL; right; exact Hb].
  Qed.
  Lemma VPM_shad_frame_law : eshad_frame H vpmrep blocks_VPM VPM_shad.
  Proof.
    unfold eshad_frame. intros LB' m m' p x SP (TOP & SH & XSH) KEEP XP BEL. unfold blocks_VPM in KEEP, BEL.
    split; [exact TOP|]. split.
    { eapply (addressable_xpres_blk H); [apply KEEP; left; reflexivity| exact TOP| exact SH| exact XP]. }
    eapply (HOSTS_shad_keep H); [exact XSH| intros b Hb; apply KEEP; right; exact Hb| exact XP| intros b Hb; apply BEL; right; exact Hb].
  Qed.
  Lemma hosts_cost_pos : forall xs, 0 <= hosts_cost H xs.
  Proof.
    intros [[K bs]|]; cbn [hosts_cost]; [| lia].
    pose proof (proj1 (proj2 (proj2 (ah_costs H HH)))) as CF0.
    assert (E0 : 0 <= ecost_sum xbufrep (xbuf_cost H) bs).
    { induction bs as [|e es IH]; cbn [ecost_sum fold_right]; [lia|]. pose proof (xbuf_cost_pos H HH e). unfold ecost_sum in IH. lia. }
    pose proof (CF0 SK_SIZE ltac:(unfold SK_SIZE; lia)). pose proof (CF0 (Z.max (8 * sk_cap K) 0) ltac:(lia)). lia.
  Qed.
  Lemma vpm_cost_pos : ecost_pos vpmrep (vpm_cost H).
  Proof.
    unfold ecost_pos, vpm_cost. intros x. pose proof (hosts_cost_pos (vp_hosts_o x)).
    pose proof (proj1 (proj2 (proj2 (ah_costs H HH))) 0 ltac:(lia)). pose proof (proj1 (proj2 (proj2 (ah_costs H HH))) VPM_SIZE ltac:(unfold VPM_SIZE; lia)). lia.
  Qed.
End LAWS.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma avpmfree_spec : vpmfree_stmt H.
  Proof.
    unfold vpmfree_stmt, efree_stmt_at. intros until CH.
    intros VIS A0 VO VSH ND HP KREL AUX SPB ST CEIL LO ERR MI TP SP16 AC CHN CHS PF HAL IM GM GG RAE. subst a0.
    unfold VPMFREE_STACK, FR_X509_VERIFY_PARAM_free, SKPOPFREE_STACK, XBUFFREE_STACK, FR_buffer_free, FR_sk_pop_free, CFREE_STACK, AFREE_STACK in LO.
    acb. subst tp. rewrite unsigned_lit in ERR by (unfold ATP; lia).
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (CSP0 : aceil <= bv_unsigned sp) by lia. assert (CSP : aceil <= bv_unsigned sp + -64) by lia. assert (CSPV : aceil <= bv_unsigned sp + -32) by lia.
    assert (SUBL : forall q L b, In b (as_lb_remove H q L) -> In b L) by (intros q L b Hb; eapply (proj2 (proj2 (ah_lb_remove H HH))); exact Hb).
    pose proof VO as (VC & VIN & HO). rewrite vpm_cells_h_eq in VC.
    pose proof VSH as (TOP & SH & XSH).
    pose proof (ah_blocks H HH _ _ _ _ HP VIN) as (K1 & K2 & K3 & K4 & K5 & K6 & K7). cbn [blk_addr blk_size fst snd] in K1, K2, K3, K4, K5, K6, K7.
    unfold AIMG_TOP in K4. unfold VPM_SIZE in K3, K5, K7, TOP. unfold AAPP_HI in TOP. clear K6.
    pose proof (aapp_bounds p 136 K7 ltac:(lia)) as (AB1 & AB2 & AB3 & AB4 & AB5). unfold AAPP_HI in AB3.
    pose proof (sh_aapp_range p 136 K7 ltac:(lia)) as (SR1 & SR2 & SR3). unfold AHI_LO in SR3. pose proof aceil_range as ACR.
    assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity.
    assert (HB : forall b, In b LB -> blk_addr b + blk_size b <= aceil).
    { intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP Hb) as (_ & _ & _ & _ & Q5 & _). exact Q5. }
    unfold blocks_VPM in ND.
    set (BX := blocks_HOSTS (vp_hosts x) (vp_hosts_o x)) in *.
    assert (OWN : forall b, In b ((vp_id x, p, VPM_SIZE) :: BX) -> In b LB).
    { intros b Hb. apply (VPMobj_owned_law LB m p x VO). unfold blocks_VPM. exact Hb. }
    assert (BELX : forall b, In b BX -> blk_addr b + blk_size b <= bv_unsigned sp + -64) by (intros b Hb; pose proof (HB b (OWN b (or_intror Hb))); lia).
    assert (RXS : 0 <= vp_hosts x < 2^64).
    { revert HO. unfold HOSTS. destruct (vp_hosts_o x) as [[K bs]|]; intros HO; [| lia].
      destruct HO as (X1 & SKO & _). destruct SKO as (_ & _ & KIN & _). pose proof (ah_blocks H HH _ _ _ _ HP KIN) as (Q1 & _ & Q3 & _ & Q5 & _). cbn [blk_addr blk_size fst snd] in Q1, Q3, Q5. unfold SK_SIZE in *. lia. }
    assert (ACC0 : accessible m p VPM_SIZE) by (unfold VPM_SIZE; eapply addressable_accessible; [exact SH| lia| unfold VPM_SIZE; lia| unfold VPM_SIZE, AAPP_HI; lia]).
    pose proof (proj1 (proj2 (proj2 (ah_costs H HH)))) as CF0.
    pose proof (hosts_cost_pos H HH (vp_hosts_o x)) as CPX. pose proof (CF0 0 ltac:(lia)) as CFZ. pose proof (CF0 136 ltac:(lia)) as CF136.
    unfold vpm_cost, VPM_SIZE in HAL.
    pose proof ND as ND0. cbn [map] in ND0. inversion ND0 as [|i0 l0 NI NDt]; subst i0 l0. clear ND0.
    assert (NOTHD : forall Fr, (forall b, In b Fr -> In b BX) -> ~ In (vp_id x, p, VPM_SIZE) Fr).
    { intros Fr SUB K. apply NI. rewrite in_map_iff. exists (vp_id x, p, VPM_SIZE). split; [reflexivity| apply SUB; exact K]. }
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply avf_seg1 with (lo := lo);
      [exact VC| exact K1| exact K2| unfold VPM_SIZE; lia| exact RXS| exact K7| exact ACC0| exact GG| exact AC| exact ST| exact CEIL| unfold FR_sk_pop_free; lia| exact MI]|].
    intros msF1 mo1 KREL1 MP1 (u0 & u1 & u2 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & VIS1 & MU1 & WM1 & MI1 & AC1 & ST1 & FR1 & FRH1 & VC1 & GG1).
    assert (CW : Forall (aclient_write_ok H LB) [(lo, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (HP1 : as_RHEAP H s LB m1) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW]).
    assert (AUX1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW]).
    assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]) by (eapply errno_across; [exact ERR| exact MU1| exact WM1| unfold ATP; cbn; lia]).
    assert (IM1 : IMPL_mem m1) by (eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]).
    assert (GM1 : GOT_mem m1) by (eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]).
    assert (XP1 : xpres H LB (bv_unsigned sp) [] m m1)
      by (eapply (xpres_of_munch H s LB _ [] _ m m m1); [exact HH| exact HP| exact MU1| exact WM1|]; constructor; [left; cbn; lia| constructor]).
    assert (CH0 : as_chain H m1 (bv_unsigned s0) CH)
      by (eapply (achain_below H HH m m1); [exact CHN| exact CHS| exact MU1|]; constructor; [left; cbn; lia| constructor]).
    assert (CH1 : as_chain H m1 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (ah_chain_cons H HH); [exact CH0| lia| lia| exact SP16| lia| lia|].
      pose proof FR1 as FR2. unfold avf_frame in FR2.
      change ([C8 s2; C8 s1; C8 s0; C8 ra]) with ([C8 s2; C8 s1] ++ [C8 s0; C8 ra]) in FR2.
      apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR2. destruct FR2 as [_ FR2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul Pos.add] in FR2.
      replace (bv_unsigned sp - 16) with (bv_unsigned sp + -32 + 16) by lia.
      first [exact FR2 | revert FR2; rewrite !Z_to_bv_bv_unsigned; intros FR2; exact FR2]. }
    assert (CHH1 : as_chain H m1 (bv_unsigned sp + -32) ((bv_unsigned sp + -32, R_X509_VERIFY_PARAM_free_sk_pop_free_2) :: (bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (ah_chain_cons H HH); [exact CH1| lia| unfold R_X509_VERIFY_PARAM_free_sk_pop_free_2; lia| lia| lia| lia|].
      pose proof FRH1 as FR2. unfold avfh_frame in FR2.
      change ([C8 (Z_to_bv 64 ASHB12); C8 (Z_to_bv 64 p); C8 sp; C8 (Z_to_bv 64 R_X509_VERIFY_PARAM_free_sk_pop_free_2)])
        with ([C8 (Z_to_bv 64 ASHB12); C8 (Z_to_bv 64 p)] ++ [C8 sp; C8 (Z_to_bv 64 R_X509_VERIFY_PARAM_free_sk_pop_free_2)]) in FR2.
      apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR2. destruct FR2 as [_ FR2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul Pos.add] in FR2.
      replace (bv_unsigned sp + -32 - 16) with (bv_unsigned sp + -64 + 16) by lia.
      first [exact FR2 | revert FR2; rewrite !Z_to_bv_bv_unsigned; intros FR2; exact FR2]. }
    assert (CHS1 : forall fp' ra', In (fp', ra') ((bv_unsigned sp, bv_unsigned ra) :: CH) -> bv_unsigned sp + -32 + 16 <= fp')
      by (intros fp' ra' [E|Hin]; [injection E as <- <-; lia| specialize (CHS _ _ Hin); lia]).
    assert (CHS1H : forall fp' ra', In (fp', ra') ((bv_unsigned sp, bv_unsigned ra) :: CH) -> bv_unsigned sp + -64 + 16 <= fp')
      by (intros fp' ra' Hin; specialize (CHS1 _ _ Hin); lia).
    assert (CHSH : forall fp' ra', In (fp', ra') ((bv_unsigned sp + -32, R_X509_VERIFY_PARAM_free_sk_pop_free_2) :: (bv_unsigned sp, bv_unsigned ra) :: CH) -> bv_unsigned sp + -64 + 16 <= fp')
      by (intros fp' ra' [E|Hin]; [injection E as <- <-; lia| specialize (CHS1H _ _ Hin); lia]).
    assert (SP16' : (bv_unsigned sp + -32) mod 16 = 0) by (replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) by lia; rewrite Zminus_mod, SP16; reflexivity).
    assert (SP16H : (bv_unsigned sp + -64) mod 16 = 0) by (replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) by lia; rewrite Zminus_mod, SP16; reflexivity).
    clear CW.
    assert (SHH1 : addressable m1 p 136).
    { unfold VPM_SIZE in SH. eapply addressable_transport; [exact SH| exact MU1| exact WM1|]. cbn. rewrite S0 in SR1.
      destruct K7 as [[P1 P2]|[P1 P2]]; unfold ALOWSH_LO, AHI_LO in *; lia. }
    assert (HO1 : HOSTS LB m1 (vp_hosts x) (vp_hosts_o x)).
    { eapply (HOSTS_keep H); [exact HO| intros b Hb; eapply HOSTS_owned; [exact HO| exact Hb]| exact XP1| intros b Hb; specialize (BELX b Hb); lia]. }
    assert (XSH1 : HOSTS_shad m1 (vp_hosts x) (vp_hosts_o x)).
    { eapply (HOSTS_shad_keep H); [exact XSH| intros b Hb; eapply HOSTS_owned; [exact HO| exact Hb]| exact XP1| intros b Hb; specialize (BELX b Hb); lia]. }

    (* [comment removed for export] *)
    assert (MID : as_SR H (fun c => exists (w0 w1 w2 c0 c1 c2 c3 c4 c5 c6 c7 w3 w4 w5 w6 : word) m6 (st6 : as_St H) LB6,
                 as_VIS H st6 (cfg_ms c) = MS (mkR (Z_to_bv 64 AVF_R2) (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 ATP) w0 w1 w2 (Z_to_bv 64 (bv_unsigned sp + -32)) (Z_to_bv 64 (p + 56))
                                    c0 c1 c2 c3 c4 c5 c6 c7 (Z_to_bv 64 (Z.shiftr (p + 56) 3 + ASHB12)) s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6)
                               F (ret_pc (Z_to_bv 64 AVF_R2)) fc None m6 (seg_rom asegs)
                 /\ as_AKREL H st6 c /\ as_MPRES H mo1 (cfg_model c) /\ mem_inv asegs m6 /\ ACONST m6 /\ stk asegs m6 lo (bv_unsigned sp + -64)
                 /\ rw_cells asegs m6 (ATP + -164) [C4 errv] /\ as_rauxv_ok H m6 B
                 /\ as_RHEAP H st6 LB6 m6 /\ In (vp_id x, p, VPM_SIZE) LB6
                 /\ Permutation (BX ++ LB6) LB /\ (forall b, In b LB6 -> In b LB)
                 /\ xpres H LB6 (bv_unsigned sp + -64) [] m1 m6 /\ IMPL_mem m6 /\ GOT_mem m6 /\ GOT_x509vpm m6
                 /\ rw_cells asegs m6 (bv_unsigned sp + -32) (avf_frame s4 s3 s2 s1 s0 ra)
                 /\ rw_cells asegs m6 (bv_unsigned sp + -64) (avfh_frame R_X509_VERIFY_PARAM_free_sk_pop_free_2 p sp)
                 /\ rw_cells asegs m6 p (vpm_cells_h (vp_hosts x)) /\ addressable m6 p 136
                 /\ as_AL H st6 >= as_AL H s - hosts_cost H (vp_hosts_o x))
             (mkCfg msF1 mo1)).
    { pose proof HO1 as HO'. unfold HOSTS in HO'. pose proof XSH1 as XSH1'. unfold HOSTS_shad in XSH1'.
      pose proof NDt as NDX.
      destruct (vp_hosts_o x) as [[K bs]|] eqn:EXO.
      - (* [comment removed for export] *)
        destruct HO' as (HPOS & SKO & LEN & F2). destruct XSH1' as ((SKSH & T1 & T2) & F2SH).
        set (h := vp_hosts x) in *.
        set (EB := concat (map (fun px : Z * xbufrep => blocks_XBUF (fst px) (snd px)) (combine (sk_elems K) bs))) in *.
        assert (BXE : BX = blocks_SK h K ++ EB) by (unfold BX, blocks_HOSTS; reflexivity).
        rewrite BXE in NDX.
        pose proof SKO as SO0. destruct SO0 as (_ & _ & KIN & KNC & KCAP & _ & _ & KDAT).
        pose proof (ah_blocks H HH _ _ _ _ HP1 KIN) as (KB1 & KB2 & KB3 & KB4 & KB5 & KB6 & KB7). cbn [blk_addr blk_size fst snd] in KB1, KB2, KB3, KB4, KB5, KB6, KB7.
        unfold AIMG_TOP in KB4. unfold SK_SIZE in KB3, KB5, KB7. clear KB6.
        pose proof (sh_aapp_range h 56 KB7 ltac:(lia)) as (HS1 & HS2 & HS3). unfold AHI_LO in HS3.
        assert (PK : blk_id (vp_id x, p, VPM_SIZE) <> blk_id (sk_id K, h, SK_SIZE)).
        { intros E. apply NI. rewrite in_map_iff. exists (sk_id K, h, SK_SIZE). split; [symmetry; exact E|].
          rewrite BXE. apply in_or_app. left. left. reflexivity. }
        pose proof (ah_disj H HH _ _ _ _ _ HP1 VIN KIN PK) as DPK. cbn [blk_addr blk_size fst snd] in DPK. unfold VPM_SIZE, SK_SIZE in DPK.
        assert (DBEL : sk_cap K = 0 \/ (In (sk_did K, sk_data K, 8 * sk_cap K) LB /\ sk_data K + 8 * sk_cap K <= aceil /\ 4 <= sk_cap K)).
        { destruct KDAT as [[C0 _]|(C4 & _ & _ & DIN & _)]; [left; exact C0| right].
          pose proof (ah_blocks H HH _ _ _ _ HP1 DIN) as (_ & _ & _ & _ & Q5 & _). cbn [blk_addr blk_size fst snd] in Q5. split; [exact DIN| split; [exact Q5| exact C4]]. }
        assert (BEL : SK_below h K lo).
        { split; [unfold SK_SIZE; lia|]. destruct DBEL as [C0|(DIN & DB & _)]; [left; exact C0| right; lia]. }
        assert (SKR : SK_ranges H h K).
        { split; [exact (ah_blocks H HH _ _ _ _ HP1 KIN)|]. intros NC. destruct DBEL as [C0|(DIN & _ & _)]; [exfalso; exact (NC C0)|].
          exact (ah_blocks H HH _ _ _ _ HP1 DIN). }
        eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1| eapply (askset_thunks_spec H) with (lo := lo) (LB := LB) (K := K); rewrite ?unsigned_lit by lia;
          [reflexivity| reflexivity| unfold P_sk_X509_BUFFER_freefunc_thunk; lia| exact SKO| exact BEL| exact SKSH| exact SKR| exact AC1| exact ST1| exact CEIL| lia| exact MI1]|].
        intros msF6a mo6a KREL6a MP6a PO. unfold skset_post in PO.
        destruct PO as (y0 & y1 & y2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & y3 & y4 & y5 & y6 & m6a & VIS6a & MU6a & WM6a & MI6a & AC6a & ST6a & SO6a).
        rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in MU6a, ST6a by lia. unfold SK_SIZE in MU6a.
        assert (XPh : xpres H (as_lb_remove H (sk_id K) LB) (bv_unsigned sp + -64) [] m1 m6a).
        { eapply (xpres_of_munch_listed H HH); [exact HP1| exact KIN| exact CSP| exact MU6a| exact WM6a|].
          apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; left; cbn; unfold SK_SIZE; lia| apply Forall_nil]. }
        assert (CW6 : Forall (aclient_write_ok H LB) [(lo, bv_unsigned sp + -64); (h, h + 56)]).
        { apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [| apply Forall_nil].
          right; right; left. exists (sk_id K, h, SK_SIZE). split; [exact KIN| cbn; unfold SK_SIZE; lia]. }
        assert (HP6a : as_RHEAP H s LB m6a) by (eapply (ah_RHEAP_frame H HH); [exact HP1| exact MU6a| exact WM6a| exact CW6]).
        assert (AUX6a : as_rauxv_ok H m6a B) by (eapply (ah_rauxv_frame H HH); [exact AUX1| exact MU6a| exact WM6a| exact CW6]).
        assert (ERR6a : rw_cells asegs m6a (ATP + -164) [C4 errv]) by (eapply errno_across; [exact ERR1| exact MU6a| exact WM6a| unfold ATP; cbn; lia]).
        assert (IM6a : IMPL_mem m6a) by (eapply IMPL_across; [exact MU6a| exact WM6a| unfold A_malloc_impl; cbn; lia| exact IM1]).
        assert (GM6a : GOT_mem m6a) by (eapply GOT_across; [exact MU6a| exact WM6a| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM1]).
        assert (GG6a : GOT_x509vpm m6a) by (eapply GOT_x509vpm_across; [exact MU6a| exact WM6a| unfold A_got_ASN1_OBJECT_free; cbn; lia| exact GG1]).
        assert (FR6a : rw_cells asegs m6a (bv_unsigned sp + -32) (avf_frame s4 s3 s2 s1 s0 ra)) by (eapply rw_cells_transport; [exact FR1| exact MU6a| exact WM6a| cbn; lia]).
        assert (FRH6a : rw_cells asegs m6a (bv_unsigned sp + -64) (avfh_frame R_X509_VERIFY_PARAM_free_sk_pop_free_2 p sp)) by (eapply rw_cells_transport; [exact FRH1| exact MU6a| exact WM6a| cbn; lia]).
        assert (VC6a : rw_cells asegs m6a p (vpm_cells_h h)).
        { eapply rw_cells_transport; [exact VC1| exact MU6a| exact WM6a|]. unfold vpm_cells_h. cbn. lia. }
        assert (SHH6a : addressable m6a p 136).
        { eapply addressable_transport; [exact SHH1| exact MU6a| exact WM6a|]. cbn. rewrite S0 in SR1.
          destruct KB7 as [[P1 P2]|[P1 P2]]; unfold ALOWSH_LO, AHI_LO in *; lia. }
        assert (SKSH6a : SK_shad m6a h K).
        { destruct SKSH as [SKH SKD]. split.
          - eapply addressable_transport; [exact SKH| exact MU6a| exact WM6a|]. unfold SK_SIZE. cbn. rewrite S0 in HS1.
            destruct KB7 as [[P1 P2]|[P1 P2]]; unfold ALOWSH_LO, AHI_LO in *; lia.
          - intros NC. destruct DBEL as [C0|(DIN & DB & C4)]; [exfalso; exact (NC C0)|].
            eapply (addressable_xpres_blk H); [| exact (T2 NC)| exact (SKD NC)| exact XPh].
            apply (proj2 (proj2 (proj2 (alb_remove_exact H HH _ _ _ _ (ah_nodup H HH _ _ _ HP1) KIN)) _)). split; [exact DIN|].
            cbn [blk_id fst snd]. intros E.
            assert (ND2 : List.NoDup (map blk_id (blocks_SK h K))) by (rewrite map_app in NDX; apply NoDup_app_remove_r in NDX; exact NDX).
            unfold blocks_SK in ND2. replace (sk_cap K =? 0) with false in ND2 by (symmetry; apply Z.eqb_neq; exact NC).
            cbn [map blk_id fst snd] in ND2. inversion ND2 as [|i1 l1 NI1 _]; subst. apply NI1. left. exact E. }
        assert (KEB : forall b, In b EB -> In b (as_lb_remove H (sk_id K) LB)).
        { intros b Hb. apply (proj2 (proj2 (proj2 (alb_remove_exact H HH _ _ _ _ (ah_nodup H HH _ _ _ HP1) KIN)) b)).
          split; [apply OWN; right; rewrite BXE; apply in_or_app; right; exact Hb|].
          intros E. eapply (nodup_ids_app_ne (blocks_SK h K) EB); [exact NDX| left; reflexivity| exact Hb| symmetry; exact E]. }
        assert (BELE : forall b, In b EB -> blk_addr b + blk_size b <= bv_unsigned sp + -64) by (intros b Hb; apply BELX; rewrite BXE; apply in_or_app; right; exact Hb).
        assert (F26a : Forall2 (fun q X => XBUFobj LB m6a q X) (sk_elems K) bs).
        { eapply (XBUFs_frame H LB (as_lb_remove H (sk_id K) LB) LB (bv_unsigned sp + -64) m1 m6a); [exact F2| exact KEB| exact (SUBL _ _)| exact XPh| exact BELE]. }
        assert (F2SH6a : Forall2 (fun q X => XBUF_shad m6a q X) (sk_elems K) bs).
        { eapply (XBUFs_shad_frame H (as_lb_remove H (sk_id K) LB) (bv_unsigned sp + -64) m1 m6a); [exact F2SH| exact KEB| exact XPh| exact BELE]. }
        assert (CH6a : as_chain H m6a (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH))
          by (eapply (chain_via_apres H HH); [exact CH1| apply (xpres_nil_apres H); exact XPh| exact CHS1H]).
        assert (CHH6a : as_chain H m6a (bv_unsigned sp + -32) ((bv_unsigned sp + -32, R_X509_VERIFY_PARAM_free_sk_pop_free_2) :: (bv_unsigned sp, bv_unsigned ra) :: CH))
          by (eapply (chain_via_apres H HH); [exact CHH1| apply (xpres_nil_apres H); exact XPh| exact CHSH]).
        (* [comment removed for export] *)
        eapply (ahh_evt_then H HH); [exact KREL6a| exact VIS6a| eapply avf_seg3; [exact MI6a]|].
        intros msF6b mo6b KREL6b MP6b (rax6 & VIS6b & ->).
        (* [comment removed for export] *)
        pose proof (apopfree_hosts_spec H HH) as PFX. unfold popfree_hosts_stmt, skpopfree_stmt_gen in PFX.
        specialize (PFX (axbuffree_spec H HH) (XBUFobj_frame_law H) XBUFobj_owned_law (GOT_x509vpm_frame H) (XBUF_shad_frame_law H) (xbuf_cost_pos H HH)
                        ltac:(unfold P_buffer_free; lia) ltac:(reflexivity)).
        pose proof (CF0 56 ltac:(lia)) as CF56. pose proof (CF0 (8 * sk_cap K) ltac:(lia)) as CFD.
        assert (E0 : 0 <= ecost_sum xbufrep (xbuf_cost H) bs).
        { clear - HH. induction bs as [|e es IH]; cbn [ecost_sum fold_right]; [lia|]. pose proof (xbuf_cost_pos H HH e). unfold ecost_sum in IH. lia. }
        assert (CX : hosts_cost H (Some (K, bs)) = ecost_sum xbufrep (xbuf_cost H) bs + as_Cf H (8 * sk_cap K) + as_Cf H SK_SIZE).
        { cbn [hosts_cost]. rewrite (Z.max_l (8 * sk_cap K) 0) by lia. reflexivity. }
        rewrite CX in CPX |- *. unfold SK_SIZE in CPX, CX |- *.
        eapply (ah_seq H HH).
        { eapply PFX with (a := h) (K := sk_with_thunk K O_SK_FREETH P_sk_X509_BUFFER_freefunc_thunk) (xs := bs) (lo := lo) (B := B) (LB := LB) (s := s) (errv := errv)
                          (CH := (bv_unsigned sp + -32, R_X509_VERIFY_PARAM_free_sk_pop_free_2) :: (bv_unsigned sp, bv_unsigned ra) :: CH);
            rewrite ?e_blocks_SK_with_thunk, ?e_sk_elems_with_thunk, ?e_sk_free_thunk_set, ?e_sk_cap_with_thunk;
            [exact VIS6b| reflexivity| reflexivity| ..]; rewrite ?unsigned_lit by (unfold AVF_R2, R_X509_VERIFY_PARAM_free_helper_sk_pop_free; lia).
          all: first [exact SO6a| exact LEN| exact F26a| exact F2SH6a| exact NDX| exact HP6a| exact KREL6b| exact AUX6a| exact ST6a| exact CEIL| exact ERR6a| exact MI6a
                     | reflexivity| exact SP16H| exact AC6a| exact CHH6a| exact CHSH| exact IM6a| exact GM6a| exact GG6a
                     | unfold SK_shad; rewrite ?e_sk_cap_with_thunk, ?e_sk_data_with_thunk; exact SKSH6a
                     | unfold is_sk_freefunc_thunk; right; right; reflexivity
                     | unfold is_sk_freefunc_thunk; right; left; reflexivity
                     | unfold is_sk_freefunc_thunk; left; reflexivity
                     | unfold SKPOPFREE_STACK, XBUFFREE_STACK, FR_buffer_free, FR_sk_pop_free, CFREE_STACK, AFREE_STACK; lia
                     | unfold AVF_R2; eapply (pf_ok_call _ (pf_shift R_X509_VERIFY_PARAM_free_helper_sk_pop_free (PF_skpopfree PF_xbuffree)));
                       [eapply pf_ok_call; [exact PF|]; unfold PF_vpmfree; intros y Hy; apply in_app_iff; left; exact Hy| intros y Hy; exact Hy]
                     | unfold SK_SIZE; lia | match goal with |- ?G => idtac "LEFTP:" G end]. }
        clear PFX. intros [msF6 mo6] PO. unfold skpopfree_post in PO. cbn [cfg_ms cfg_model] in PO.
        destruct PO as (v0 & v1 & v2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & v3 & v4 & v5 & v6 & m6 & st6 & LB6 &
                        VIS6 & KREL6 & MP6 & MI6 & AC6 & ST6 & ERR6 & AUX6 & PERM6 & HP6 & XP6 & IM6 & GM6 & GG6 & AL6).
        rewrite ?e_blocks_SK_with_thunk, ?e_sk_elems_with_thunk in PERM6. fold EB in PERM6. cbn [sk_cap sk_with_thunk] in AL6.
        rewrite (unsigned_lit (bv_unsigned sp + -64)) in ST6, XP6 by lia.
        pose proof PERM6 as P6. rewrite app_assoc in P6.
        assert (SUB6 : forall b, In b LB6 -> In b LB) by (intros b Hb; eapply Permutation_in; [exact P6| apply in_or_app; right; exact Hb]).
        assert (VIN6 : In (vp_id x, p, VPM_SIZE) LB6).
        { eapply perm_in_rest; [exact P6| exact VIN|]. apply NOTHD. intros b Hb. rewrite BXE. exact Hb. }
        assert (SUBR : forall b, In b LB6 -> In b (as_lb_remove H (sk_id K) LB)).
        { eapply (perm_rest_sub_remove H HH); [exact HP1| exact P6|]. apply in_or_app. left. left. reflexivity. }
        apply (ah_done H HH). cbn [cfg_ms cfg_model].
        exists v0, v1, v2, e0, e1, e2, e3, e4, e5, e6, e7, v3, v4, v5, v6, m6, st6, LB6.
        split; [exact VIS6|]. split; [exact KREL6|]. split; [eapply (ah_mpres_trans H HH); [| exact MP6]; eapply (ah_mpres_trans H HH); [exact MP6a| exact MP6b]|].
        split; [exact MI6|]. split; [exact AC6|]. split; [exact ST6|].
        split; [rewrite unsigned_lit in ERR6 by (unfold ATP; lia); exact ERR6|]. split; [exact AUX6|]. split; [exact HP6|]. split; [exact VIN6|].
        split; [rewrite BXE; first [exact P6| rewrite app_assoc; exact P6| rewrite <- app_assoc; exact P6]|]. split; [exact SUB6|].
        split.
        { eapply xpres_trans; [eapply (xpres_weaken H); [exact XPh| lia| exact SUBR| auto]| exact XP6]. }
        split; [exact IM6|]. split; [exact GM6|]. split; [exact GG6|].
        split; [eapply (xpres_rw_cells' H); [exact XP6| exact FR6a| left; cbn; lia| constructor]|].
        split; [eapply (xpres_rw_cells' H); [exact XP6| exact FRH6a| left; cbn; lia| constructor]|].
        split.
        { eapply (xpres_rw_cells' H); [exact XP6| exact VC6a| | constructor]. right; right; left. exists (vp_id x, p, VPM_SIZE). split; [exact VIN6|].
          unfold vpm_cells_h. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold VPM_SIZE. lia. }
        split; [eapply (addressable_xpres_blk H); [exact VIN6| unfold AAPP_HI; lia| exact SHH6a| exact XP6]|].
        unfold SK_SIZE in AL6. lia.
      - (* [comment removed for export] *)
        assert (BXE : BX = []) by (unfold BX, blocks_HOSTS; reflexivity).
        assert (H0 : vp_hosts x = 0) by exact HO'. rewrite H0 in VIS1.
        eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1| eapply askset_thunks_null_spec with (lo := lo); rewrite ?unsigned_lit by lia;
          [exact ST1| exact CEIL| lia| exact MI1| exact AC1]|].
        intros msF6a mo6a KREL6a MP6a PO. unfold sknull_post in PO.
        destruct PO as (y0 & y1 & y2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & y3 & y4 & y5 & y6 & m6a & VIS6a & MU6a & WM6a & MI6a & AC6a & ST6a).
        rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in MU6a, ST6a by lia.
        eapply (ahh_evt_then H HH); [exact KREL6a| exact VIS6a| eapply avf_seg3; [exact MI6a]|].
        intros msF6b mo6b KREL6b MP6b (rax6 & VIS6b & ->).
        eapply (ahh_evt H HH); [exact KREL6b| exact VIS6b| eapply ask_pop_free_null_spec with (lo := lo); rewrite ?unsigned_lit by lia;
          [exact ST6a| exact CEIL| unfold FR_sk_pop_free; lia| exact MI6a| exact AC6a]|].
        intros msF6 mo6 KREL6 MP6 PO. unfold sknull_post in PO.
        destruct PO as (v0 & v1 & v2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & v3 & v4 & v5 & v6 & m6 & VIS6 & MU6 & WM6 & MI6 & AC6 & ST6).
        rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in MU6, ST6 by lia.
        assert (CW6 : Forall (aclient_write_ok H LB) [(lo, bv_unsigned sp + -64)]) by (constructor; [left; cbn; lia| constructor]).
        assert (XPa : xpres H LB (bv_unsigned sp + -64) [] m1 m6a)
          by (eapply (xpres_of_munch H s LB _ [] _ m1 m1 m6a); [exact HH| exact HP1| exact MU6a| exact WM6a|]; constructor; [left; cbn; lia| constructor]).
        assert (HP6a : as_RHEAP H s LB m6a) by (eapply (ah_RHEAP_frame H HH); [exact HP1| exact MU6a| exact WM6a| exact CW6]).
        assert (XPb : xpres H LB (bv_unsigned sp + -64) [] m6a m6)
          by (eapply (xpres_of_munch H s LB _ [] _ m6a m6a m6); [exact HH| exact HP6a| exact MU6| exact WM6|]; constructor; [left; cbn; lia| constructor]).
        assert (XPab : xpres H LB (bv_unsigned sp + -64) [] m1 m6) by (eapply xpres_trans; [exact XPa| exact XPb]).
        cbn [cfg_ms cfg_model].
        exists v0, v1, v2, (Z_to_bv 64 0), e1, e2, e3, e4, e5, e6, e7, v3, v4, v5, v6, m6, s, LB.
        split; [exact VIS6|]. split; [exact KREL6|].
        split; [eapply (ah_mpres_trans H HH); [| exact MP6]; eapply (ah_mpres_trans H HH); [exact MP6a| exact MP6b]|].
        split; [exact MI6|]. split; [exact AC6|]. split; [exact ST6|].
        split; [eapply rw_cells_transport; [| exact MU6| exact WM6| unfold ATP; cbn; lia]; eapply rw_cells_transport; [exact ERR1| exact MU6a| exact WM6a| unfold ATP; cbn; lia]|].
        split. { eapply (ah_rauxv_frame H HH); [| exact MU6| exact WM6| exact CW6]. eapply (ah_rauxv_frame H HH); [exact AUX1| exact MU6a| exact WM6a| exact CW6]. }
        split. { eapply (ah_RHEAP_frame H HH); [exact HP6a| exact MU6| exact WM6| exact CW6]. }
        split; [exact VIN|]. rewrite BXE. cbn [app]. split; [apply Permutation_refl|]. split; [auto|].
        split; [exact XPab|].
        split; [eapply IMPL_across; [exact MU6| exact WM6| unfold A_malloc_impl; cbn; lia|]; eapply IMPL_across; [exact MU6a| exact WM6a| unfold A_malloc_impl; cbn; lia| exact IM1]|].
        split; [eapply GOT_across; [exact MU6| exact WM6| unfold A_got_CRYPTO_malloc; cbn; lia|]; eapply GOT_across; [exact MU6a| exact WM6a| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM1]|].
        split; [eapply GOT_x509vpm_across; [exact MU6| exact WM6| unfold A_got_ASN1_OBJECT_free; cbn; lia|]; eapply GOT_x509vpm_across; [exact MU6a| exact WM6a| unfold A_got_ASN1_OBJECT_free; cbn; lia| exact GG1]|].
        split; [eapply rw_cells_transport; [| exact MU6| exact WM6| cbn; lia]; eapply rw_cells_transport; [exact FR1| exact MU6a| exact WM6a| cbn; lia]|].
        split; [eapply rw_cells_transport; [| exact MU6| exact WM6| cbn; lia]; eapply rw_cells_transport; [exact FRH1| exact MU6a| exact WM6a| cbn; lia]|].
        split. { rewrite H0 in VC1 |- *. eapply rw_cells_transport; [| exact MU6| exact WM6| unfold vpm_cells_h; cbn; lia]. eapply rw_cells_transport; [exact VC1| exact MU6a| exact WM6a| unfold vpm_cells_h; cbn; lia]. }
        split. { eapply addressable_transport; [| exact MU6| exact WM6| cbn; rewrite S0 in SR1; destruct K7 as [[P1 P2]|[P1 P2]]; unfold ALOWSH_LO, AHI_LO in *; lia].
                 eapply addressable_transport; [exact SHH1| exact MU6a| exact WM6a| cbn; rewrite S0 in SR1; destruct K7 as [[P1 P2]|[P1 P2]]; unfold ALOWSH_LO, AHI_LO in *; lia]. }
        cbn [hosts_cost]. lia. }

    (* [comment removed for export] *)
    eapply (ah_seq H HH); [exact MID|]. clear MID.
    intros [msF6 mo6] PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (k0 & k1 & k2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & k3 & k4 & k5 & k6 & m6 & st6 & LB6 &
                    VIS6 & KREL6 & MP6 & MI6 & AC6 & ST6 & ERR6 & AUX6 & HP6 & VIN6 & PERMX & SUB6 & XPM1 & IM6 & GM6 & GG6 & FR6 & FRH6 & VC6 & SHH6 & AL6).
    assert (MPA6 := ah_mpres_trans H HH _ _ _ MP1 MP6). clear MP1 MP6.
    assert (ACC6 : accessible m6 p VPM_SIZE) by (unfold VPM_SIZE; eapply addressable_accessible; [exact SHH6| lia| lia| unfold AAPP_HI; lia]).
    assert (CH6 : as_chain H m6 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH))
      by (eapply (chain_via_apres H HH); [exact CH1| apply (xpres_nil_apres H); exact XPM1| exact CHS1H]).
    assert (XPM : xpres H LB6 (bv_unsigned sp) [] m m6).
    { eapply xpres_trans; [eapply (xpres_weaken H); [exact XP1| lia| exact SUB6| auto]| eapply (xpres_weaken H); [exact XPM1| lia| auto| auto]]. }
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL6| exact VIS6| eapply avf_seg4 with (lo := lo);
      [exact VC6| exact K1| exact K2| unfold VPM_SIZE; lia| exact RXS| exact K7| exact ACC6| exact AC6| exact ST6| exact CEIL| unfold FR_sk_pop_free; lia| exact MI6| exact FRH6]|].
    intros msF7 mo7 KREL7 MP7 (z0 & z1 & z2 & d3 & d4 & d5 & d6 & d7 & z3 & z4 & z5 & z6 & m7 & VIS7 & MU7 & WM7 & MI7 & AC7 & ST7 & VC7).
    unfold VPM_SIZE in MU7.
    assert (MPA7 := ah_mpres_trans H HH _ _ _ MPA6 MP7). clear MPA6 MP7.
    assert (CW7 : Forall (aclient_write_ok H LB6) [(lo, bv_unsigned sp + -32); (p, p + 136)]).
    { apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [| apply Forall_nil].
      right; right; left. exists (vp_id x, p, VPM_SIZE). split; [exact VIN6| cbn; unfold VPM_SIZE; lia]. }
    assert (HP7 : as_RHEAP H st6 LB6 m7) by (eapply (ah_RHEAP_frame H HH); [exact HP6| exact MU7| exact WM7| exact CW7]).
    assert (AUX7 : as_rauxv_ok H m7 B) by (eapply (ah_rauxv_frame H HH); [exact AUX6| exact MU7| exact WM7| exact CW7]).
    assert (ERR7 : rw_cells asegs m7 (ATP + -164) [C4 errv]) by (eapply errno_across; [exact ERR6| exact MU7| exact WM7| unfold ATP; cbn; lia]).
    assert (IM7 : IMPL_mem m7) by (eapply IMPL_across; [exact MU7| exact WM7| unfold A_malloc_impl; cbn; lia| exact IM6]).
    assert (GM7 : GOT_mem m7) by (eapply GOT_across; [exact MU7| exact WM7| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM6]).
    assert (GG7 : GOT_x509vpm m7) by (eapply GOT_x509vpm_across; [exact MU7| exact WM7| unfold A_got_ASN1_OBJECT_free; cbn; lia| exact GG6]).
    assert (FR7 : rw_cells asegs m7 (bv_unsigned sp + -32) (avf_frame s4 s3 s2 s1 s0 ra)) by (eapply rw_cells_transport; [exact FR6| exact MU7| exact WM7| unfold avf_frame; cbn; lia]).
    assert (XP7 : xpres H (as_lb_remove H (vp_id x) LB6) (bv_unsigned sp + -32) [] m6 m7).
    { eapply (xpres_of_munch_listed H HH); [exact HP6| exact VIN6| exact CSPV| exact MU7| exact WM7|].
      apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; left; cbn; unfold VPM_SIZE; lia| apply Forall_nil]. }
    assert (SHH7 : addressable m7 p 136).
    { eapply addressable_transport; [exact SHH6| exact MU7| exact WM7|]. cbn. rewrite S0 in SR1.
      destruct K7 as [[P1 P2]|[P1 P2]]; unfold ALOWSH_LO, AHI_LO in *; lia. }
    assert (CH7 : as_chain H m7 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH))
      by (eapply (chain_via_apres H HH); [exact CH6| apply (xpres_nil_apres H); exact XP7| exact CHS1]).
    (* [comment removed for export] *)
    eapply (ah_seq H HH).
    { eapply (acfree_null_spec H HH) with (lo := lo) (B := B) (LB := LB6) (s := st6) (errv := errv) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
        [exact VIS7| ..]; rewrite ?unsigned_lit by (unfold AVF_R9, R_X509_VERIFY_PARAM_free_CRYPTO_free; lia).
      all: first [exact HP7| exact KREL7| exact AUX7| exact ST7| exact CEIL| exact ERR7| exact MI7| reflexivity| exact SP16'| exact AC7| exact CH7| exact CHS1
                 | exact IM7| exact GM7| unfold CFREE_STACK, AFREE_STACK; lia | lia | match goal with |- ?G => idtac "LEFTN:" G end]. }
    intros [msF7b mo7b] PO. unfold cfree_null_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0' & u1' & u2' & b0 & b1 & b2' & b3' & b4' & b5' & b6' & b7' & u3' & u4' & u5' & u6' & m8 & st8 &
                    VIS8 & KREL8 & MP8 & MI8 & AC8 & ST8 & ERR8 & AUX8 & XP8 & HEAP8 & IM8 & GM8 & AL8).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST8, XP8 by lia.
    assert (MPA8 := ah_mpres_trans H HH _ _ _ MPA7 MP8). clear MPA7 MP8.
    assert (FR8 : rw_cells asegs m8 (bv_unsigned sp + -32) (avf_frame s4 s3 s2 s1 s0 ra)) by (eapply (xpres_rw_cells' H); [exact XP8| exact FR7| left; cbn; lia| constructor]).
    assert (VC8 : rw_cells asegs m8 p (vpm_cells_h 0)).
    { eapply (xpres_rw_cells' H); [exact XP8| exact VC7| | constructor]. right; right; left. exists (vp_id x, p, VPM_SIZE). split; [exact VIN6|].
      unfold vpm_cells_h. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold VPM_SIZE. lia. }
    assert (SHH8 : addressable m8 p 136) by (eapply (addressable_xpres_blk H); [exact VIN6| unfold AAPP_HI; lia| exact SHH7| exact XP8]).
    assert (GG8 : GOT_x509vpm m8) by (eapply (GOT_x509vpm_xpres H); [exact XP8| exact CSPV| constructor| exact GG7]).
    assert (XPM8 : xpres H (as_lb_remove H (vp_id x) LB6) (bv_unsigned sp + -32) [] m1 m8).
    { eapply xpres_trans; [eapply (xpres_weaken H); [exact XPM1| lia| exact (SUBL _ _)| auto]|].
      eapply xpres_trans; [exact XP7| eapply (xpres_weaken H); [exact XP8| lia| exact (SUBL _ _)| auto]]. }
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL8| exact VIS8| eapply avf_seg5; [exact FR8| exact MI8]|].
    intros msF9 mo9 KREL9 MP9 (u1x & VIS9).
    assert (MPA9 := ah_mpres_trans H HH _ _ _ MPA8 MP9). clear MPA8 MP9.
    unfold avf_frame in FR8. release_frame FR8 ST8 (bv_unsigned sp). rename ST8 into ST9.
    pose proof (rw_cells_flatten _ _ _ _ VC8) as VCB. unfold vpm_cells_h in VCB. cbn [cells_size csize Nat.add] in VCB.
    assert (CH9 : as_chain H m8 (bv_unsigned s0) CH).
    { eapply (chain_via_apres H HH); [exact CH0| apply (xpres_nil_apres H); exact XPM8| intros fp' ra' Hin; specialize (CHS _ _ Hin); lia]. }
    (* [comment removed for export] *)
    pose proof (acfree_spec H HH) as CF. unfold cfree_stmt in CF.
    eapply (ah_mono H HH).
    { eapply CF with (lo := lo) (B := B) (LB := LB6) (s := st8) (p := vp_id x) (n := VPM_SIZE) (errv := errv) (CH := CH);
        [exact VIS9| reflexivity| ..]; rewrite ?unsigned_lit by (unfold ATP; lia).
      all: first [exact HEAP8| exact KREL9| exact VIN6| exact AUX8| exact SPB| exact ST9| exact CEIL| exact ERR8| exact MI8| reflexivity| exact SP16| exact AC8| exact CH9| exact CHS
                 | unfold VPM_SIZE; exact VCB| unfold VPM_SIZE; exact SHH8| exact IM8| exact GM8| exact RAE| unfold CFREE_STACK, AFREE_STACK; lia
                 | eapply pf_ok_incl; [exact PF|]; unfold PF_vpmfree; intros y Hy; do 2 (apply in_app_iff; right); exact Hy
                 | unfold VPM_SIZE; lia | match goal with |- ?G => idtac "LEFTT:" G end]. }
    intros [msF10 mo10] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (q0 & q1 & q2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & q3 & q4 & q5 & q6 & m10 & st10 &
                    VIS10 & KREL10 & MP10 & MI10 & AC10 & ST10 & ERR10 & AUX10 & XP10 & HEAP10 & IM10 & GM10 & AL10).
    unfold efree_post. cbn [cfg_ms cfg_model].
    exists q0, q1, q2, e0, e1, e2, e3, e4, e5, e6, e7, q3, q4, q5, q6, m10, st10, (as_lb_remove H (vp_id x) LB6).
    split; [exact VIS10|]. split; [exact KREL10|]. split; [eapply (ah_mpres_trans H HH); [exact MPA9| exact MP10]|].
    split; [exact MI10|]. split; [exact AC10|]. split; [exact ST10|].
    split; [rewrite unsigned_lit by (unfold ATP; lia); rewrite unsigned_lit in ERR10 by (unfold ATP; lia); exact ERR10|]. split; [exact AUX10|].
    split.
    { unfold blocks_VPM. fold BX. cbn [app]. eapply Permutation_trans; [| exact PERMX].
      eapply Permutation_trans; [apply Permutation_middle|]. apply Permutation_app_head.
      eapply (alb_remove_perm H HH); [exact HEAP8| exact VIN6]. }
    split; [exact HEAP10|].
    split. { eapply xpres_trans; [eapply (xpres_weaken H); [exact XP1| lia| intros b Hb; apply SUB6; eapply SUBL; exact Hb| auto]|].
             eapply xpres_trans; [eapply (xpres_weaken H); [exact XPM8| lia| auto| auto]| exact XP10]. }
    split; [exact IM10|]. split; [exact GM10|].
    split; [eapply (GOT_x509vpm_xpres H); [exact XP10| exact CSP0| constructor| exact GG8]|].
    unfold vpm_cost, VPM_SIZE. unfold VPM_SIZE in AL10. lia.
  Qed.
End W.
