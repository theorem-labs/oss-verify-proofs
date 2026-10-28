(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX AsStack0 ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C2 ECH_AStmt_C4 ECH_AStmt_C11 ECH_AKit ECH_AsKit ECH_ARostr ECH_AC11_find.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition A_str_hpke_util_c : Z := 0xad2e0.
Definition A_str_kem_find : Z := 0xad340.
Definition A_str_kdf_find : Z := 0xad380.
Definition A_str_aead_find : Z := 0xad3c0.
Definition S_hpke_util_c : list byte := Eval vm_compute in img_cstr A_str_hpke_util_c 64.
Definition K_hpke_util_c : list byte := Eval vm_compute in img_slack A_str_hpke_util_c (length S_hpke_util_c).
Definition S_kem_find : list byte := Eval vm_compute in img_cstr A_str_kem_find 64.
Definition K_kem_find : list byte := Eval vm_compute in img_slack A_str_kem_find (length S_kem_find).
Definition S_kdf_find : list byte := Eval vm_compute in img_cstr A_str_kdf_find 64.
Definition K_kdf_find : list byte := Eval vm_compute in img_slack A_str_kdf_find (length S_kdf_find).
Definition S_aead_find : list byte := Eval vm_compute in img_cstr A_str_aead_find 64.
Definition K_aead_find : list byte := Eval vm_compute in img_slack A_str_aead_find (length S_aead_find).

(* [comment removed for export] *)
Definition KDF_RA1 : Z := 0x3e5c64.  Definition KDF_RA2 : Z := 0x3e5c80.  Definition KDF_RA3 : Z := 0x3e5c94.
Definition AEAD_RA1 : Z := 0x3e5d28. Definition AEAD_RA2 : Z := 0x3e5d44. Definition AEAD_RA3 : Z := 0x3e5d58.
Definition KEM_RA1 : Z := 0x3e5b9c.  Definition KEM_RA2 : Z := 0x3e5bb8.  Definition KEM_RA3 : Z := 0x3e5bcc.

Section S.
  Context {HCEIL : HeapCeil}.
  Lemma R_hpke_util_c : AROSTR A_str_hpke_util_c S_hpke_util_c K_hpke_util_c.
  Proof. eapply AROSTR_intro; [apply ROSTR_of_image; vm_compute; reflexivity| unfold aglobals; cbn; tauto| vm_compute; intros X; discriminate X| vm_compute; intros X; discriminate X]. Qed.
  Lemma R_kem_find : AROSTR A_str_kem_find S_kem_find K_kem_find.
  Proof. eapply AROSTR_intro; [apply ROSTR_of_image; vm_compute; reflexivity| unfold aglobals; cbn; tauto| vm_compute; intros X; discriminate X| vm_compute; intros X; discriminate X]. Qed.
  Lemma R_kdf_find : AROSTR A_str_kdf_find S_kdf_find K_kdf_find.
  Proof. eapply AROSTR_intro; [apply ROSTR_of_image; vm_compute; reflexivity| unfold aglobals; cbn; tauto| vm_compute; intros X; discriminate X| vm_compute; intros X; discriminate X]. Qed.
  Lemma R_aead_find : AROSTR A_str_aead_find S_aead_find K_aead_find.
  Proof. eapply AROSTR_intro; [apply ROSTR_of_image; vm_compute; reflexivity| unfold aglobals; cbn; tauto| vm_compute; intros X; discriminate X| vm_compute; intros X; discriminate X]. Qed.

  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit by lia; lia.
  (* [comment removed for export] *)
  Local Ltac finish_jk := apply evt_done; hnf; repeat (lazymatch goal with |- ex _ => eexists end);
    lazymatch goal with
    | |- list byte => exact []
    | |- _ = _ /\ _ => split; [reflexivity|]; repeat match goal with |- _ /\ _ => split end; try assumption;
                        try (lazymatch goal with |- rw_cells _ _ _ _ => eassumption end)
    end.
  Local Ltac br_not := step; try (let K0 := fresh "K0" in if_cases K0; zify_cond K0; [kill K0|]; clear K0).
  Local Ltac fix_rows R1 R2 R3 R4 :=
    try match type of R1 with rw_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in R1 end;
    try match type of R2 with rw_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in R2 end;
    try match type of R3 with rw_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in R3 end;
    try match type of R4 with rw_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in R4 end.

  (* [comment removed for export] *)
  Definition segA_stmt (f : finder) (FRZ ra1 : Z) (frc : list byte -> word -> word -> word -> list cell) (S1 : Z -> word -> word -> Prop) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (id lo : Z),
      0 <= id < 2^16 -> find_id (f_ids f) id = None -> HPKE_tabs m -> ACONST m ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - FRZ -> mem_inv asegs m ->
      evt asegs (fun ms' => exists t0' t1' t2' s1i a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' jk,
                   ms' = MS (mkR (Z_to_bv 64 ra1) (Z_to_bv 64 (bv_unsigned sp + - FRZ)) gp tp t0' t1' t2' sp s1i a0' a1' a2' a3' a4' a5' a6' a7'
                                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 P_ERR_new) fc None m' (seg_rom asegs)
                   /\ S1 id s1 s1i
                   /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + - FRZ)
                   /\ rw_cells asegs m' (bv_unsigned sp + - FRZ) (frc jk ra s0 s1) /\ HPKE_tabs m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 id) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (f_entry f)) fc None m (seg_rom asegs)).
  Definition glue_stmt (S1 : word -> Prop) (raA raB target a0v a1v a2v : Z) : Prop :=
    forall (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (m1 : mem), S1 s1 -> mem_inv asegs m1 ->
      evt asegs (fun ms' => exists v0 v1 v2 c3 c4 c5 c6 c7 v3 v4 v5 v6,
                   ms' = MS (mkR (Z_to_bv 64 raB) sp gp tp v0 v1 v2 s0 s1 (Z_to_bv 64 a0v) (Z_to_bv 64 a1v) (Z_to_bv 64 a2v) c3 c4 c5 c6 c7
                                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6) F (Z_to_bv 64 target) fc None m1 (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 raA) sp gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
            F (ret_pc (Z_to_bv 64 raA)) fc None m1 (seg_rom asegs)).
  Definition segC_stmt (FRZ ra3 : Z) (frc : list byte -> word -> word -> word -> list cell) (S1 : word -> word -> Prop) : Prop :=
    forall (ra sp gp tp s0 s1 s0i s1i s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (m' : mem) (lo : Z) (jk : list byte),
      S1 s1 s1i ->
      rw_cells asegs m' (bv_unsigned sp + - FRZ) (frc jk ra s0 s1) -> stk asegs m' lo (bv_unsigned sp + - FRZ) -> mem_inv asegs m' ->
      aceil <= lo -> lo <= bv_unsigned sp - FRZ ->
      evt asegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
                   ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                            F (ret_pc ra) fc None m' (seg_rom asegs) /\ stk asegs m' lo (bv_unsigned sp))
        (MS (mkR (Z_to_bv 64 ra3) (Z_to_bv 64 (bv_unsigned sp + - FRZ)) gp tp u0 u1 u2 s0i s1i b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
            F (ret_pc (Z_to_bv 64 ra3)) fc None m' (seg_rom asegs)).

  (* [comment removed for export] *)
  Lemma kdf_segA : segA_stmt KDF_finder 16 KDF_RA1 (fun _ ra s0 _ => [C8 s0; C8 ra]) (fun _ s1 s1i => s1i = s1).
  Proof.
    unfold segA_stmt. cbn [f_ids f_entry KDF_finder]. change (Z.opp 16) with (-16).
    intros until lo. intros IDR FI TB AC ST CEIL LO MI.
    unfold P_ossl_HPKE_KDF_INFO_find_id, KDF_RA1, P_ERR_new in *. acb.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (ACONST_shbase m AC) as [GSB SHB]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB. rewrite ASHADOW_BASE_val in SHB.
    pose proof TB as TB0. unfold HPKE_tabs in TB. destruct TB as (_ & TD & _).
    unfold A_hpke_kdf_tab, HPKE_KDF_ROW, HPKE_KDF_IDS in TD. cbn [id_rows] in TD.
    destruct TD as (R0 & R1 & R2 & _). unfold wz in R0, R1, R2. fix_rows R1 R2 R2 R2.
    assert (NE : id <> 1 /\ id <> 2 /\ id <> 3).
    { cbn [find_id HPKE_KDF_IDS] in FI. repeat split; intros ->; cbn in FI; discriminate FI. }
    destruct NE as (N1 & N2 & N3).
    carve_frame 16%nat ST.
    do 4 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACC : accessible mx 0x5ad9a0 72) by (apply kdf_tab_acc; eapply ACONST_stack_frame; [exact AC| exact MU| exact WM| exact CEIL]) end.
    step. step. step. step. zstep. zstep. zstep. step. step.
    ck8_check_lit ACC 0x5ad9a0. st1. br_not. zstep. zstep. zstep. zstep. br_not. step.
    ck8_check_lit ACC (0x5ad9a0 + 24). st1. br_not. zstep. zstep. zstep. zstep. br_not. step.
    ck8_check_lit ACC (0x5ad9a0 + 48). st1. br_not. zstep. zstep. zstep. zstep. step. try if_true. try if_lit.
    step. step.
    finish_jk; [reflexivity|].
    eapply HPKE_tabs_transport; [exact MU | exact WM | | exact TB0]. unfold HPKE_TAB_LO, HPKE_TAB_HI, A_hpke_kem_tab, A_hpke_aead_tab; cbn; lia.
  Qed.

  Lemma kdf_glue1 : forall id s1o, glue_stmt (fun s1 => s1 = s1o) KDF_RA1 KDF_RA2 P_ERR_set_debug A_str_hpke_util_c (f_line KDF_finder id) A_str_kdf_find.
  Proof.
    unfold glue_stmt. intros until m1. intros _ MI. unfold KDF_RA1, KDF_RA2, P_ERR_set_debug, A_str_hpke_util_c, A_str_kdf_find. cbn [f_line KDF_finder].
    replace (ret_pc (Z_to_bv 64 0x3e5c64)) with (Z_to_bv 64 0x3e5c64) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    do 7 step. finish.
  Qed.
  Lemma kdf_glue2 : glue_stmt (fun _ => True) KDF_RA2 KDF_RA3 P_ERR_set_error ERR_LIB_PROV (f_reason KDF_finder) 0.
  Proof.
    unfold glue_stmt. intros until m1. intros _ MI. unfold KDF_RA2, KDF_RA3, P_ERR_set_error, ERR_LIB_PROV, PROV_R_INVALID_KDF. cbn [f_reason KDF_finder]. unfold PROV_R_INVALID_KDF.
    replace (ret_pc (Z_to_bv 64 0x3e5c80)) with (Z_to_bv 64 0x3e5c80) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    do 5 step. finish.
  Qed.
  Lemma kdf_segC : segC_stmt 16 KDF_RA3 (fun _ ra s0 _ => [C8 s0; C8 ra]) (fun s1 s1i => s1i = s1).
  Proof.
    unfold segC_stmt. intros until lo. intros jk -> FR ST MI CEIL LO. unfold KDF_RA3. acb.
    change (Z.opp 16) with (-16) in *.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    replace (ret_pc (Z_to_bv 64 0x3e5c94)) with (Z_to_bv 64 0x3e5c94) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. step. step. step. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.

  (* [comment removed for export] *)
  Lemma aead_segA : segA_stmt AEAD_finder 16 AEAD_RA1 (fun _ ra s0 _ => [C8 s0; C8 ra]) (fun _ s1 s1i => s1i = s1).
  Proof.
    unfold segA_stmt. cbn [f_ids f_entry AEAD_finder]. change (Z.opp 16) with (-16).
    intros until lo. intros IDR FI TB AC ST CEIL LO MI.
    unfold P_ossl_HPKE_AEAD_INFO_find_id, AEAD_RA1, P_ERR_new in *. acb.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (ACONST_shbase m AC) as [GSB SHB]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB. rewrite ASHADOW_BASE_val in SHB.
    pose proof TB as TB0. unfold HPKE_tabs in TB. destruct TB as (_ & _ & TA).
    unfold A_hpke_aead_tab, HPKE_AEAD_ROW, HPKE_AEAD_IDS in TA. cbn [id_rows] in TA.
    destruct TA as (R0 & R1 & R2 & R3 & _). unfold wz in R0, R1, R2, R3. fix_rows R1 R2 R3 R3.
    assert (NE : id <> 1 /\ id <> 2 /\ id <> 3 /\ id <> 65535).
    { cbn [find_id HPKE_AEAD_IDS] in FI. repeat split; intros ->; cbn in FI; discriminate FI. }
    destruct NE as (N1 & N2 & N3 & N4).
    carve_frame 16%nat ST.
    do 4 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACC : accessible mx 0x5ada20 160) by (apply aead_tab_acc; eapply ACONST_stack_frame; [exact AC| exact MU| exact WM| exact CEIL]) end.
    step. step. step. step. zstep. zstep. zstep. step. step.
    ck8_check_lit ACC 0x5ada20. st1. br_not. zstep. zstep. zstep. zstep. br_not. step.
    ck8_check_lit ACC (0x5ada20 + 40). st1. br_not. zstep. zstep. zstep. zstep. br_not. step.
    ck8_check_lit ACC (0x5ada20 + 80). st1. br_not. zstep. zstep. zstep. zstep. br_not. step.
    ck8_check_lit ACC (0x5ada20 + 120). st1. br_not. zstep. zstep. zstep. zstep. step. try if_true. try if_lit.
    step. step.
    finish_jk; [reflexivity|].
    eapply HPKE_tabs_transport; [exact MU | exact WM | | exact TB0]. unfold HPKE_TAB_LO, HPKE_TAB_HI, A_hpke_kem_tab, A_hpke_aead_tab; cbn; lia.
  Qed.
  Lemma aead_glue1 : forall id s1o, glue_stmt (fun s1 => s1 = s1o) AEAD_RA1 AEAD_RA2 P_ERR_set_debug A_str_hpke_util_c (f_line AEAD_finder id) A_str_aead_find.
  Proof.
    unfold glue_stmt. intros until m1. intros _ MI. unfold AEAD_RA1, AEAD_RA2, P_ERR_set_debug, A_str_hpke_util_c, A_str_aead_find. cbn [f_line AEAD_finder].
    replace (ret_pc (Z_to_bv 64 0x3e5d28)) with (Z_to_bv 64 0x3e5d28) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    do 7 step. finish.
  Qed.
  Lemma aead_glue2 : glue_stmt (fun _ => True) AEAD_RA2 AEAD_RA3 P_ERR_set_error ERR_LIB_PROV (f_reason AEAD_finder) 0.
  Proof.
    unfold glue_stmt. intros until m1. intros _ MI. unfold AEAD_RA2, AEAD_RA3, P_ERR_set_error, ERR_LIB_PROV. cbn [f_reason AEAD_finder]. unfold PROV_R_INVALID_AEAD.
    replace (ret_pc (Z_to_bv 64 0x3e5d44)) with (Z_to_bv 64 0x3e5d44) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    do 5 step. finish.
  Qed.
  Lemma aead_segC : segC_stmt 16 AEAD_RA3 (fun _ ra s0 _ => [C8 s0; C8 ra]) (fun s1 s1i => s1i = s1).
  Proof.
    unfold segC_stmt. intros until lo. intros jk -> FR ST MI CEIL LO. unfold AEAD_RA3. acb.
    change (Z.opp 16) with (-16) in *.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    replace (ret_pc (Z_to_bv 64 0x3e5d58)) with (Z_to_bv 64 0x3e5d58) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. step. step. step. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.

  (* [comment removed for export] *)
  Lemma kem_segA : segA_stmt KEM_finder 32 KEM_RA1 (fun jk ra s0 s1 => [CB 8 jk; C8 s1; C8 s0; C8 ra]) (fun id _ s1i => s1i = Z_to_bv 64 (f_line KEM_finder id)).
  Proof.
    unfold segA_stmt. cbn [f_ids f_entry f_line KEM_finder]. change (Z.opp 32) with (-32).
    intros until lo. intros IDR FI TB AC ST CEIL LO MI.
    unfold P_ossl_HPKE_KEM_INFO_find_id, KEM_RA1, P_ERR_new in *. acb.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (ACONST_shbase m AC) as [GSB SHB]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB. rewrite ASHADOW_BASE_val in SHB.
    pose proof TB as TB0. unfold HPKE_tabs in TB. destruct TB as (TK & _ & _).
    unfold A_hpke_kem_tab, HPKE_KEM_ROW, HPKE_KEM_IDS in TK. cbn [id_rows] in TK.
    destruct TK as (R0 & R1 & R2 & R3 & R4 & _). unfold wz in R0, R1, R2, R3, R4. fix_rows R1 R2 R3 R4.
    assert (NE : id <> 16 /\ id <> 17 /\ id <> 18 /\ id <> 32 /\ id <> 33).
    { cbn [find_id HPKE_KEM_IDS] in FI. repeat split; intros ->; cbn in FI; discriminate FI. }
    destruct NE as (N1 & N2 & N3 & N4 & N5).
    carve_frame 32%nat ST.
    do 5 step. step. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      assert (E0 : id = 0) by (revert K0; rewrite ?unsigned_lit by lia; lia). subst id. try clear K0.
      step. step. step. step. cbn [Z.eqb].
      finish_jk; [reflexivity|].
      eapply HPKE_tabs_transport; [exact MU | exact WM | | exact TB0]. unfold HPKE_TAB_LO, HPKE_TAB_HI, A_hpke_kem_tab, A_hpke_aead_tab; cbn; lia.
    - assert (E0 : id <> 0) by (revert K0; rewrite ?unsigned_lit by lia; lia). try clear K0.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        assert (ACC : accessible mx 0x5ad7e0 360) by (apply kem_tab_acc; eapply ACONST_stack_frame; [exact AC| exact MU| exact WM| exact CEIL]) end.
      step. step. step. step. zstep. zstep. zstep. step. step.
      ck8_check_lit ACC 0x5ad7e0. st1. br_not. zstep. zstep. zstep. zstep. step. try if_true. try if_lit.
      ck8_check_lit ACC (0x5ad7e0 + 72). st1. br_not. zstep. zstep. zstep. zstep. step. try if_true. try if_lit.
      ck8_check_lit ACC (0x5ad7e0 + 144). st1. br_not. zstep. zstep. zstep. zstep. step. try if_true. try if_lit.
      ck8_check_lit ACC (0x5ad7e0 + 216). st1. br_not. zstep. zstep. zstep. zstep. step. try if_true. try if_lit.
      ck8_check_lit ACC (0x5ad7e0 + 288). st1. br_not. zstep. zstep. zstep. zstep. step. try if_false. try if_lit.
      (* [comment removed for export] *)
      step. step. step. step.
      replace (if id =? 0 then 181 else 188) with 188 by (destruct (Z.eqb_spec id 0); [lia| reflexivity]).
      finish_jk; [reflexivity|].
      eapply HPKE_tabs_transport; [exact MU | exact WM | | exact TB0]. unfold HPKE_TAB_LO, HPKE_TAB_HI, A_hpke_kem_tab, A_hpke_aead_tab; cbn; lia.
  Qed.
  Lemma kem_glue1 : forall id (s1o : word), glue_stmt (fun s1 => s1 = Z_to_bv 64 (f_line KEM_finder id)) KEM_RA1 KEM_RA2 P_ERR_set_debug A_str_hpke_util_c (f_line KEM_finder id) A_str_kem_find.
  Proof.
    unfold glue_stmt. intros until m1. intros -> MI. unfold KEM_RA1, KEM_RA2, P_ERR_set_debug, A_str_hpke_util_c, A_str_kem_find. cbn [f_line KEM_finder].
    replace (ret_pc (Z_to_bv 64 0x3e5b9c)) with (Z_to_bv 64 0x3e5b9c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    do 7 step. finish.
  Qed.
  Lemma kem_glue2 : glue_stmt (fun _ => True) KEM_RA2 KEM_RA3 P_ERR_set_error ERR_LIB_PROV (f_reason KEM_finder) 0.
  Proof.
    unfold glue_stmt. intros until m1. intros _ MI. unfold KEM_RA2, KEM_RA3, P_ERR_set_error, ERR_LIB_PROV. cbn [f_reason KEM_finder]. unfold PROV_R_INVALID_CURVE.
    replace (ret_pc (Z_to_bv 64 0x3e5bb8)) with (Z_to_bv 64 0x3e5bb8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    do 5 step. finish.
  Qed.
  Lemma kem_segC : forall id, segC_stmt 32 KEM_RA3 (fun jk ra s0 s1 => [CB 8 jk; C8 s1; C8 s0; C8 ra]) (fun _ s1i => s1i = Z_to_bv 64 (f_line KEM_finder id)).
  Proof.
    intros id. unfold segC_stmt. intros until lo. intros jk S1 FR ST MI CEIL LO. unfold KEM_RA3. acb.
    change (Z.opp 32) with (-32) in *.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    replace (ret_pc (Z_to_bv 64 0x3e5bcc)) with (Z_to_bv 64 0x3e5bcc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. step. step. step. step. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.
End S.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis RAISE : araise_stmt H.

  (* [comment removed for export] *)
  Lemma magree_of_munch : forall (R : Z -> Prop) W m m',
    munch W m m' -> wmono asegs m m' -> (forall a, R a -> outside W a) -> magree R m m'.
  Proof.
    intros R W m m' MU WM HR a Ha Hr. split.
    - unfold wa. apply MU. rewrite unsigned_lit by lia. apply HR. exact Hr.
    - intros Hw. apply WM. exact Hw.
  Qed.
  (* [comment removed for export] *)
  Lemma lib_addr_off_stack : forall s LBx LB m0 lo hi a,
    as_RHEAP H s LBx m0 -> (forall b, In b LB -> In b LBx) -> aceil <= lo -> lib_addr LB a -> outside [(lo, hi)] a.
  Proof.
    intros s LBx LB m0 lo hi a HP SUB CE [HX|[(b & Hb & Hr)|(b & Hb & Hr)]]; cbn; (split; [| exact I]).
    - assert (K : a < AIMG_TOP).
      { revert HX. unfold LIBX, LIBX0, LIBXW. unfold A_tsd_main, A_keys, A_next_key, A_key_lock, A_td_tsd_used, A_td_cancelbuf, AIMG_TOP. cbn. lia. }
      acb. unfold AIMG_TOP in *. lia.
    - pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ Hb)) as (_ & _ & _ & _ & D5 & _). lia.
    - (* [comment removed for export] *) pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ Hb)) as (_ & _ & D3 & _ & _ & _ & D7).
      pose proof (sh_aapp_range _ _ D7 D3) as (S1 & S2 & S3). pose proof aceil_range. unfold AHI_LO in S3. lia.
  Qed.
  Lemma arelro_across : forall W m m', arelro_lib m -> munch W m m' -> Forall (fun iv : Z * Z => 0x5ea000 <= fst iv) W -> arelro_lib m'.
  Proof.
    intros W m m' RL MU FW i Hi. rewrite <- (RL i Hi). unfold wa. apply MU. rewrite unsigned_lit by lia.
    clear - FW Hi. induction W as [|[lo hi] W IH]; [exact I|]. cbn. pose proof (Forall_inv FW) as K. cbn in K.
    split; [lia| exact (IH (Forall_inv_tail FW))].
  Qed.

  (* [comment removed for export] *)
  Lemma id_rows_xpres : forall LB SP X m m' ids a stride,
    xpres H LB SP X m m' -> 2 <= stride -> 0x571000 <= a -> a + stride * Z.of_nat (length ids) <= 0x5ea000 ->
    Forall (fun iv : Z * Z => a + stride * Z.of_nat (length ids) <= fst iv \/ snd iv <= a) X ->
    id_rows m a stride ids -> id_rows m' a stride ids.
  Proof.
    intros LB SP X m m' ids; induction ids as [|x ids IH]; intros a stride XP SP2 LOA HIA FX R; [exact I|].
    cbn [id_rows] in R |- *. destruct R as [R0 R1]. cbn [length] in HIA, FX. rewrite Nat2Z.inj_succ in HIA, FX.
    split.
    - eapply xpres_rw_cells'; [exact XP| exact R0| |].
      + right; left. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros b Hb. unfold aimg_client. nia.
      + eapply Forall_impl; [| exact FX]. cbn beta. intros iv K. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. nia.
    - eapply IH; [exact XP| exact SP2| nia| nia| | exact R1].
      eapply Forall_impl; [| exact FX]. cbn beta. intros iv K. nia.
  Qed.
  Lemma HPKE_tabs_xpres : forall LB SP X m m',
    xpres H LB SP X m m' -> Forall (fun iv : Z * Z => HPKE_TAB_HI <= fst iv \/ snd iv <= HPKE_TAB_LO) X -> HPKE_tabs m -> HPKE_tabs m'.
  Proof.
    intros LB SP X m m' XP FX (TK & TD & TA).
    unfold HPKE_TAB_LO, HPKE_TAB_HI, A_hpke_kem_tab, A_hpke_aead_tab in FX.
    split; [|split]; (eapply id_rows_xpres; [exact XP| | | | | eassumption]);
      unfold HPKE_KEM_ROW, HPKE_KDF_ROW, HPKE_AEAD_ROW, HPKE_KEM_IDS, HPKE_KDF_IDS, HPKE_AEAD_IDS, A_hpke_kem_tab, A_hpke_kdf_tab, A_hpke_aead_tab;
      cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul Pos.add]; try lia;
      (eapply Forall_impl; [| exact FX]; cbn beta; intros iv K; lia).
  Qed.

  (* [comment removed for export] *)
  Lemma raise_foot_frame : forall ph spi n lo,
    aceil <= lo -> lo <= spi -> errph_below ph aceil ->
    Forall (fun iv : Z * Z => spi + n <= fst iv \/ snd iv <= spi) (ERR_XE ++ memflag_foot ++ errph_foot ph).
  Proof.
    intros ph spi n lo CE LO EB. acb.
    apply Forall_app. split; [| apply Forall_app; split].
    - unfold ERR_XE, ERRNO_X, ARERRNO, ATP, ERR_X, A_err_string_lock, A_int_error_hash, A_err_string_once, A_err_string_ret, A_master_once, A_master_key, A_master_once_ret,
        A_tevent_once, A_tevent_ret, A_glob_tevent_reg, A_load_strings_once, A_load_strings_ret, A_optsdone, A_td_tsd_used, A_td_cancelbuf,
        A_keys, A_next_key, A_key_lock, A_tsd_main.
      cbn [app]. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
    - unfold memflag_foot, A_mem_inited. constructor; [cbn; lia| constructor].
    - destruct ph as [|c0]; [constructor|]. cbn [errph_foot errph_below] in *. unfold chain_below in EB. constructor; [cbn; lia| constructor].
  Qed.
  Lemma raise_foot_tabs : forall ph lo,
    errph_below ph lo -> match ph with ErrFresh => True | ErrReady c => AIMG_TOP <= blk_addr (ec_es c) end ->
    Forall (fun iv : Z * Z => HPKE_TAB_HI <= fst iv \/ snd iv <= HPKE_TAB_LO) (ERR_XE ++ memflag_foot ++ errph_foot ph).
  Proof.
    intros ph lo EB ES. unfold HPKE_TAB_HI, HPKE_TAB_LO, A_hpke_aead_tab, A_hpke_kem_tab.
    apply Forall_app. split; [| apply Forall_app; split].
    - unfold ERR_XE, ERRNO_X, ARERRNO, ATP, ERR_X, A_err_string_lock, A_int_error_hash, A_err_string_once, A_err_string_ret, A_master_once, A_master_key, A_master_once_ret,
        A_tevent_once, A_tevent_ret, A_glob_tevent_reg, A_load_strings_once, A_load_strings_ret, A_optsdone, A_td_tsd_used, A_td_cancelbuf,
        A_keys, A_next_key, A_key_lock, A_tsd_main.
      cbn [app]. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
    - unfold memflag_foot, A_mem_inited. constructor; [cbn; lia| constructor].
    - destruct ph as [|c0]; [constructor|]. cbn [errph_foot]. unfold AIMG_TOP in ES. constructor; [cbn; lia| constructor].
  Qed.

  (* [comment removed for export] *)
  Lemma scratch_foot_frame : forall LF m XS spi n lo,
    as_RFS H LF m -> Forall (fs_scratch H LF) XS -> aceil <= lo -> lo <= spi ->
    Forall (fun iv : Z * Z => spi + n <= fst iv \/ snd iv <= spi) XS.
  Proof.
    intros LF m XS spi n lo R FX CE LO. eapply Forall_impl; [| exact (fs_scratch_range_Forall H HH _ _ _ R FX)]. cbn beta. intros iv K. lia.
  Qed.
  Lemma scratch_foot_tabs : forall LF m XS,
    as_RFS H LF m -> Forall (fs_scratch H LF) XS -> Forall (fun iv : Z * Z => HPKE_TAB_HI <= fst iv \/ snd iv <= HPKE_TAB_LO) XS.
  Proof.
    intros LF m XS R FX. eapply Forall_impl; [| exact (fs_scratch_range_Forall H HH _ _ _ R FX)]. cbn beta. intros iv K.
    unfold HPKE_TAB_HI, A_hpke_aead_tab, AIMG_TOP in *. lia.
  Qed.

  Lemma ahfind_fail_gen : forall (f : finder) (FRZ ra1 ra2 ra3 funcA : Z) (gs gsl : list byte)
      (frc : list byte -> word -> word -> word -> list cell) (pre : list byte -> word -> list cell) (S1 : Z -> word -> word -> Prop),
    f_frame f = FRZ -> 16 <= FRZ <= 64 -> FRZ mod 16 = 0 -> (forall jk ra s0 s1, Z.of_nat (cells_size (frc jk ra s0 s1)) = FRZ) ->
    (forall jk ra s0 s1, frc jk ra s0 s1 = pre jk s1 ++ [C8 s0; C8 ra]) ->
    f_ra1 f = ra1 -> f_ra2 f = ra2 -> f_ra3 f = ra3 ->
    AROSTR funcA gs gsl -> gs <> [] -> Z.of_nat (length gs) < 32 -> 0 < funcA ->
    0 <= ra1 < 2^64 -> ra1 mod 2 = 0 -> 0 <= ra2 < 2^64 -> ra2 mod 2 = 0 -> 0 <= ra3 < 2^64 -> ra3 mod 2 = 0 ->
    (forall id, 0 <= f_line f id < 2^31) -> 0 < f_reason f < 2^23 ->
    segA_stmt f FRZ ra1 frc S1 ->
    (forall id s1o, glue_stmt (fun s1 => S1 id s1o s1) ra1 ra2 P_ERR_set_debug A_str_hpke_util_c (f_line f id) funcA) ->
    glue_stmt (fun _ => True) ra2 ra3 P_ERR_set_error ERR_LIB_PROV (f_reason f) 0 ->
    (forall id, segC_stmt FRZ ra3 frc (S1 id)) ->
    hfind_fail_stmt H f.
  Proof using HH RAISE.
    intros f FRZ ra1 ra2 ra3 funcA gs gsl frc pre S1 FRE FRR FR16 FRS FRL E1 E2 E3 RSG GSN GSL GPOS R1 R1E R2 R2E R3 R3E LNR REAS SA G1 G2 SC.
    unfold hfind_fail_stmt. intros until CH.
    intros VIS A0 IDR FI TB HP KREL BY CN AUX SPB SPA ST CEIL LO SH0 ERR MI TP AC MF IM GM RL EP EX EB ESH CP RAE RFS LFB CHN CHS PF ECL HAL.
    subst a0. rewrite FRE in LO. acb. pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (RS0 : 0 <= RAISE_STACK ph).
    { unfold RAISE_STACK, ERRDEBUG_STACK, FR_ERR_set_debug, CMALLOC_STACK, FR_CRYPTO_malloc, AMALLOC_STACK. lia. }
    set (SB := blocks_ERRST E) in *.
    assert (SUBx : forall b, In b LB -> In b (SB ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
    subst tp. rewrite unsigned_lit in ERR by (unfold ATP; lia).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply SA with (lo := lo) (id := id); try eassumption; lia|].
    intros msF1 mo1 KREL1 MP1 (t0' & t1' & t2' & s1i & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & jk & VIS1 & S1F & MU1 & WM1 & MI1 & ST1 & FR1 & TB1).
    set (spi := Z_to_bv 64 (bv_unsigned sp + - FRZ)) in *.
    assert (SPI : bv_unsigned spi = bv_unsigned sp + - FRZ) by (unfold spi; rewrite unsigned_lit by lia; reflexivity).
    assert (AG1 : magree (lib_addr LB) m m1).
    { eapply magree_of_munch; [exact MU1| exact WM1|]. intros a Ha. eapply lib_addr_off_stack; [exact HP| exact SUBx| exact CEIL| exact Ha]. }
    assert (MF1 : MEMFLAG m1 1) by (eapply MEMFLAG_across; [exact MU1| exact WM1| unfold A_mem_inited; cbn; lia| exact MF]).
    assert (IM1 : IMPL_mem m1) by (eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]).
    assert (GM1 : GOT_mem m1) by (eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]).
    assert (RL1 : arelro_lib m1) by (eapply arelro_across; [exact RL| exact MU1| constructor; [cbn; lia| constructor]]).
    assert (EP1 : ERRPH LB m1 ph) by (eapply ERRPH_frame; [exact EP| exact AG1]).
    assert (CP1 : CTXPH LB m1 (CtxReady x)) by (eapply CTXPH_frame; [exact CP| exact AG1]).
    assert (CW : Forall (aclient_write_ok H (SB ++ LB)) [(lo, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (HP1 : as_RHEAP H s (SB ++ LB) m1) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW]).
    assert (AUX1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW]).
    assert (AC1 : ACONST m1) by (eapply ACONST_stack_frame; [exact AC| exact MU1| exact WM1| exact CEIL]).
    assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]) by (eapply errno_across; [exact ERR| exact MU1| exact WM1| unfold ATP; cbn; lia]).
    assert (AGS : magree (lib_addr SB) m m1).
    { eapply magree_of_munch; [exact MU1| exact WM1|]. intros a Ha. eapply lib_addr_off_stack; [exact HP| intros b Hb; apply in_or_app; left; exact Hb| exact CEIL| exact Ha]. }
    assert (EX1 : ERRX m1 ph E).
    { destruct ph as [|c0]; [exact EX|]. cbn [ERRX] in *. destruct EX as (EXa & EXb & EXc & EXd). split; [| split; [exact EXb| split]].
      - eapply ERRST_agree; [| exact EXa| intros x0 Hx0; exact Hx0].
        eapply magree_of_munch; [exact MU1| exact WM1|]. intros a Ha. cbn [errph_below] in EB. unfold chain_below, in_range, ERRST_SIZE in *. cbn. lia.
      - eapply lib_shad_frame; [exact EXc| exact AGS].
      - (* [comment removed for export] *)
        unfold estrs_cells in *. apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) EXd _ Hb) as [bs BC]. exists bs.
        eapply rw_cells_agree; [exact AGS| exact BC|]. intros a Ha. right; left. exists b. split; [exact Hb|].
        unfold in_range in Ha. pose proof (rw_cells_bound _ _ _ _ BC) as BB. revert Ha BB. cbn [cells_size csize]. rewrite Nat.add_0_r.
        pose proof (ah_blocks H HH _ _ _ _ HP (in_or_app _ _ _ (or_introl Hb))) as (_ & _ & B3 & _). rewrite Z2Nat.id by lia. intros Ha BB. lia. }
    assert (ESH1 : errph_shad m1 ph).
    { destruct ph as [|c0]; [exact I|]. cbn [errph_shad] in ESH |- *. cbn [ERRPH] in EP. destruct EP as [_ ECx].
      eapply lib_shad_frame; [exact ESH|]. eapply magree_mono; [exact AG1|]. intros a Ha. eapply lib_addr_mono; [| exact Ha].
      intros b Hb. eapply chain_blocks_in; [exact ECx| exact Hb]. }
    pose proof (RFS_fsb H HH _ _ RFS) as (F1 & F2 & F3 & F4).
    assert (RFS1 : as_RFS H LF m1).
    { eapply (ah_RFS_frame H HH); [exact RFS| exact MU1| exact WM1|]. constructor; [left; cbn; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AIMG_TOP in *; lia| constructor]. }
    (* [comment removed for export] *)
    assert (CH0 : as_chain H m1 (bv_unsigned s0) CH).
    { eapply (achain_below H HH m m1); [exact CHN| exact CHS| exact MU1|]. constructor; [left; cbn; lia| constructor]. }
    assert (CH1 : as_chain H m1 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (ah_chain_cons H HH); [exact CH0| lia| lia| exact SPA| lia| lia|].
      pose proof FR1 as FR2. rewrite FRL in FR2. apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR2. destruct FR2 as [_ FR2].
      specialize (FRS jk ra s0 s1). rewrite FRL in FRS. rewrite cells_size_app in FRS. cbn [cells_size csize Nat.add] in FRS.
      replace (bv_unsigned sp - 16) with (bv_unsigned sp + - FRZ + Z.of_nat (cells_size (pre jk s1))) by lia.
      rewrite Z_to_bv_bv_unsigned || idtac. exact FR2 || (revert FR2; rewrite !Z_to_bv_bv_unsigned; intros FR2; exact FR2). }
    assert (CHS1 : forall fp' ra', In (fp', ra') ((bv_unsigned sp, bv_unsigned ra) :: CH) -> bv_unsigned spi + 16 <= fp').
    { rewrite SPI. intros fp' ra' [Ex|Hin]; [injection Ex as <- <-; lia| specialize (CHS _ _ Hin); lia]. }
    assert (PFx : forall rax PFg, (forall x0, In x0 (pf_shift rax PFg) -> In x0 (PF_hfind f ph)) -> pf_ok (as_TR H) PFg rax ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { intros rax PFg INC. eapply pf_ok_call; [exact PF| exact INC]. }
    (* [comment removed for export] *)
    pose proof R_hpke_util_c as RSF. unfold glue_stmt in G1, G2.
    eapply RAISE with (lo := lo) (B := B) (LB := LB) (s := s) (ph := ph) (E := E) (x := x) (errv := errv) (LF := LF)
      (CH := (bv_unsigned sp, bv_unsigned ra) :: CH)
      (file := A_str_hpke_util_c) (fs := S_hpke_util_c) (fsl := K_hpke_util_c) (func := funcA) (gs := gs) (gsl := gsl)
      (line := f_line f id) (lib := ERR_LIB_PROV) (reason := f_reason f) (ra2 := ra2) (ra3 := ra3);
      [exact VIS1| ..]; try eassumption; try (rewrite SPI); try eassumption; try (unfold ERR_LIB_PROV; lia); try (clear - SPA FR16 SPI FRR; lia).
    all: lazymatch goal with
         | |- _ <> [] => discriminate
         | |- Z.of_nat (length S_hpke_util_c) < 24 => vm_compute; reflexivity
         | |- 0 < A_str_hpke_util_c => unfold A_str_hpke_util_c; lia
         | |- 0 <= f_line _ _ < _ => apply LNR
         | |- rw_cells _ _ (errno_addr _) _ => rewrite unsigned_lit by (unfold ATP; lia); exact ERR1
         | |- _ = Z_to_bv 64 ATP => reflexivity
         | |- as_chain _ _ _ _ => exact CH1
         | |- errph_shad _ _ => exact ESH1
         | |- errph_closed_ok _ _ => exact ECL
         | |- errph_below _ _ => exact EB
         | |- errph_sh0 _ _ _ _ => eapply errph_sh0_sub; [eapply errph_sh0_munch; [exact SH0| exact MU1| exact WM1| apply Forall_cons; [apply stack0_ok_app; unfold AHI_LO; lia| apply Forall_nil]]
                                    | rewrite ?SPI, ?unsigned_lit by lia; clear - SPR FRR LO RS0 LO0 ACEILB CEIL; lia
                                    | rewrite ?SPI, ?unsigned_lit by lia; clear - SPA FR16 FRR; Z.div_mod_to_equations; lia]
         | |- pf_ok _ (PF_errnew _) _ _ => rewrite <- E1; apply PFx; intros x0 Hx; unfold PF_hfind; apply in_or_app; left; exact Hx
         | |- pf_ok _ PF_errdebug _ _ => rewrite <- E2; apply PFx; intros x0 Hx; unfold PF_hfind; apply in_or_app; right; apply in_or_app; left; exact Hx
         | |- pf_ok _ PF_errseterr _ _ => rewrite <- E3; apply PFx; intros x0 Hx; unfold PF_hfind; apply in_or_app; right; apply in_or_app; right; exact Hx
         | |- forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, mem_inv _ _ -> evt _ (fun _ => exists _ _ _ _ _ _ _ _ _ _ _ _, _ = MS _ _ (Z_to_bv 64 P_ERR_set_debug) _ _ _ _) _ =>
             intros; eapply (G1 id s1); [exact S1F| assumption]
         | |- forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, mem_inv _ _ -> evt _ (fun _ => exists _ _ _ _ _ _ _ _ _ _ _ _, _ = MS _ _ (Z_to_bv 64 P_ERR_set_error) _ _ _ _) _ =>
             intros; eapply G2; [exact I| assumption]
         | _ => idtac
         end.
    all: try lia.
    (* [comment removed for export] *)
    intros u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 msF' m' mo' s' errv' LBN c p1 p2 A1 A2 n1 n2 E'
           VIS' KREL' MP' MI' AC' ST' AUX' HP' MF' IM' GM' RL' ERR' DL RSZ EP' CP' EST' ESH' XS FXS XP' RFS' AL'.
    assert (LOS : lo <= bv_unsigned sp + - FRZ) by lia.
    pose proof (raise_foot_frame ph (bv_unsigned sp + - FRZ) (Z.of_nat (cells_size (frc jk ra s0 s1))) lo CEIL LOS EB) as FX0.
    pose proof (scratch_foot_frame LF m1 XS (bv_unsigned sp + - FRZ) (Z.of_nat (cells_size (frc jk ra s0 s1))) lo RFS1 FXS CEIL LOS) as FX1.
    pose proof (proj2 (Forall_app _ _ _) (conj FX1 FX0)) as FX.
    pose proof (xpres_rw_cells' H _ _ _ _ _ _ _ XP' FR1 ltac:(left; lia) FX) as FR'.

    eapply (ahh_evt_then H HH); [exact KREL'| exact VIS'| eapply (SC id) with (lo := lo) (s1 := s1) (ra := ra) (jk := jk); try eassumption; lia|].
    intros msF2 mo2 KREL2 MP2 (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & VIS2 & ST2).
    eapply (ah_done H HH). unfold hfind_fail_post. cbn [cfg_ms cfg_model].
    exists w0, w1, w2, d1, d2, d3, d4, d5, d6, d7, w3, w4, w5, w6, m', errv', s', LBN, c, p1, p2, A1, n1, A2, n2, XS.
    split; [exact VIS2|].
    split; [eapply (ah_mpres_trans H HH); [| exact MP2]; eapply (ah_mpres_trans H HH); [exact MP1| exact MP']|].
    split; [unfold c4_frame; repeat match goal with |- _ /\ _ => split end; assumption|].
    split; [exact ERR'|]. split; [exact DL|]. split; [exact RSZ|]. split; [exact EP'|]. split; [exact CP'|]. split; [exact EST'|]. split; [exact ESH'|].
    split.
    - (* [comment removed for export] *)
      eapply HPKE_tabs_xpres; [exact XP'| | exact TB1]. apply Forall_app. split; [eapply scratch_foot_tabs; [exact RFS1| exact FXS]|].
      eapply raise_foot_tabs; [| ].
      { destruct ph as [|c0]; [exact I|]. cbn [errph_below] in EB |- *. exact EB. }
      destruct ph as [|c0]; [exact I|]. cbn [ERRPH] in EP. destruct EP as [_ EC].
      pose proof EC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & _). pose proof (ah_blocks H HH _ _ _ _ HP (SUBx _ I5)) as (_ & _ & _ & B4 & _). exact B4.
    - split; [exact FXS|]. split.
      + (* [comment removed for export] *)
        eapply xpres_trans.
        * eapply (xpres_weaken H (SB ++ LB) LB); [| apply Z.le_refl| exact SUBx| intros ax K; exact K].
          eapply (xpres_of_munch H s (SB ++ LB) _ _ _ m m m1); [exact HH| exact HP| exact MU1| exact WM1|]. constructor; [left; cbn; lia| constructor].
        * eapply (xpres_weaken H LB LB); [exact XP'| lia| auto| auto].
      + split; [exact RFS'| exact AL'].
  Qed.

  Local Ltac gen_side :=
    lazymatch goal with
    | |- AROSTR _ _ _ => first [apply R_kdf_find| apply R_kem_find| apply R_aead_find]
    | |- _ <> [] => discriminate
    | |- Z.of_nat (length _) < 32 => vm_compute; reflexivity
    | |- forall _ _ _ _, Z.of_nat (cells_size _) = _ => intros; reflexivity
    | |- forall _ _ _ _, _ = _ ++ _ => intros; reflexivity
    | |- forall id, _ <= f_line _ id < _ => intros id; cbn [f_line KEM_finder KDF_finder AEAD_finder]; try (destruct (id =? 0)); lia
    | |- _ < f_reason _ < _ => cbn [f_reason KEM_finder KDF_finder AEAD_finder]; unfold PROV_R_INVALID_CURVE, PROV_R_INVALID_KDF, PROV_R_INVALID_AEAD; lia
    | |- _ mod _ = _ => reflexivity
    | |- f_frame _ = _ => reflexivity
    | |- f_ra1 _ = _ => reflexivity
    | |- f_ra2 _ = _ => reflexivity
    | |- f_ra3 _ = _ => reflexivity
    | |- _ => try (unfold KDF_RA1, KDF_RA2, KDF_RA3, KEM_RA1, KEM_RA2, KEM_RA3, AEAD_RA1, AEAD_RA2, AEAD_RA3, A_str_kdf_find, A_str_kem_find, A_str_aead_find; lia)
    end.
  Lemma ahfind_fail_kdf : hfind_fail_stmt H KDF_finder.
  Proof using HH RAISE.
    eapply (ahfind_fail_gen KDF_finder 16 KDF_RA1 KDF_RA2 KDF_RA3 A_str_kdf_find S_kdf_find K_kdf_find (fun _ ra s0 _ => [C8 s0; C8 ra]) (fun _ _ => []) (fun _ s1 s1i => s1i = s1));
      [gen_side ..| exact kdf_segA| exact kdf_glue1| exact kdf_glue2| intros id; exact kdf_segC].
  Qed.
  Lemma ahfind_fail_aead : hfind_fail_stmt H AEAD_finder.
  Proof using HH RAISE.
    eapply (ahfind_fail_gen AEAD_finder 16 AEAD_RA1 AEAD_RA2 AEAD_RA3 A_str_aead_find S_aead_find K_aead_find (fun _ ra s0 _ => [C8 s0; C8 ra]) (fun _ _ => []) (fun _ s1 s1i => s1i = s1));
      [gen_side ..| exact aead_segA| exact aead_glue1| exact aead_glue2| intros id; exact aead_segC].
  Qed.
  Lemma ahfind_fail_kem : hfind_fail_stmt H KEM_finder.
  Proof using HH RAISE.
    eapply (ahfind_fail_gen KEM_finder 32 KEM_RA1 KEM_RA2 KEM_RA3 A_str_kem_find S_kem_find K_kem_find (fun jk ra s0 s1 => [CB 8 jk; C8 s1; C8 s0; C8 ra])
              (fun jk s1 => [CB 8 jk; C8 s1]) (fun id _ s1i => s1i = Z_to_bv 64 (f_line KEM_finder id)));
      [gen_side ..| exact kem_segA| exact kem_glue1| exact kem_glue2| exact kem_segC].
  Qed.
End W.

