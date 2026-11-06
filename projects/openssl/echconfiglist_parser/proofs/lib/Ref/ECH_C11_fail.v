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
     ECH_C0_stmt ECH_C1_stmt ECH_C2_stmt ECH_LibFrame ECH_C4_stmt ECH_C4_rep ECH_C4_frame ECH_C4_frame2 ECH_C4_raise ECH_Rostr ECH_C11_stmt ECH_C11_find.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition A_str_hpke_util_c : Z := 0x1f5b8.
Definition A_str_kem_find : Z := 0x18d0a.
Definition A_str_kdf_find : Z := 0x2f110.
Definition A_str_aead_find : Z := 0x137ef.
Definition S_hpke_util_c : list byte := Eval vm_compute in img_cstr A_str_hpke_util_c 64.
Definition K_hpke_util_c : list byte := Eval vm_compute in img_slack A_str_hpke_util_c (length S_hpke_util_c).
Definition S_kem_find : list byte := Eval vm_compute in img_cstr A_str_kem_find 64.
Definition K_kem_find : list byte := Eval vm_compute in img_slack A_str_kem_find (length S_kem_find).
Definition S_kdf_find : list byte := Eval vm_compute in img_cstr A_str_kdf_find 64.
Definition K_kdf_find : list byte := Eval vm_compute in img_slack A_str_kdf_find (length S_kdf_find).
Definition S_aead_find : list byte := Eval vm_compute in img_cstr A_str_aead_find 64.
Definition K_aead_find : list byte := Eval vm_compute in img_slack A_str_aead_find (length S_aead_find).

(* [comment removed for export] *)
Definition KDF_RA1 : Z := 0x1bf364.  Definition KDF_RA2 : Z := 0x1bf37c.  Definition KDF_RA3 : Z := 0x1bf38c.
Definition AEAD_RA1 : Z := 0x1bf3d8. Definition AEAD_RA2 : Z := 0x1bf3f0. Definition AEAD_RA3 : Z := 0x1bf400.
Definition KEM_RA1 : Z := 0x1bf2ec.  Definition KEM_RA2 : Z := 0x1bf304.  Definition KEM_RA3 : Z := 0x1bf314.

Section S.
  Context {HCEIL : HeapCeil}.
  Lemma R_hpke_util_c : ROSTR A_str_hpke_util_c S_hpke_util_c K_hpke_util_c.
  Proof. apply ROSTR_of_image; vm_compute; reflexivity. Qed.
  Lemma R_kem_find : ROSTR A_str_kem_find S_kem_find K_kem_find.
  Proof. apply ROSTR_of_image; vm_compute; reflexivity. Qed.
  Lemma R_kdf_find : ROSTR A_str_kdf_find S_kdf_find K_kdf_find.
  Proof. apply ROSTR_of_image; vm_compute; reflexivity. Qed.
  Lemma R_aead_find : ROSTR A_str_aead_find S_aead_find K_aead_find.
  Proof. apply ROSTR_of_image; vm_compute; reflexivity. Qed.

  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  (* [comment removed for export] *)
  Local Ltac finish_jk := apply evt_done; hnf; repeat (lazymatch goal with |- ex _ => eexists end);
    lazymatch goal with
    | |- list byte => exact []
    | |- _ = _ /\ _ => split; [reflexivity|]; repeat match goal with |- _ /\ _ => split end; try assumption;
                        try (lazymatch goal with |- rw_cells _ _ _ _ => eassumption end)
    end.
  Local Ltac br_not := step; try (let K0 := fresh "K0" in if_cases K0; zify_cond K0; [kill K0|]; clear K0).

  (* [comment removed for export] *)
  Definition segA_stmt (f : finder) (FRZ ra1 : Z) (frc : list byte -> word -> word -> word -> list cell) (S1 : Z -> word -> word -> Prop) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (id lo : Z),
      0 <= id < 2^16 -> find_id (f_ids f) id = None -> HPKE_tabs m ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - FRZ -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists t0' t1' t2' s0i s1i a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' jk,
                   ms' = MS (mkR (Z_to_bv 64 ra1) (Z_to_bv 64 (bv_unsigned sp + - FRZ)) gp tp t0' t1' t2' s0i s1i a0' a1' a2' a3' a4' a5' a6' a7'
                                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 P_ERR_new) fc None m' (seg_rom rsegs)
                   /\ S1 id s1 s1i
                   /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp + - FRZ)
                   /\ rw_cells rsegs m' (bv_unsigned sp + - FRZ) (frc jk ra s0 s1) /\ HPKE_tabs m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 id) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (f_entry f)) fc None m (seg_rom rsegs)).
  Definition glue_stmt (S1 : word -> Prop) (raA raB target a0v a1v a2v : Z) : Prop :=
    forall (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (m1 : mem), S1 s1 -> mem_inv rsegs m1 ->
      evt rsegs (fun ms' => exists v0 v1 v2 c3 c4 c5 c6 c7 v3 v4 v5 v6,
                   ms' = MS (mkR (Z_to_bv 64 raB) sp gp tp v0 v1 v2 s0 s1 (Z_to_bv 64 a0v) (Z_to_bv 64 a1v) (Z_to_bv 64 a2v) c3 c4 c5 c6 c7
                                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6) F (Z_to_bv 64 target) fc None m1 (seg_rom rsegs))
        (MS (mkR (Z_to_bv 64 raA) sp gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
            F (ret_pc (Z_to_bv 64 raA)) fc None m1 (seg_rom rsegs)).
  Definition segC_stmt (FRZ ra3 : Z) (frc : list byte -> word -> word -> word -> list cell) (S1 : word -> word -> Prop) : Prop :=
    forall (ra sp gp tp s0 s1 s0i s1i s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (m' : mem) (lo : Z) (jk : list byte),
      S1 s1 s1i ->
      rw_cells rsegs m' (bv_unsigned sp + - FRZ) (frc jk ra s0 s1) -> stk rsegs m' lo (bv_unsigned sp + - FRZ) -> mem_inv rsegs m' ->
      hceil <= lo -> lo <= bv_unsigned sp - FRZ ->
      evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
                   ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                            F (ret_pc ra) fc None m' (seg_rom rsegs) /\ stk rsegs m' lo (bv_unsigned sp))
        (MS (mkR (Z_to_bv 64 ra3) (Z_to_bv 64 (bv_unsigned sp + - FRZ)) gp tp u0 u1 u2 s0i s1i b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
            F (ret_pc (Z_to_bv 64 ra3)) fc None m' (seg_rom rsegs)).


  (* [comment removed for export] *)
  Lemma kdf_segA : segA_stmt KDF_finder 16 KDF_RA1 (fun _ ra s0 _ => [C8 s0; C8 ra]) (fun _ s1 s1i => s1i = s1).
  Proof.
    unfold segA_stmt. cbn [f_ids f_entry KDF_finder]. change (Z.opp 16) with (-16).
    intros until lo. intros IDR FI TB ST CEIL LO MI.
    unfold P_ossl_HPKE_KDF_INFO_find_id, KDF_RA1, P_ERR_new in *. hcb.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof TB as TB0. unfold HPKE_tabs in TB. destruct TB as (_ & TD & _).
    unfold A_hpke_kdf_tab, HPKE_KDF_ROW, HPKE_KDF_IDS in TD. cbn [id_rows] in TD.
    destruct TD as (R0 & R1 & R2 & _). unfold wz in R0, R1, R2.
    match type of R1 with rw_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in R1 end.
    match type of R2 with rw_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in R2 end.
    assert (NE : id <> 1 /\ id <> 2 /\ id <> 3).
    { cbn [find_id HPKE_KDF_IDS] in FI. repeat split; intros ->; cbn in FI; discriminate FI. }
    destruct NE as (N1 & N2 & N3).
    carve_frame 16%nat ST.
    do 4 st1. step. step. step. step.
    st1. br_not. step. step. step. try if_true.
    st1. br_not. step. step. step. try if_true.
    st1. br_not. step. step. step. try if_false.
    step.
    finish_jk; [reflexivity|].
    eapply HPKE_tabs_transport; [exact MU | exact WM | | exact TB0]. unfold HPKE_TAB_LO, HPKE_TAB_HI, A_hpke_kem_tab, A_hpke_aead_tab; cbn; lia.
  Qed.

  Lemma kdf_glue1 : forall id s1o, glue_stmt (fun s1 => s1 = s1o) KDF_RA1 KDF_RA2 P_ERR_set_debug A_str_hpke_util_c (f_line KDF_finder id) A_str_kdf_find.
  Proof.
    unfold glue_stmt. intros until m1. intros _ MI. unfold KDF_RA1, KDF_RA2, P_ERR_set_debug, A_str_hpke_util_c, A_str_kdf_find. cbn [f_line KDF_finder].
    replace (ret_pc (Z_to_bv 64 1831780)) with (Z_to_bv 64 1831780) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    do 6 step. finish.
  Qed.
  Lemma kdf_glue2 : glue_stmt (fun _ => True) KDF_RA2 KDF_RA3 P_ERR_set_error ERR_LIB_PROV (f_reason KDF_finder) 0.
  Proof.
    unfold glue_stmt. intros until m1. intros _ MI. unfold KDF_RA2, KDF_RA3, P_ERR_set_error, ERR_LIB_PROV, PROV_R_INVALID_KDF. cbn [f_reason KDF_finder]. unfold PROV_R_INVALID_KDF.
    replace (ret_pc (Z_to_bv 64 1831804)) with (Z_to_bv 64 1831804) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    do 4 step. finish.
  Qed.
  Lemma kdf_segC : segC_stmt 16 KDF_RA3 (fun _ ra s0 _ => [C8 s0; C8 ra]) (fun s1 s1i => s1i = s1).
  Proof.
    unfold segC_stmt. intros until lo. intros jk -> FR ST MI CEIL LO. unfold KDF_RA3. hcb.
    change (Z.opp 16) with (-16) in *.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    replace (ret_pc (Z_to_bv 64 1831820)) with (Z_to_bv 64 1831820) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. st1. st1. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.

  (* [comment removed for export] *)
  Lemma kem_segA : segA_stmt KEM_finder 32 KEM_RA1 (fun jk ra s0 s1 => [CB 8 jk; C8 s1; C8 s0; C8 ra]) (fun id _ s1i => s1i = Z_to_bv 64 (f_line KEM_finder id)).
  Proof.
    unfold segA_stmt. cbn [f_ids f_entry f_line KEM_finder]. change (Z.opp 32) with (-32).
    intros until lo. intros IDR FI TB ST CEIL LO MI.
    unfold P_ossl_HPKE_KEM_INFO_find_id, KEM_RA1, P_ERR_new in *. hcb.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof TB as TB0. unfold HPKE_tabs in TB. destruct TB as (TK & _ & _).
    unfold A_hpke_kem_tab, HPKE_KEM_ROW, HPKE_KEM_IDS in TK. cbn [id_rows] in TK.
    destruct TK as (R0 & R1 & R2 & R3 & R4 & _). unfold wz in R0, R1, R2, R3, R4.
    match type of R1 with rw_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in R1 end.
    match type of R2 with rw_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in R2 end.
    match type of R3 with rw_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in R3 end.
    match type of R4 with rw_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in R4 end.
    assert (NE : id <> 16 /\ id <> 17 /\ id <> 18 /\ id <> 32 /\ id <> 33).
    { cbn [find_id HPKE_KEM_IDS] in FI. repeat split; intros ->; cbn in FI; discriminate FI. }
    destruct NE as (N1 & N2 & N3 & N4 & N5).
    carve_frame 32%nat ST.
    do 5 st1.
    destruct (Z.eqb_spec id 0) as [E0|E0].
    { subst id. step. try if_true. step. step. finish_jk; [reflexivity|].
      eapply HPKE_tabs_transport; [exact MU | exact WM | | exact TB0]. unfold HPKE_TAB_LO, HPKE_TAB_HI, A_hpke_kem_tab, A_hpke_aead_tab; cbn; lia. }
    br_not. step. step. step. step.
    st1. br_not. step. step. step. try if_true.
    st1. br_not. step. step. step. try if_true.
    st1. br_not. step. step. step. try if_true.
    st1. br_not. step. step. step. try if_true.
    st1. br_not. step. step. step. try if_false.
    step. step. step.
    finish_jk; [reflexivity|].
    eapply HPKE_tabs_transport; [exact MU | exact WM | | exact TB0]. unfold HPKE_TAB_LO, HPKE_TAB_HI, A_hpke_kem_tab, A_hpke_aead_tab; cbn; lia.
  Qed.
  Lemma kem_glue1 : forall id (s1o : word), glue_stmt (fun s1 => s1 = Z_to_bv 64 (f_line KEM_finder id)) KEM_RA1 KEM_RA2 P_ERR_set_debug A_str_hpke_util_c (f_line KEM_finder id) A_str_kem_find.
  Proof.
    unfold glue_stmt. intros until m1. intros -> MI. unfold KEM_RA1, KEM_RA2, P_ERR_set_debug, A_str_hpke_util_c, A_str_kem_find.
    replace (ret_pc (Z_to_bv 64 1831660)) with (Z_to_bv 64 1831660) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    do 6 step. finish.
  Qed.
  Lemma kem_glue2 : glue_stmt (fun _ => True) KEM_RA2 KEM_RA3 P_ERR_set_error ERR_LIB_PROV (f_reason KEM_finder) 0.
  Proof.
    unfold glue_stmt. intros until m1. intros _ MI. unfold KEM_RA2, KEM_RA3, P_ERR_set_error, ERR_LIB_PROV. cbn [f_reason KEM_finder]. unfold PROV_R_INVALID_CURVE.
    replace (ret_pc (Z_to_bv 64 1831684)) with (Z_to_bv 64 1831684) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    do 4 step. finish.
  Qed.
  Lemma kem_segC : forall id, segC_stmt 32 KEM_RA3 (fun jk ra s0 s1 => [CB 8 jk; C8 s1; C8 s0; C8 ra]) (fun _ s1i => s1i = Z_to_bv 64 (f_line KEM_finder id)).
  Proof.
    intros id. unfold segC_stmt. intros until jk. intros _ FR ST MI CEIL LO. unfold KEM_RA3. hcb.
    change (Z.opp 32) with (-32) in *.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    replace (ret_pc (Z_to_bv 64 1831700)) with (Z_to_bv 64 1831700) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. st1. st1. st1. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.

  (* [comment removed for export] *)
  Lemma aead_segA : segA_stmt AEAD_finder 16 AEAD_RA1 (fun _ ra s0 _ => [C8 s0; C8 ra]) (fun _ s1 s1i => s1i = s1).
  Proof.
    unfold segA_stmt. cbn [f_ids f_entry AEAD_finder]. change (Z.opp 16) with (-16).
    intros until lo. intros IDR FI TB ST CEIL LO MI.
    unfold P_ossl_HPKE_AEAD_INFO_find_id, AEAD_RA1, P_ERR_new in *. hcb.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof TB as TB0. unfold HPKE_tabs in TB. destruct TB as (_ & _ & TA).
    unfold A_hpke_aead_tab, HPKE_AEAD_ROW, HPKE_AEAD_IDS in TA. cbn [id_rows] in TA.
    destruct TA as (R0 & R1 & R2 & R3 & _). unfold wz in R0, R1, R2, R3.
    match type of R1 with rw_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in R1 end.
    match type of R2 with rw_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in R2 end.
    match type of R3 with rw_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in R3 end.
    assert (NE : id <> 1 /\ id <> 2 /\ id <> 3 /\ id <> 65535).
    { cbn [find_id HPKE_AEAD_IDS] in FI. repeat split; intros ->; cbn in FI; discriminate FI. }
    destruct NE as (N1 & N2 & N3 & N4).
    carve_frame 16%nat ST.
    do 4 st1. step. step. step. step.
    st1. br_not. step. step. step. try if_true.
    st1. br_not. step. step. step. try if_true.
    st1. br_not. step. step. step. try if_true.
    st1. br_not. step. step. step. try if_false.
    step.
    finish_jk; [reflexivity|].
    eapply HPKE_tabs_transport; [exact MU | exact WM | | exact TB0]. unfold HPKE_TAB_LO, HPKE_TAB_HI, A_hpke_kem_tab, A_hpke_aead_tab; cbn; lia.
  Qed.
  Lemma aead_glue1 : forall id s1o, glue_stmt (fun s1 => s1 = s1o) AEAD_RA1 AEAD_RA2 P_ERR_set_debug A_str_hpke_util_c (f_line AEAD_finder id) A_str_aead_find.
  Proof.
    unfold glue_stmt. intros until m1. intros _ MI. unfold AEAD_RA1, AEAD_RA2, P_ERR_set_debug, A_str_hpke_util_c, A_str_aead_find. cbn [f_line AEAD_finder].
    replace (ret_pc (Z_to_bv 64 1831896)) with (Z_to_bv 64 1831896) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    do 6 step. finish.
  Qed.
  Lemma aead_glue2 : glue_stmt (fun _ => True) AEAD_RA2 AEAD_RA3 P_ERR_set_error ERR_LIB_PROV (f_reason AEAD_finder) 0.
  Proof.
    unfold glue_stmt. intros until m1. intros _ MI. unfold AEAD_RA2, AEAD_RA3, P_ERR_set_error, ERR_LIB_PROV. cbn [f_reason AEAD_finder]. unfold PROV_R_INVALID_AEAD.
    replace (ret_pc (Z_to_bv 64 1831920)) with (Z_to_bv 64 1831920) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    do 4 step. finish.
  Qed.
  Lemma aead_segC : segC_stmt 16 AEAD_RA3 (fun _ ra s0 _ => [C8 s0; C8 ra]) (fun s1 s1i => s1i = s1).
  Proof.
    unfold segC_stmt. intros until lo. intros jk -> FR ST MI CEIL LO. unfold AEAD_RA3. hcb.
    change (Z.opp 16) with (-16) in *.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    replace (ret_pc (Z_to_bv 64 1831936)) with (Z_to_bv 64 1831936) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. st1. st1. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.
End S.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HX : heap_sr_hyps_x H.
  Hypothesis EGS : egs_stmt H.
  Let HH : heap_sr_hyps H := proj1 HX.

  (* [comment removed for export] *)
  Lemma id_rows_xpres : forall LB SP X m m' ids a stride,
    xpres LB SP X m m' -> 2 <= stride -> 0x27e000 <= a -> a + stride * Z.of_nat (length ids) <= 0x2db000 ->
    Forall (fun iv : Z * Z => a + stride * Z.of_nat (length ids) <= fst iv \/ snd iv <= a) X ->
    id_rows m a stride ids -> id_rows m' a stride ids.
  Proof.
    intros LB SP X m m' ids; induction ids as [|x ids IH]; intros a stride XP SP2 LOA HIA FX R; [exact I|].
    cbn [id_rows] in R |- *. destruct R as [R0 R1]. cbn [length] in HIA, FX. rewrite Nat2Z.inj_succ in HIA, FX.
    split.
    - eapply xpres_rw_cells'; [exact XP| exact R0| |].
      + right; left. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK. nia.
      + eapply Forall_impl; [| exact FX]. cbn beta. intros iv K. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. nia.
    - eapply IH; [exact XP| exact SP2| nia| nia| | exact R1].
      eapply Forall_impl; [| exact FX]. cbn beta. intros iv K. nia.
  Qed.
  Lemma HPKE_tabs_xpres : forall LB SP X m m',
    xpres LB SP X m m' -> Forall (fun iv : Z * Z => HPKE_TAB_HI <= fst iv \/ snd iv <= HPKE_TAB_LO) X -> HPKE_tabs m -> HPKE_tabs m'.
  Proof.
    intros LB SP X m m' XP FX (TK & TD & TA).
    unfold HPKE_TAB_LO, HPKE_TAB_HI, A_hpke_kem_tab, A_hpke_aead_tab in FX.
    split; [|split]; (eapply id_rows_xpres; [exact XP| | | | | eassumption]);
      unfold HPKE_KEM_ROW, HPKE_KDF_ROW, HPKE_AEAD_ROW, HPKE_KEM_IDS, HPKE_KDF_IDS, HPKE_AEAD_IDS, A_hpke_kem_tab, A_hpke_kdf_tab, A_hpke_aead_tab;
      cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul Pos.add]; try lia;
      (eapply Forall_impl; [| exact FX]; cbn beta; intros iv K; lia).
  Qed.

  Lemma hfind_fail_gen : forall (f : finder) (FRZ ra1 ra2 ra3 funcA : Z) (gs gsl : list byte)
      (frc : list byte -> word -> word -> word -> list cell) (S1 : Z -> word -> word -> Prop),
    f_frame f = FRZ -> 0 <= FRZ <= 64 -> FRZ mod 16 = 0 -> (forall jk ra s0 s1, Z.of_nat (cells_size (frc jk ra s0 s1)) = FRZ) ->
    ROSTR funcA gs gsl -> gs <> [] -> Z.of_nat (length gs) < 32 -> 0 < funcA ->
    0 <= ra1 < 2^64 -> ra1 mod 2 = 0 -> 0 <= ra2 < 2^64 -> ra2 mod 2 = 0 -> 0 <= ra3 < 2^64 -> ra3 mod 2 = 0 ->
    (forall id, 0 <= f_line f id < 2^31) -> 0 < f_reason f < 2^23 ->
    segA_stmt f FRZ ra1 frc S1 ->
    (forall id s1o, glue_stmt (fun s1 => S1 id s1o s1) ra1 ra2 P_ERR_set_debug A_str_hpke_util_c (f_line f id) funcA) ->
    glue_stmt (fun _ => True) ra2 ra3 P_ERR_set_error ERR_LIB_PROV (f_reason f) 0 ->
    (forall id, segC_stmt FRZ ra3 frc (S1 id)) ->
    hfind_fail_stmt H f.
  Proof using HX EGS.
    intros f FRZ ra1 ra2 ra3 funcA gs gsl frc S1 FRE FRR FR16 FRS RSG GSN GSL GPOS R1 R1E R2 R2E R3 R3E LNR REAS SA G1 G2 SC.
    unfold hfind_fail_stmt. intros until errv.
    intros A0 IDR FI TB HP KREL BY CN BG AUX SPB SPA ST CEIL LO ERR MI TP MF IM GM RL EP EX EB CP RAE.
    subst a0. rewrite FRE in LO. hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (RS0 : 0 <= RAISE_STACK ph).
    { unfold RAISE_STACK, ERRDEBUG_STACK, FR_ERR_set_debug, CMALLOC_STACK, FR_CRYPTO_malloc, RMALLOC_STACK. lia. }
    set (SB := blocks_ERRST E) in *.
    assert (SUBx : forall b, In b LB -> In b (SB ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
    assert (RBL : forall b, In b LB -> rblock_range (blk_addr b) (blk_size b)).
    { intros b Hb. eapply (HH_RHEAP_block_range H HH); [exact HP| apply SUBx; exact Hb]. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply SA with (lo := lo) (id := id); try eassumption; lia|].
    intros ms1 (t0' & t1' & t2' & s0i & s1i & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & jk & -> & S1F & MU1 & WM1 & MI1 & ST1 & FR1 & TB1).
    set (spi := Z_to_bv 64 (bv_unsigned sp + - FRZ)) in *.
    assert (SPI : bv_unsigned spi = bv_unsigned sp + - FRZ) by (unfold spi; rewrite unsigned_lit by lia; reflexivity).
    assert (FW1 : Forall stack_or_errno [(lo, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (CW1 : C4W LB m1 ph x).
    { eapply C4W_stack; [| exact MU1| exact WM1| exact FW1| exact RBL]. unfold C4W. tauto. }
    destruct CW1 as (MF1 & IM1 & GM1 & RL1 & EP1 & CP1).
    assert (HP1 : hs_RHEAP H s (SB ++ LB) m1).
    { eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]. constructor; [left; cbn; lia| constructor]. }
    assert (AUX1 : hs_rauxv_ok H m1 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor]. }
    assert (ERR1 : rw_cells rsegs m1 (errno_addr tp) [C4 errv]).
    { subst tp. rewrite errno_RATP in *. eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. unfold RERRNO. cbn. lia. }
    assert (EX1 : ERRX m1 ph E).
    { destruct ph as [|c0]; [exact EX|]. cbn [ERRX] in *. eapply ERRST_munch; [exact EX| exact MU1| exact WM1|].
      cbn [errph_below] in EB. unfold chain_below in EB. unfold ERRST_SIZE in *. cbn. lia. }
    (* [comment removed for export] *)
    pose proof R_hpke_util_c as RSF.
    unfold glue_stmt in G1, G2.
    eapply (raise_spec H HX EGS) with (lo := lo) (B := B) (LB := LB) (s := s) (ph := ph) (E := E) (x := x) (errv := errv)
      (file := A_str_hpke_util_c) (fs := S_hpke_util_c) (fsl := K_hpke_util_c) (func := funcA) (gs := gs) (gsl := gsl)
      (line := f_line f id) (lib := ERR_LIB_PROV) (reason := f_reason f) (ra2 := ra2) (ra3 := ra3);
      try eassumption; try (rewrite SPI); try eassumption; try (unfold ERR_LIB_PROV; lia); try (clear - SPA FR16 SPI; lia).
    all: lazymatch goal with
         | |- _ <> [] => discriminate
         | |- Z.of_nat (length S_hpke_util_c) < 24 => vm_compute; reflexivity
         | |- 0 < A_str_hpke_util_c => unfold A_str_hpke_util_c; lia
         | |- 0 <= f_line _ _ < _ => apply LNR
         | |- forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, mem_inv _ _ -> evt _ (fun _ => exists _ _ _ _ _ _ _ _ _ _ _ _, _ = MS _ _ (Z_to_bv 64 P_ERR_set_debug) _ _ _ _) _ =>
             intros; eapply (G1 id s1); [exact S1F| assumption]
         | |- forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, mem_inv _ _ -> evt _ (fun _ => exists _ _ _ _ _ _ _ _ _ _ _ _, _ = MS _ _ (Z_to_bv 64 P_ERR_set_error) _ _ _ _) _ =>
             intros; eapply G2; [exact I| assumption]
         | _ => idtac
         end.
    (* [comment removed for export] *)
    intros u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m' mo' s' errv' LBN c p1 p2 A1 A2 n1 n2 E'
           KREL' MP' MI' ST' AUX' HP' MF' IM' GM' RL' ERR' DL RSZ EP' CP' EST' XP'.
    assert (FX : Forall (fun iv : Z * Z => bv_unsigned sp + - FRZ + Z.of_nat (cells_size (frc jk ra s0 s1)) <= fst iv \/ snd iv <= bv_unsigned sp + - FRZ)
                        (ERR_X ++ memflag_foot ++ errph_foot ph)).
    { rewrite FRS. apply Forall_app. split; [| apply Forall_app; split].
      - unfold ERR_X, A_err_string_once, A_defctx_inited, A_tevent_once, A_load_strings_once, A_optsdone, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, A_tsd_main.
        repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
      - unfold memflag_foot, A_mem_inited. constructor; [cbn; lia| constructor].
      - destruct ph as [|c0]; [constructor|]. cbn [errph_foot errph_below] in *. unfold chain_below in EB. constructor; [cbn; lia| constructor]. }
    pose proof (xpres_rw_cells' _ _ _ _ _ _ _ XP' FR1 ltac:(left; lia) FX) as FR'.
    eapply (sr_evt_krel H HH); [exact KREL'| eapply (SC id) with (lo := lo) (s0 := s0) (s1 := s1) (ra := ra) (jk := jk); try eassumption; lia|].
    intros ms2 (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & -> & ST2).
    apply (sr_done H HH). unfold hfind_fail_post. cbn [cfg_ms cfg_model].
    exists w0, w1, w2, d1, d2, d3, d4, d5, d6, d7, w3, w4, w5, w6, m', errv', s', LBN, c, p1, p2, A1, n1, A2, n2.
    split; [reflexivity|]. split; [exact MP'|]. split; [unfold c4_frame; cbn [cfg_model]; tauto|].
    split; [exact ERR'|]. split; [exact DL|]. split; [exact RSZ|]. split; [exact EP'|]. split; [exact CP'|]. split; [exact EST'|].
    split.
    - (* [comment removed for export] *)
      eapply HPKE_tabs_xpres; [exact XP'| | exact TB1]. unfold HPKE_TAB_HI, HPKE_TAB_LO, A_hpke_aead_tab, A_hpke_kem_tab.
      apply Forall_app. split; [| apply Forall_app; split].
      + unfold ERR_X, A_err_string_once, A_defctx_inited, A_tevent_once, A_load_strings_once, A_optsdone, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, A_tsd_main.
        repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
      + unfold memflag_foot, A_mem_inited. constructor; [cbn; lia| constructor].
      + destruct ph as [|c0]; [constructor|]. cbn [errph_foot ERRPH] in *. destruct EP as [_ EC].
        pose proof EC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _). pose proof (RBL _ I5) as RB5. unfold rblock_range in RB5. rewrite Z5 in RB5.
        unfold ERRST_SIZE in *. constructor; [cbn; lia| constructor].
    - (* [comment removed for export] *)
      eapply xpres_trans.
      + eapply xpres_of_munch; [exact MU1| exact WM1| |].
        * constructor; [left; cbn; lia| constructor].
        * intros b Hb. pose proof (RBL b Hb) as RB. unfold rblock_range in RB. lia.
      + eapply xpres_weaken; [exact XP'| lia| auto| auto].
  Qed.

  Local Ltac gen_side :=
    lazymatch goal with
    | |- ROSTR _ _ _ => first [apply R_kdf_find| apply R_kem_find| apply R_aead_find]
    | |- _ <> [] => discriminate
    | |- Z.of_nat (length _) < 32 => vm_compute; reflexivity
    | |- forall _ _ _ _, Z.of_nat (cells_size _) = _ => intros; reflexivity
    | |- forall id, _ <= f_line _ id < _ => intros id; cbn [f_line KEM_finder KDF_finder AEAD_finder]; try (destruct (id =? 0)); lia
    | |- _ < f_reason _ < _ => cbn [f_reason KEM_finder KDF_finder AEAD_finder]; unfold PROV_R_INVALID_CURVE, PROV_R_INVALID_KDF, PROV_R_INVALID_AEAD; lia
    | |- _ mod _ = _ => reflexivity
    | |- f_frame _ = _ => reflexivity
    | |- _ => try (unfold KDF_RA1, KDF_RA2, KDF_RA3, KEM_RA1, KEM_RA2, KEM_RA3, AEAD_RA1, AEAD_RA2, AEAD_RA3, A_str_kdf_find, A_str_kem_find, A_str_aead_find; lia)
    end.
  Lemma hfind_fail_kdf : hfind_fail_stmt H KDF_finder.
  Proof using HX EGS.
    eapply (hfind_fail_gen KDF_finder 16 KDF_RA1 KDF_RA2 KDF_RA3 A_str_kdf_find S_kdf_find K_kdf_find (fun _ ra s0 _ => [C8 s0; C8 ra]) (fun _ s1 s1i => s1i = s1));
      [gen_side ..| exact kdf_segA| exact kdf_glue1| exact kdf_glue2| intros id; exact kdf_segC].
  Qed.
  Lemma hfind_fail_aead : hfind_fail_stmt H AEAD_finder.
  Proof using HX EGS.
    eapply (hfind_fail_gen AEAD_finder 16 AEAD_RA1 AEAD_RA2 AEAD_RA3 A_str_aead_find S_aead_find K_aead_find (fun _ ra s0 _ => [C8 s0; C8 ra]) (fun _ s1 s1i => s1i = s1));
      [gen_side ..| exact aead_segA| exact aead_glue1| exact aead_glue2| intros id; exact aead_segC].
  Qed.
  Lemma hfind_fail_kem : hfind_fail_stmt H KEM_finder.
  Proof using HX EGS.
    eapply (hfind_fail_gen KEM_finder 32 KEM_RA1 KEM_RA2 KEM_RA3 A_str_kem_find S_kem_find K_kem_find (fun jk ra s0 s1 => [CB 8 jk; C8 s1; C8 s0; C8 ra])
              (fun id _ s1i => s1i = Z_to_bv 64 (f_line KEM_finder id)));
      [gen_side ..| exact kem_segA| exact kem_glue1| exact kem_glue2| exact kem_segC].
  Qed.
End W.
