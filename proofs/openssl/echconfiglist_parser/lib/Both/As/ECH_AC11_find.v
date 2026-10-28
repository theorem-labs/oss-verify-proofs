(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C2 ECH_AStmt_C4 ECH_AStmt_C11 ECH_AKit ECH_AsKit.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.

  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit by lia; lia.
  (* [comment removed for export] *)
  Local Ltac br_not := step; let K0 := fresh "K0" in if_cases K0; zify_cond K0; [kill K0|]; clear K0.
  Local Ltac br_yes := step; let K0 := fresh "K0" in if_cases K0; zify_cond K0; [|kill K0]; clear K0.

  Lemma id_rows_transport : forall W m m' ids a stride,
    id_rows m a stride ids -> munch W m m' -> wmono asegs m m' ->
    (forall k, (k < length ids)%nat -> disjoint_from W (a + stride * Z.of_nat k) 2) -> 0 <= stride ->
    id_rows m' a stride ids.
  Proof.
    intros W m m' ids. induction ids as [|x ids IH]; intros a stride R MU WM D HS; cbn in *; [exact I|].
    destruct R as [R1 R2]. split.
    - eapply rw_cells_transport; [exact R1| exact MU| exact WM|]. specialize (D 0%nat ltac:(lia)). cbn in D. rewrite Z.mul_0_r, Z.add_0_r in D. exact D.
    - eapply IH; [exact R2| exact MU| exact WM| | exact HS]. intros k Hk. specialize (D (S k) ltac:(lia)).
      replace (a + stride + stride * Z.of_nat k) with (a + stride * Z.of_nat (S k)) by lia. exact D.
  Qed.
  Definition HPKE_TAB_LO : Z := A_hpke_kem_tab.
  Definition HPKE_TAB_HI : Z := A_hpke_aead_tab + 160.
  Lemma HPKE_tabs_transport : forall W m m',
    munch W m m' -> wmono asegs m m' -> disjoint_from W HPKE_TAB_LO (HPKE_TAB_HI - HPKE_TAB_LO) -> HPKE_tabs m -> HPKE_tabs m'.
  Proof.
    intros W m m' MU WM D (TK & TD & TA). unfold HPKE_TAB_LO, HPKE_TAB_HI in D.
    split; [| split]; (eapply id_rows_transport; [eassumption| exact MU| exact WM| | ]); intros;
      unfold HPKE_KEM_ROW, HPKE_KDF_ROW, HPKE_AEAD_ROW, HPKE_KEM_IDS, HPKE_KDF_IDS, HPKE_AEAD_IDS, A_hpke_kem_tab, A_hpke_kdf_tab, A_hpke_aead_tab in *;
      cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul Pos.add] in *; try lia;
      (eapply disjoint_from_sub; [exact D | lia | lia | lia]).
  Qed.

  (* [comment removed for export] *)
  Lemma kem_tab_acc : forall m, ACONST m -> accessible m 0x5ad7e0 360.
  Proof.
    intros m AC. assert (IN : In (0x5ad7e0, 360, 360) aglobals) by (unfold aglobals; cbn; tauto).
    pose proof (ACONST_global_addressable m 0x5ad7e0 360 360 AC IN ltac:(lia)) as AD.
    eapply addressable_accessible; [exact AD| lia| lia| unfold AAPP_HI; lia].
  Qed.
  Lemma kdf_tab_acc : forall m, ACONST m -> accessible m 0x5ad9a0 72.
  Proof.
    intros m AC. assert (IN : In (0x5ad9a0, 72, 72) aglobals) by (unfold aglobals; cbn; tauto).
    pose proof (ACONST_global_addressable m 0x5ad9a0 72 72 AC IN ltac:(lia)) as AD.
    eapply addressable_accessible; [exact AD| lia| lia| unfold AAPP_HI; lia].
  Qed.
  Lemma aead_tab_acc : forall m, ACONST m -> accessible m 0x5ada20 160.
  Proof.
    intros m AC. assert (IN : In (0x5ada20, 160, 160) aglobals) by (unfold aglobals; cbn; tauto).
    pose proof (ACONST_global_addressable m 0x5ada20 160 160 AC IN ltac:(lia)) as AD.
    eapply addressable_accessible; [exact AD| lia| lia| unfold AAPP_HI; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma ACONST_stack_frame : forall m m' lo hi, ACONST m -> munch [(lo, hi)] m m' -> wmono asegs m m' -> aceil <= lo -> ACONST m'.
  Proof.
    intros m m' lo hi AC MU WM CE. eapply ACONST_frame; [exact AC| exact MU| exact WM|].
    constructor; [| constructor]. apply aconst_ok_high; cbn [fst snd]; acb; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia.
  Qed.

  Local Ltac fix_rows R1 R2 R3 R4 :=
    try match type of R1 with rw_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in R1 end;
    try match type of R2 with rw_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in R2 end;
    try match type of R3 with rw_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in R3 end;
    try match type of R4 with rw_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in R4 end.

  (* [comment removed for export] *)
  Local Ltac found_post FR ST MU WM TB0 AC CEIL spv :=
    release_frame FR ST (bv_unsigned spv); unfold hfind_post; finish;
    first [ eapply ACONST_stack_frame; [exact AC| exact MU| exact WM| exact CEIL]
          | eapply HPKE_tabs_transport; [exact MU | exact WM | | exact TB0]; unfold HPKE_TAB_LO, HPKE_TAB_HI, A_hpke_kem_tab, A_hpke_aead_tab; cbn; lia ].

  Lemma ahfind_found_kem : hfind_found_stmt KEM_finder.
  Proof.
    unfold hfind_found_stmt. cbn [f_ids f_tab f_stride f_frame f_entry KEM_finder].
    intros until i. intros A0 IDR FI TB AC ST CEIL LO MI RAE. subst a0.
    unfold P_ossl_HPKE_KEM_INFO_find_id, FR_ossl_HPKE_KEM_INFO_find_id, A_hpke_kem_tab, HPKE_KEM_ROW in *. acb.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (ACONST_shbase m AC) as [GSB SHB]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB. rewrite ASHADOW_BASE_val in SHB.
    pose proof TB as TB0. unfold HPKE_tabs in TB. destruct TB as (TK & _ & _).
    unfold A_hpke_kem_tab, HPKE_KEM_ROW, HPKE_KEM_IDS in TK. cbn [id_rows] in TK.
    destruct TK as (R0 & R1 & R2 & R3 & R4 & _). unfold wz in R0, R1, R2, R3, R4. fix_rows R1 R2 R3 R4.
    cbn [find_id HPKE_KEM_IDS] in FI.
    carve_frame 32%nat ST.
    (* [comment removed for export] *)
    do 5 step. step. if_cases K0; zify_cond K0.
    { exfalso. destruct (Z.eqb_spec 16 id); [lia|]. cbn [option_map] in FI. destruct (Z.eqb_spec 17 id); [lia|]. cbn [option_map] in FI.
      destruct (Z.eqb_spec 18 id); [lia|]. cbn [option_map] in FI. destruct (Z.eqb_spec 32 id); [lia|]. cbn [option_map] in FI.
      destruct (Z.eqb_spec 33 id); [lia|]. cbn in FI. discriminate FI. }
    clear K0.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACC : accessible mx 0x5ad7e0 360) by (apply kem_tab_acc; eapply ACONST_stack_frame; [exact AC| exact MU| exact WM| exact CEIL]) end.
    (* [comment removed for export] *)
    step. step. step. step. zstep. zstep. zstep. step. step.
    (* [comment removed for export] *)
    ck8_check_lit ACC 0x5ad7e0. st1. destruct (Z.eqb_spec 16 id) as [E1|E1].
    { subst id. cbn in FI. injection FI as <-. step. try if_true. do 6 step. found_post FR ST MU WM TB0 AC CEIL sp. }
    cbn [option_map] in FI. br_not. zstep. zstep. zstep. zstep. br_yes.
    (* [comment removed for export] *)
    ck8_check_lit ACC (0x5ad7e0 + 72). st1. destruct (Z.eqb_spec 17 id) as [E2|E2].
    { subst id. cbn in FI. injection FI as <-. step. try if_true. do 6 step. found_post FR ST MU WM TB0 AC CEIL sp. }
    cbn [option_map] in FI. br_not. zstep. zstep. zstep. zstep. br_yes.
    (* [comment removed for export] *)
    ck8_check_lit ACC (0x5ad7e0 + 144). st1. destruct (Z.eqb_spec 18 id) as [E3|E3].
    { subst id. cbn in FI. injection FI as <-. step. try if_true. do 6 step. found_post FR ST MU WM TB0 AC CEIL sp. }
    cbn [option_map] in FI. br_not. zstep. zstep. zstep. zstep. br_yes.
    (* [comment removed for export] *)
    ck8_check_lit ACC (0x5ad7e0 + 216). st1. destruct (Z.eqb_spec 32 id) as [E4|E4].
    { subst id. cbn in FI. injection FI as <-. step. try if_true. do 6 step. found_post FR ST MU WM TB0 AC CEIL sp. }
    cbn [option_map] in FI. br_not. zstep. zstep. zstep. zstep. br_yes.
    (* [comment removed for export] *)
    ck8_check_lit ACC (0x5ad7e0 + 288). st1. destruct (Z.eqb_spec 33 id) as [E5|E5]; [| cbn in FI; discriminate FI].
    subst id. cbn in FI. injection FI as <-. step. try if_true. do 6 step. found_post FR ST MU WM TB0 AC CEIL sp.
  Qed.

  Lemma ahfind_found_kdf : hfind_found_stmt KDF_finder.
  Proof.
    unfold hfind_found_stmt. cbn [f_ids f_tab f_stride f_frame f_entry KDF_finder].
    intros until i. intros A0 IDR FI TB AC ST CEIL LO MI RAE. subst a0.
    unfold P_ossl_HPKE_KDF_INFO_find_id, FR_ossl_HPKE_KDF_INFO_find_id, A_hpke_kdf_tab, HPKE_KDF_ROW in *. acb.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (ACONST_shbase m AC) as [GSB SHB]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB. rewrite ASHADOW_BASE_val in SHB.
    pose proof TB as TB0. unfold HPKE_tabs in TB. destruct TB as (_ & TD & _).
    unfold A_hpke_kdf_tab, HPKE_KDF_ROW, HPKE_KDF_IDS in TD. cbn [id_rows] in TD.
    destruct TD as (R0 & R1 & R2 & _). unfold wz in R0, R1, R2. fix_rows R1 R2 R2 R2.
    cbn [find_id HPKE_KDF_IDS] in FI.
    carve_frame 16%nat ST.
    (* [comment removed for export] *)
    do 4 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACC : accessible mx 0x5ad9a0 72) by (apply kdf_tab_acc; eapply ACONST_stack_frame; [exact AC| exact MU| exact WM| exact CEIL]) end.
    (* [comment removed for export] *)
    step. step. step. step. zstep. zstep. zstep. step. step.
    (* [comment removed for export] *)
    ck8_check_lit ACC 0x5ad9a0. st1. destruct (Z.eqb_spec 1 id) as [E1|E1].
    { subst id. cbn in FI. injection FI as <-. step. try if_true. do 5 step. found_post FR ST MU WM TB0 AC CEIL sp. }
    cbn [option_map] in FI. br_not. zstep. zstep. zstep. zstep. br_not. step.
    (* [comment removed for export] *)
    ck8_check_lit ACC (0x5ad9a0 + 24). st1. destruct (Z.eqb_spec 2 id) as [E2|E2].
    { subst id. cbn in FI. injection FI as <-. step. try if_true. do 5 step. found_post FR ST MU WM TB0 AC CEIL sp. }
    cbn [option_map] in FI. br_not. zstep. zstep. zstep. zstep. br_not. step.
    (* [comment removed for export] *)
    ck8_check_lit ACC (0x5ad9a0 + 48). st1. destruct (Z.eqb_spec 3 id) as [E3|E3]; [| cbn in FI; discriminate FI].
    subst id. cbn in FI. injection FI as <-. step. try if_true. do 5 step. found_post FR ST MU WM TB0 AC CEIL sp.
  Qed.

  Lemma ahfind_found_aead : hfind_found_stmt AEAD_finder.
  Proof.
    unfold hfind_found_stmt. cbn [f_ids f_tab f_stride f_frame f_entry AEAD_finder].
    intros until i. intros A0 IDR FI TB AC ST CEIL LO MI RAE. subst a0.
    unfold P_ossl_HPKE_AEAD_INFO_find_id, FR_ossl_HPKE_AEAD_INFO_find_id, A_hpke_aead_tab, HPKE_AEAD_ROW in *. acb.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (ACONST_shbase m AC) as [GSB SHB]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB. rewrite ASHADOW_BASE_val in SHB.
    pose proof TB as TB0. unfold HPKE_tabs in TB. destruct TB as (_ & _ & TA).
    unfold A_hpke_aead_tab, HPKE_AEAD_ROW, HPKE_AEAD_IDS in TA. cbn [id_rows] in TA.
    destruct TA as (R0 & R1 & R2 & R3 & _). unfold wz in R0, R1, R2, R3. fix_rows R1 R2 R3 R3.
    cbn [find_id HPKE_AEAD_IDS] in FI.
    carve_frame 16%nat ST.
    do 4 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACC : accessible mx 0x5ada20 160) by (apply aead_tab_acc; eapply ACONST_stack_frame; [exact AC| exact MU| exact WM| exact CEIL]) end.
    step. step. step. step. zstep. zstep. zstep. step. step.
    (* [comment removed for export] *)
    ck8_check_lit ACC 0x5ada20. st1. destruct (Z.eqb_spec 1 id) as [E1|E1].
    { subst id. cbn in FI. injection FI as <-. step. try if_true. do 5 step. found_post FR ST MU WM TB0 AC CEIL sp. }
    cbn [option_map] in FI. br_not. zstep. zstep. zstep. zstep. br_not. step.
    (* [comment removed for export] *)
    ck8_check_lit ACC (0x5ada20 + 40). st1. destruct (Z.eqb_spec 2 id) as [E2|E2].
    { subst id. cbn in FI. injection FI as <-. step. try if_true. do 5 step. found_post FR ST MU WM TB0 AC CEIL sp. }
    cbn [option_map] in FI. br_not. zstep. zstep. zstep. zstep. br_not. step.
    (* [comment removed for export] *)
    ck8_check_lit ACC (0x5ada20 + 80). st1. destruct (Z.eqb_spec 3 id) as [E3|E3].
    { subst id. cbn in FI. injection FI as <-. step. try if_true. do 5 step. found_post FR ST MU WM TB0 AC CEIL sp. }
    cbn [option_map] in FI. br_not. zstep. zstep. zstep. zstep. br_not. step.
    (* [comment removed for export] *)
    ck8_check_lit ACC (0x5ada20 + 120). st1. destruct (Z.eqb_spec 65535 id) as [E4|E4]; [| cbn in FI; discriminate FI].
    subst id. cbn in FI. injection FI as <-. step. try if_true. do 5 step. found_post FR ST MU WM TB0 AC CEIL sp.
  Qed.
  Lemma find_id_lt : forall ids id i, find_id ids id = Some i -> (i < length ids)%nat.
  Proof.
    induction ids as [|x ids IH]; intros id i Hf; cbn in Hf; [discriminate|].
    destruct (x =? id); [injection Hf as <-; cbn; lia|].
    destruct (find_id ids id) as [j|] eqn:E; [|discriminate]. cbn in Hf. injection Hf as <-.
    specialize (IH _ _ E). cbn. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma suite_mask48 : forall kem kdf aead hi, 0 <= kem < 2^16 -> 0 <= kdf < 2^16 -> 0 <= aead < 2^16 -> 0 <= hi < 2^16 ->
    Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (kem + kdf * 2 ^ 16 + aead * 2 ^ 32 + hi * 2 ^ 48))) 16))) 16
    = kem + kdf * 2 ^ 16 + aead * 2 ^ 32.
  Proof.
    intros kem kdf aead hi K D A Hh.
    rewrite (unsigned_lit (kem + kdf * 2 ^ 16 + aead * 2 ^ 32 + hi * 2 ^ 48)) by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite unsigned_lit_wrap.
    rewrite Z.shiftr_div_pow2 by lia.
    replace ((kem + kdf * 2 ^ 16 + aead * 2 ^ 32 + hi * 2 ^ 48) * 2 ^ 16) with ((kem * 2^16 + kdf * 2 ^ 32 + aead * 2 ^ 48) + hi * 2 ^ 64) by lia.
    rewrite Z_mod_plus_full. rewrite Z.mod_small by lia.
    symmetry. apply Z.div_unique with (r := 0); lia.
  Qed.
  Lemma suite_kem : forall kem kdf aead, 0 <= kem < 2^16 -> 0 <= kdf < 2^16 -> 0 <= aead < 2^16 ->
    Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (kem + kdf * 2 ^ 16 + aead * 2 ^ 32))) 48))) 48 = kem.
  Proof.
    intros kem kdf aead K D A.
    rewrite (unsigned_lit (kem + kdf * 2 ^ 16 + aead * 2 ^ 32)) by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite unsigned_lit_wrap.
    rewrite Z.shiftr_div_pow2 by lia.
    replace ((kem + kdf * 2 ^ 16 + aead * 2 ^ 32) * 2 ^ 48) with (kem * 2^48 + (kdf + aead * 2 ^ 16) * 2 ^ 64) by lia.
    rewrite Z_mod_plus_full. rewrite Z.mod_small by lia.
    symmetry. apply Z.div_unique with (r := 0); lia.
  Qed.
  Lemma suite_kdf : forall kem kdf aead, 0 <= kem < 2^16 -> 0 <= kdf < 2^16 -> 0 <= aead < 2^16 ->
    bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (Z_to_bv 64 (kem + kdf * 2 ^ 16 + aead * 2 ^ 32)))) 16) = kdf.
  Proof.
    intros kem kdf aead K D A. rewrite unsigned_lit by lia.
    unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
    replace (kem + kdf * 2 ^ 16 + aead * 2 ^ 32) with ((kem + kdf * 2 ^ 16) + aead * 2 ^ 32) by lia.
    rewrite Z_mod_plus_full. rewrite (Z.mod_small (kem + kdf * 2 ^ 16)) by lia. rewrite Z.shiftr_div_pow2 by lia.
    replace ((kem + kdf * 2 ^ 16) / 2 ^ 16) with kdf by (apply Z.div_unique with (r := kem); lia).
    rewrite Z.mod_small by lia. lia.
  Qed.
  Lemma suite_aead : forall kem kdf aead, 0 <= kem < 2^16 -> 0 <= kdf < 2^16 -> 0 <= aead < 2^16 ->
    Z.shiftr (bv_unsigned (Z_to_bv 64 (kem + kdf * 2 ^ 16 + aead * 2 ^ 32))) 32 = aead.
  Proof.
    intros kem kdf aead K D A. rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia.
    symmetry. apply Z.div_unique with (r := kem + kdf * 2^16); lia.
  Qed.


  Lemma asuiteok_spec : suiteok_stmt.
  Proof.
    unfold suiteok_stmt. intros until lo. intros A0 KR DR AR HR SF TB AC ST CEIL LO MI RAE. subst a0.
    unfold P_OSSL_HPKE_suite_check, SUITECHECK_OK_STACK, FR_OSSL_HPKE_suite_check, FR_hpke_suite_check, FR_ossl_HPKE_KEM_INFO_find_id, suite_word in *. acb.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (ACONST_shbase m AC) as [GSB SHB]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB. rewrite ASHADOW_BASE_val in SHB.
    carve_frame 16%nat ST.
    (* [comment removed for export] *)
    do 4 step. step. step. rewrite suite_mask48 by lia.
    step. step. step. step. step. step. step.
    release_frame FR ST (bv_unsigned sp).
    (* [comment removed for export] *)
    carve_frame 80%nat ST. do 11 step. step. step. step. step. step. step. step. step. step.
    rewrite suite_kem by lia. step. step.
    unfold suite_fail in SF.
    destruct (find_id HPKE_KEM_IDS kem) as [ik|] eqn:FK; [|discriminate SF].
    destruct (find_id HPKE_KDF_IDS kdf) as [idf|] eqn:FD; [|discriminate SF].
    destruct (find_id HPKE_AEAD_IDS aead) as [ia|] eqn:FA; [|discriminate SF].
    pose proof (find_id_lt _ _ _ FK) as BK. pose proof (find_id_lt _ _ _ FD) as BD. pose proof (find_id_lt _ _ _ FA) as BA. cbn [length HPKE_KEM_IDS HPKE_KDF_IDS HPKE_AEAD_IDS] in BK, BD, BA.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (TB1 : HPKE_tabs m1).
    { eapply HPKE_tabs_transport; [exact MU | exact WM | | exact TB]. unfold HPKE_TAB_LO, HPKE_TAB_HI, A_hpke_kem_tab, A_hpke_aead_tab; cbn; lia. }
    assert (AC1 : ACONST m1) by (eapply ACONST_stack_frame; [exact AC| exact MU| exact WM| exact CEIL]).
    eapply evt_cut.
    { eapply (ahfind_found_kem) with (lo := lo) (i := ik) (id := kem); try reflexivity; try eassumption; try lia.
      all: cbn [f_frame KEM_finder]; unfold FR_ossl_HPKE_KEM_INFO_find_id; rewrite ?unsigned_lit by lia; first [eassumption | lia | reflexivity]. }
    intros ms' PO. unfold hfind_post in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU' & WM' & MI' & AC' & ST' & TB').
    match goal with |- context [ret_pc (Z_to_bv 64 ?r)] => replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
    rewrite unsigned_lit in MU', ST' by lia. carry MU' WM'. extend_munch MU WM MU' WM'. clear MI TB1 ST AC1. rename MI' into MI. rename ST' into ST. rename AC' into AC1.
    cbn [f_tab f_stride KEM_finder]. unfold A_hpke_kem_tab, HPKE_KEM_ROW.
    (* [comment removed for export] *)
    br_not. step. step. rewrite suite_kdf by lia. step. step.
    eapply evt_cut.
    { eapply (ahfind_found_kdf) with (lo := lo) (i := idf) (id := kdf); try reflexivity; try eassumption; try lia.
      all: cbn [f_frame KDF_finder]; unfold FR_ossl_HPKE_KDF_INFO_find_id; rewrite ?unsigned_lit by lia; first [eassumption | lia | reflexivity]. }
    intros ms' PO. unfold hfind_post in PO.
    destruct PO as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m'' & -> & MU' & WM' & MI' & AC' & ST' & TB'').
    match goal with |- context [ret_pc (Z_to_bv 64 ?r)] => replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
    rewrite unsigned_lit in MU', ST' by lia. carry MU' WM'. extend_munch MU WM MU' WM'. clear MI TB' ST AC1. rename MI' into MI. rename ST' into ST. rename AC' into AC1.
    cbn [f_tab f_stride KDF_finder]. unfold A_hpke_kdf_tab, HPKE_KDF_ROW.
    (* [comment removed for export] *)
    br_not. step. step. rewrite suite_aead by lia. step. step.
    eapply evt_cut.
    { eapply (ahfind_found_aead) with (lo := lo) (i := ia) (id := aead); try reflexivity; try eassumption; try lia.
      all: cbn [f_frame AEAD_finder]; unfold FR_ossl_HPKE_AEAD_INFO_find_id; rewrite ?unsigned_lit by lia; first [eassumption | lia | reflexivity]. }
    intros ms' PO. unfold hfind_post in PO.
    destruct PO as (t0x & t1x & t2x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & mx & -> & MU' & WM' & MI' & AC' & ST' & TBx).
    match goal with |- context [ret_pc (Z_to_bv 64 ?r)] => replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
    rewrite unsigned_lit in MU', ST' by lia. carry MU' WM'. extend_munch MU WM MU' WM'. clear MI TB'' ST AC1. rename MI' into MI. rename ST' into ST. rename AC' into AC1.
    cbn [f_tab f_stride AEAD_finder]. unfold A_hpke_aead_tab, HPKE_AEAD_ROW.
    (* [comment removed for export] *)
    br_not. step. try if_true. step. try if_true. step. step. try if_true.
    step. do 9 step. step. step.
    release_frame FR ST (bv_unsigned sp). unfold hfind_post. finish.
  Qed.
End S.
