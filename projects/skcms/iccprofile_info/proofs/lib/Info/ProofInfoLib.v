(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State.
From OSSVerify.skcms.iccprofile_info.images Require Plain.
From OSSVerify.skcms.iccprofile_info.images Require Ubsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require PropExec FuzzContract LibDefs LibWP1Spec LibWP2Spec LibCurveSpec LibFPSpec LibTagsSpec.
From Stdlib Require NArith.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require SymExecFP SymExecFPSound SymRunFP SymDriveFP SymCallFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf Require SymDriveLB.
From Stdlib Require Zify.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require SymDriveLZ.
Unset Nia Cache.  (* [comment removed for export] *)

Module LibMemsetS1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP1Spec.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf.SymDriveLB.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveLZ.
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.ev_simpl E ::= ev_simpl_lz E.
#[local] Ltac SymDriveFP.ev_simpl_in E H ::= ev_simpl_in_lz E H.
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.run_fp_with_h HR HF HK fuel stops scr chints keep extra ::= run_fp_with_h_lz HR HF HK fuel stops scr chints keep extra.
#[local] Ltac SymDriveFP.branch_case_with HR HF HK Hc ::= branch_case_with_lz HR HF HK Hc.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SXF. Import SXFS.

#[local] Abbreviation SEGS := Plain.M.loaded_segments.

Section Memset.
  Variables (n al : Z).
  Hypothesis Hn : n = 976%Z /\ al = 8%Z \/ n = 20%Z /\ al = 4%Z.

  Lemma memset_lit_ok : forall d, fn_contract SEGS 0x1dfe4 (memset_pre SEGS n al d) (memset_post n d).
  Proof.
    intros d. unfold fn_contract, memset_pre, memset_post.
    intros FPI regs mem rom ret Hra Hret (Hd & H11 & H12 & Hal & Hwr & Hnw).
    destruct Hwr as (Hw0 & Hwn & Hw64 & Hst).
    pose proof (u64_range d) as Hdr.
    apply runs_to_contract with
      (P := fun FPI' regs' mem' =>
         regs_kept abi_kept regs regs' /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI')) /\
         (frame_mod mem mem' [(d, n)] /\
          (forall i, (0 <= i < n)%Z -> mem' (Z_to_bv 64 (bv_unsigned d + i)) = Some (Z_to_bv 8 0)) /\
          getr regs' 10 = d)).
    set (E := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ [])) (blobs_ev [])).
    assert (HR0 : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [])).
    (* [comment removed for export] *)
    assert (HR : regs_ok E (sr_upd (sr_upd (sr_vars 0) 11 (ELit 0)) 12 (ELit n)) regs).
    { apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [exact HR0|]|]; cbn [edenot]; [exact H11 | exact H12]. }
    pose proof (HR0 : id _) as HRid. clear HR0. pose proof (HF : id _) as HFid.
    assert (HK : know_ok SEGS E mem [KAlign (EVar 10) al; KWr (SA (EVar 10) 0) n]).
    { constructor; [|constructor; [|constructor]].
      - apply kalign_intro; [lia|]. cbn [edenot]. ev_simpl E. rewrite Hd. exact Hal.
      - apply (kwr_intro SEGS E mem (EVar 10) d 0 n); cbn [edenot]; try lia. ev_simpl E. exact Hd.
        rewrite Z.add_0_r. exact Hst. }
    (* [comment removed for export] *)
    assert (FIN : forall (nn : nat) (FPI' : FPState) (R : bvmap 5 word) (log : list sentry) sr' sfr',
      Z.of_nat nn = n ->
      regs_ok E sr' R -> fregs_ok E sfr' (fp_regs (FPState:=FPI')) ->
      log_flat E log ->
      forallb (fun r => expr_eqb (sr_get sr' r) (sr_get (sr_vars 0) r)) abi_kept = true ->
      forallb (fun r => expr_eqb (sfr_get sfr' r) (sfr_get (sfr_vars 32) r)) abi_fkept = true ->
      sr_get sr' 10 = EVar 10 -> sr_get sr' 1 = EVar 1 ->
      log_in_regions log [(SA (EVar 10) 0, n)] = true ->
      lz_cover log (EVar 10) 0 nn = true ->
      runs_to SEGS (mkst (FP:=FPI') R (Z_to_bv 64 0x1e0d8) (mem_denot E mem log) rom)
        (fun st' => exists (FPI'0 : FPState) regs' mem',
           st' = mkst (FP:=FPI'0) regs' ret mem' rom /\
           (regs_kept abi_kept regs regs' /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI'0)) /\
            (frame_mod mem mem' [(d, n)] /\
             (forall i, (0 <= i < n)%Z -> mem' (Z_to_bv 64 (bv_unsigned d + i)) = Some (Z_to_bv 8 0)) /\
             getr regs' 10 = d)))).
    { intros nn FPI' R log sr' sfr' Hnn HR' HF' Hlf Hk Hfk H10 H1 Hreg Hcov.
      fin_ret_with HR'.
      { rewrite (HR' 1%bv), H1. cbn [edenot]. ev_simpl E. rewrite Hra. exact Hret. }
      exists FPI', R, (mem_denot E mem log). split.
      + rewrite (HR' 1%bv), H1. cbn [edenot]. ev_simpl E. rewrite Hra. reflexivity.
      + split; [exact (regs_same_on E _ _ regs R abi_kept HRid HR' Hk)|].
          split; [exact (fregs_same_on E _ _ _ _ abi_fkept HFid HF' Hfk)|].
          split; [|split].
          * replace [(d, n)] with (regions_denot E [(SA (EVar 10) 0, n)]).
            -- apply frame_mod_mem_denot; [exact Hlf | | exact Hreg].
               constructor; [|constructor]. cbn [fst snd]. unfold flat, estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite Hd. lia.
            -- cbn [regions_denot map fst snd]. unfold adenot. cbn [a_base a_off edenot]. ev_simpl E. rewrite Hd, v_addi_0. reflexivity.
          * intros i Hi. rewrite <- Hd.
            change (getr regs 10) with (edenot E (EVar 10)).
            apply (mem_denot_lz_cover E mem log (EVar 10) 0 nn Hlf Hcov); cbn [edenot]; ev_simpl E; rewrite ?Hd; lia.
          * rewrite (HR' 10%bv), H10. cbn [edenot]. ev_simpl E. exact Hd. }
    destruct Hn as [[-> ->] | [-> ->]].
    - run_fp 400%nat (@nil Z) noscr true. subst M.
      eapply (FIN 976%nat); [reflexivity | exact HR | exact HF | exact HLF | vm_compute; reflexivity .. ].
    - run_fp 400%nat (@nil Z) noscr true. subst M.
      eapply (FIN 20%nat); [reflexivity | exact HR | exact HF | exact HLF | vm_compute; reflexivity .. ].
  Qed.
End Memset.

Theorem memset976_src1 : memset976_contract SEGS wp1_src1.
Proof. intros d. exact (memset_lit_ok 976 8 (or_introl (conj eq_refl eq_refl)) d). Qed.

Theorem memset20_src1 : memset20_contract SEGS wp1_src1.
Proof. intros d. exact (memset_lit_ok 20 4 (or_intror (conj eq_refl eq_refl)) d). Qed.
End LibMemsetS1.

Module LibMemsetUb.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP1Spec.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf.SymDriveLB.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveLZ.
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.ev_simpl E ::= ev_simpl_lz E.
#[local] Ltac SymDriveFP.ev_simpl_in E H ::= ev_simpl_in_lz E H.
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.run_fp_with_h HR HF HK fuel stops scr chints keep extra ::= run_fp_with_h_lz HR HF HK fuel stops scr chints keep extra.
#[local] Ltac SymDriveFP.branch_case_with HR HF HK Hc ::= branch_case_with_lz HR HF HK Hc.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SXF. Import SXFS.

#[local] Abbreviation SEGS := Ubsan.M.loaded_segments.

Section Memset.
  Variables (n al : Z).
  Hypothesis Hn : n = 976%Z /\ al = 8%Z \/ n = 20%Z /\ al = 4%Z.

  Lemma memset_lit_ok : forall d, fn_contract SEGS 0x1eae0 (memset_pre SEGS n al d) (memset_post n d).
  Proof.
    intros d. unfold fn_contract, memset_pre, memset_post.
    intros FPI regs mem rom ret Hra Hret (Hd & H11 & H12 & Hal & Hwr & Hnw).
    destruct Hwr as (Hw0 & Hwn & Hw64 & Hst).
    pose proof (u64_range d) as Hdr.
    apply runs_to_contract with
      (P := fun FPI' regs' mem' =>
         regs_kept abi_kept regs regs' /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI')) /\
         (frame_mod mem mem' [(d, n)] /\
          (forall i, (0 <= i < n)%Z -> mem' (Z_to_bv 64 (bv_unsigned d + i)) = Some (Z_to_bv 8 0)) /\
          getr regs' 10 = d)).
    set (E := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ [])) (blobs_ev [])).
    assert (HR0 : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [])).
    (* [comment removed for export] *)
    assert (HR : regs_ok E (sr_upd (sr_upd (sr_vars 0) 11 (ELit 0)) 12 (ELit n)) regs).
    { apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [exact HR0|]|]; cbn [edenot]; [exact H11 | exact H12]. }
    pose proof (HR0 : id _) as HRid. clear HR0. pose proof (HF : id _) as HFid.
    assert (HK : know_ok SEGS E mem [KAlign (EVar 10) al; KWr (SA (EVar 10) 0) n]).
    { constructor; [|constructor; [|constructor]].
      - apply kalign_intro; [lia|]. cbn [edenot]. ev_simpl E. rewrite Hd. exact Hal.
      - apply (kwr_intro SEGS E mem (EVar 10) d 0 n); cbn [edenot]; try lia. ev_simpl E. exact Hd.
        rewrite Z.add_0_r. exact Hst. }
    (* [comment removed for export] *)
    assert (FIN : forall (nn : nat) (FPI' : FPState) (R : bvmap 5 word) (log : list sentry) sr' sfr',
      Z.of_nat nn = n ->
      regs_ok E sr' R -> fregs_ok E sfr' (fp_regs (FPState:=FPI')) ->
      log_flat E log ->
      forallb (fun r => expr_eqb (sr_get sr' r) (sr_get (sr_vars 0) r)) abi_kept = true ->
      forallb (fun r => expr_eqb (sfr_get sfr' r) (sfr_get (sfr_vars 32) r)) abi_fkept = true ->
      sr_get sr' 10 = EVar 10 -> sr_get sr' 1 = EVar 1 ->
      log_in_regions log [(SA (EVar 10) 0, n)] = true ->
      lz_cover log (EVar 10) 0 nn = true ->
      runs_to SEGS (mkst (FP:=FPI') R (Z_to_bv 64 0x1ebd4) (mem_denot E mem log) rom)
        (fun st' => exists (FPI'0 : FPState) regs' mem',
           st' = mkst (FP:=FPI'0) regs' ret mem' rom /\
           (regs_kept abi_kept regs regs' /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI'0)) /\
            (frame_mod mem mem' [(d, n)] /\
             (forall i, (0 <= i < n)%Z -> mem' (Z_to_bv 64 (bv_unsigned d + i)) = Some (Z_to_bv 8 0)) /\
             getr regs' 10 = d)))).
    { intros nn FPI' R log sr' sfr' Hnn HR' HF' Hlf Hk Hfk H10 H1 Hreg Hcov.
      fin_ret_with HR'.
      { rewrite (HR' 1%bv), H1. cbn [edenot]. ev_simpl E. rewrite Hra. exact Hret. }
      exists FPI', R, (mem_denot E mem log). split.
      + rewrite (HR' 1%bv), H1. cbn [edenot]. ev_simpl E. rewrite Hra. reflexivity.
      + split; [exact (regs_same_on E _ _ regs R abi_kept HRid HR' Hk)|].
          split; [exact (fregs_same_on E _ _ _ _ abi_fkept HFid HF' Hfk)|].
          split; [|split].
          * replace [(d, n)] with (regions_denot E [(SA (EVar 10) 0, n)]).
            -- apply frame_mod_mem_denot; [exact Hlf | | exact Hreg].
               constructor; [|constructor]. cbn [fst snd]. unfold flat, estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite Hd. lia.
            -- cbn [regions_denot map fst snd]. unfold adenot. cbn [a_base a_off edenot]. ev_simpl E. rewrite Hd, v_addi_0. reflexivity.
          * intros i Hi. rewrite <- Hd.
            change (getr regs 10) with (edenot E (EVar 10)).
            apply (mem_denot_lz_cover E mem log (EVar 10) 0 nn Hlf Hcov); cbn [edenot]; ev_simpl E; rewrite ?Hd; lia.
          * rewrite (HR' 10%bv), H10. cbn [edenot]. ev_simpl E. exact Hd. }
    destruct Hn as [[-> ->] | [-> ->]].
    - run_fp 400%nat (@nil Z) noscr true. subst M.
      eapply (FIN 976%nat); [reflexivity | exact HR | exact HF | exact HLF | vm_compute; reflexivity .. ].
    - run_fp 400%nat (@nil Z) noscr true. subst M.
      eapply (FIN 20%nat); [reflexivity | exact HR | exact HF | exact HLF | vm_compute; reflexivity .. ].
  Qed.
End Memset.

Theorem memset976_infoub : memset976_contract SEGS wp1_infoub.
Proof. intros d. exact (memset_lit_ok 976 8 (or_introl (conj eq_refl eq_refl)) d). Qed.

Theorem memset20_infoub : memset20_contract SEGS wp1_infoub.
Proof. intros d. exact (memset_lit_ok 20 4 (or_intror (conj eq_refl eq_refl)) d). Qed.
End LibMemsetUb.

Module LibRteS1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP1Spec.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveLZ.
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.ev_simpl E ::= ev_simpl_lz E.
#[local] Ltac SymDriveFP.ev_simpl_in E H ::= ev_simpl_in_lz E H.
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.run_fp_with_h HR HF HK fuel stops scr chints keep extra ::= run_fp_with_h_lz HR HF HK fuel stops scr chints keep extra.
#[local] Ltac SymDriveFP.branch_case_with HR HF HK Hc ::= branch_case_with_lz HR HF HK Hc.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SXF. Import SXFS.

#[local] Abbreviation SEGS := Plain.M.loaded_segments.

Section RTE.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret c data t8 t16 : word) (n len : Z) (bs : list byte).

  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hc : getr regs 10 = c.
  Hypothesis Hn   : rdn SEGS mem (Z_to_bv 64 (bv_unsigned c + 0)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 n)).
  Hypothesis Ht8  : rdn SEGS mem (Z_to_bv 64 (bv_unsigned c + 8)) 8 = Some (word_to_le_bytes 8 t8).
  Hypothesis Ht16 : rdn SEGS mem (Z_to_bv 64 (bv_unsigned c + 16)) 8 = Some (word_to_le_bytes 8 t16).
  Hypothesis Hc24 : (bv_unsigned c + 24 <= 2 ^ 64)%Z.
  Hypothesis Hlen : (0 <= len < 2 ^ 26)%Z.
  Hypothesis Hbs : Z.of_nat (length bs) = len.
  Hypothesis Hdata : (bv_unsigned data + len < 2 ^ 64)%Z.
  Hypothesis Hblob : forall i, (0 <= i < len)%Z ->
      mem (Z_to_bv 64 (bv_unsigned data + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0)).
  Hypothesis Hcurve : n = 0%Z \/
     ((2 <= n <= 2 ^ 24)%Z
      /\ (bv_unsigned t8 <> 0%Z -> bv_unsigned data <= bv_unsigned t8 /\ bv_unsigned t8 + n <= bv_unsigned data + len)%Z
      /\ (bv_unsigned t16 <> 0%Z -> bv_unsigned data <= bv_unsigned t16 /\ bv_unsigned t16 + 2 * n <= bv_unsigned data + len)%Z).

  Let E : env := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI))
                                ++ [Z_to_bv 64 n; t8; t16; data; Z_to_bv 64 len])) (blobs_ev [bs]).

  Definition kn0 : list kentry :=
    [KWord (SA (EVar 10) 0) 4 (EVar 64); KWord (SA (EVar 10) 8) 8 (EVar 65); KWord (SA (EVar 10) 16) 8 (EVar 66);
     KBlobD (SA (EVar 67) 0) (EVar 68) 0].

  Lemma kn0_ok : know_ok SEGS E mem kn0.
  Proof.
    unfold kn0. pose proof (u64_range c). pose proof (u64_range data).
    constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    - eapply (kword_intro SEGS E mem (EVar 10) c 0 4 (EVar 64) (Z_to_bv 64 n)); cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (EVar 10) c 8 8 (EVar 65) t8); cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (EVar 10) c 16 8 (EVar 66) t16); cbn; try lia; auto.
    - cbn [kentry_ok]. unfold flat, estart, elenZ. cbn. rewrite u_small by lia.
      split; [lia|]. split; [exact Hbs|]. intros i Hi. rewrite Z.add_0_r. apply Hblob. exact Hi.
  Qed.

  Ltac post :=
    lazymatch goal with
    | |- exists FPI' regs' mem', @mkst ?FPI ?R _ ?M _ = _ /\ _ =>
      lazymatch goal with
      | HR : regs_ok ?E _ R, HF : fregs_ok _ _ (@fp_regs FPI), HR0 : id (regs_ok _ ?sr0 ?regs), HF0 : id (fregs_ok _ ?sfr0 ?fr) |- _ =>
        exists FPI, R, M; split; [| split; [|split; [|reflexivity]]]; unfold regs_kept, fregs_kept;
        [ regv HR (1%bv:reg); rewrite_getr; reflexivity
        | eapply (regs_same_on E sr0 _ regs R abi_kept); [ exact HR0 | exact HR | vm_compute; reflexivity ]
        | eapply (fregs_same_on E sfr0 _ fr _ abi_fkept); [ exact HF0 | exact HF | vm_compute; reflexivity ] ]
      end
    end.

  Theorem rte_run_ok :
    exists (FPI' : FPState) regs' mem',
      msteps SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x130cc) mem rom)
                  (mkst (FP:=FPI') regs' ret mem' rom)
      /\ regs_kept abi_kept regs regs'
      /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI'))
      /\ mem' = mem.
  Proof.
    apply runs_to_contract with
      (P := fun FPI' regs' mem' => regs_kept abi_kept regs regs'
              /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI')) /\ mem' = mem).
    assert (HR : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [bs])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [bs])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    pose proof (u64_range t8). pose proof (u64_range t16). pose proof (u64_range data).
    destruct Hcurve as [Hn0 | (Hnr & H8 & H16)].
    - (* [comment removed for export] *)
      assert (HK : know_ok SEGS E mem (KRange (EVar 64) 0 0 :: kn0)).
      { constructor; [apply krange_intro; cbn; subst n; rewrite u_small by lia; lia | apply kn0_ok]. }
      run_fp 100%nat (@nil Z) noscr false. fin_ret. post.
    - (* [comment removed for export] *)
      assert (K64 : kentry_ok SEGS E mem (KRange (EVar 64) 2 (2^24))).
      { apply krange_intro; cbn; rewrite u_small by lia; lia. }
      assert (Kcase : forall (i : nat) (t : word) (z : {bv_unsigned t = 0%Z} + {bv_unsigned t <> 0%Z}),
                edenot E (EVar i) = t ->
                kentry_ok SEGS E mem (if z then KRange (EVar i) 0 0 else KRange (EVar i) 1 (2^64 - 1))).
      { intros i t z Hi. pose proof (u64_range t). destruct z; apply krange_intro; rewrite Hi; lia. }
      pose proof (Kcase 65%nat t8 (Z.eq_dec (bv_unsigned t8) 0) eq_refl) as K65.
      pose proof (Kcase 66%nat t16 (Z.eq_dec (bv_unsigned t16) 0) eq_refl) as K66.
      assert (HK : know_ok SEGS E mem
               (KRange (EVar 64) 2 (2^24)
                :: (if Z.eq_dec (bv_unsigned t8) 0 then KRange (EVar 65) 0 0 else KRange (EVar 65) 1 (2^64 - 1))
                :: (if Z.eq_dec (bv_unsigned t16) 0 then KRange (EVar 66) 0 0 else KRange (EVar 66) 1 (2^64 - 1))
                :: kn0)).
      { constructor; [exact K64|]. constructor; [exact K65|]. constructor; [exact K66|]. apply kn0_ok. }
      clear K64 K65 K66 Kcase.
      destruct (Z.eq_dec (bv_unsigned t8) 0) as [Ht8z | Ht8nz];
        [| specialize (H8 Ht8nz)];
      destruct (Z.eq_dec (bv_unsigned t16) 0) as [Ht16z | Ht16nz];
        try specialize (H16 Ht16nz);
      run_fp 100%nat (@nil Z) noscr false; fin_ret; post.
  Qed.
End RTE.

Theorem rte_S1_ok : rte_contract SEGS 0x130cc.
Proof.
  intros data len bs c FPI regs mem rom ret Hra Hret PRE.
  destruct PRE as (Hc & (Hlen & Hbs & Hdnz & Hdata & Hblob) & Hcurve & Hal & Hc32).
  destruct Hcurve as (n & t8 & t16 & [Hn32 Hn] & H8c & H16c & Hcv).
  unfold cell64, cell in H8c, H16c. unfold cell in Hn.
  destruct (rte_run_ok FPI regs mem rom ret c data t8 t16 n len bs Hra Hret Hc
              ltac:(rewrite Z.add_0_r; exact Hn) H8c H16c ltac:(lia) Hlen Hbs ltac:(lia) Hblob
              ltac:(destruct Hcv as [Hz | (Hr & Hnz & H8 & H16)]; [left; exact Hz | right];
                    split; [exact Hr|]; split;
                    [ intros Hz; destruct (H8 Hz) as (A & _ & B); split; [exact A|exact B]
                    | intros Hz; destruct (H16 Hz) as (A & _ & B); split; [exact A|exact B] ]))
    as (FPI' & regs' & mem' & Hms & Hk1 & Hk2 & Hmem).
  exists FPI', regs', mem'. unfold rte_post. auto.
Qed.
End LibRteS1.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require LibRteUb LibClassifyS1 LibClassifyUb LibEvalCurveS1W LibEvalCurveUb LibFitLinearS1 LibFitLinearUb.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require LibRodata LibFrame LibFPLib.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require PerfKc.

Module LibCanonS1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP1Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFPSpec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibRodata OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFPLib.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PerfKc.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf.SymDriveLB.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveLZ.
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.ev_simpl E ::= ev_simpl_lz E.
#[local] Ltac SymDriveFP.ev_simpl_in E H ::= ev_simpl_in_lz E H.
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.run_fp_with_h HR HF HK fuel stops scr chints keep extra ::= run_fp_with_h_lz HR HF HK fuel stops scr chints keep extra.
#[local] Ltac SymDriveFP.branch_case_with HR HF HK Hc ::= branch_case_with_lz HR HF HK Hc.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SXF. Import SXFS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation SEGS := Plain.M.loaded_segments.

Section Proof.
  Hypothesis Hfit : fit_linear_contract SEGS wp3_src1.
  Hypothesis Hmemset : memset20_contract SEGS wp1_src1.

  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp C data t8 t16 : word) (n len : Z) (bs : list byte).

  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis Hc : getr regs 10 = C.
  Hypothesis Hal16 : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis Hwst : writable SEGS mem (bv_unsigned sp - 160) 160.
  Hypothesis Hcal : (bv_unsigned C mod 8 = 0)%Z.
  Hypothesis Hwc : writable SEGS mem (bv_unsigned C) 32.
  Hypothesis Hc32 : (bv_unsigned C + 32 < 2 ^ 64)%Z.
  Hypothesis Hn32 : (0 <= n < 2 ^ 32)%Z.
  Hypothesis Hn   : rdn SEGS mem (Z_to_bv 64 (bv_unsigned C + 0)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 n)).
  Hypothesis Ht8  : rdn SEGS mem (Z_to_bv 64 (bv_unsigned C + 8)) 8 = Some (word_to_le_bytes 8 t8).
  Hypothesis Ht16 : rdn SEGS mem (Z_to_bv 64 (bv_unsigned C + 16)) 8 = Some (word_to_le_bytes 8 t16).
  Hypothesis Hcurve : n = 0%Z \/
     ((2 <= n <= 2 ^ 24)%Z
      /\ (bv_unsigned t8 <> 0%Z \/ bv_unsigned t16 <> 0%Z)
      /\ (bv_unsigned t8 <> 0%Z -> inDATA data len (bv_unsigned t8) n)
      /\ (bv_unsigned t16 <> 0%Z -> inDATA data len (bv_unsigned t16) (2 * n))).
  Hypothesis Hdok : data_ok mem data len bs.
  Hypothesis Hro : rodata_clear mem 0x103ec 0x1048c.
  Hypothesis Hdisj_sc : (bv_unsigned sp <= bv_unsigned C \/ bv_unsigned C + 32 <= bv_unsigned sp - 160)%Z.
  Hypothesis Hdisj_dc : (bv_unsigned data + len <= bv_unsigned C \/ bv_unsigned C + 32 <= bv_unsigned data)%Z.
  Hypothesis Hdisj_ds : (bv_unsigned data + len <= bv_unsigned sp - 160 \/ bv_unsigned sp <= bv_unsigned data)%Z.

  Let E : env := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI))
                                ++ [Z_to_bv 64 n; t8; t16])) (blobs_ev [bs]).

  Definition kn0 : list kentry :=
    [KAlign (EVar 10) 8; KAlign (EVar 2) 16;
     KWord (SA (EVar 10) 0) 4 (EVar 64); KWord (SA (EVar 10) 8) 8 (EVar 65); KWord (SA (EVar 10) 16) 8 (EVar 66);
     KWr (SA (EVar 2) (-160)) 160; KWr (SA (EVar 10) 0) 32;
     KDisj (SA (EVar 2) (-160)) 160 (SA (EVar 10) 0) 32].

  Lemma kn0_ok : know_ok SEGS E mem kn0.
  Proof.
    unfold kn0. pose proof (u64_range C). pose proof (u64_range sp).
    destruct Hwst as (W1 & W2 & W3 & W4). destruct Hwc as (V1 & V2 & V3 & V4).
    constructor; [apply kalign_intro; [lia | cbn; rewrite Hc; exact Hcal]|].
    constructor; [apply kalign_intro; [lia | cbn; rewrite Hsp; exact Hal16]|].
    constructor; [eapply (kword_intro SEGS E mem (EVar 10) C 0 4 (EVar 64) (Z_to_bv 64 n)); cbn; try lia; auto|].
    constructor; [eapply (kword_intro SEGS E mem (EVar 10) C 8 8 (EVar 65) t8); cbn; try lia; auto|].
    constructor; [eapply (kword_intro SEGS E mem (EVar 10) C 16 8 (EVar 66) t16); cbn; try lia; auto|].
    constructor; [apply (kwr_intro SEGS E mem (EVar 2) sp (-160) 160);
                  [cbn [edenot]; ev_simpl E; exact Hsp | lia | lia | lia |
                   replace (bv_unsigned sp + -160)%Z with (bv_unsigned sp - 160)%Z by lia; exact W4]|].
    constructor; [apply (kwr_intro SEGS E mem (EVar 10) C 0 32);
                  [cbn [edenot]; ev_simpl E; exact Hc | lia | lia | lia | rewrite Z.add_0_r; exact V4]|].
    constructor; [cbn [kentry_ok]; unfold estart; cbn [a_base a_off edenot]; ev_simpl E; rewrite Hsp, Hc; lia|].
    constructor.
  Qed.

  Ltac rewrite_getr_in H :=
    repeat match goal with G : getr ?R ?r = _ |- _ => rewrite G in H end.

  (* [comment removed for export] *)
  Ltac kcell HK b k n v H :=
    lazymatch type of HK with know_ok _ ?E0 ?M0 ?kn =>
      let KR := fresh "KR" in let Hfl := fresh "Hfl" in
      kread_rdn_fast SEGS E0 M0 kn b k n v HK H;
      lazymatch type of H with ?FL -> _ =>
        assert (Hfl : FL) by (unfold flat, estart; cbn [a_base a_off edenot]; ev_simpl E0; rewrite_getr; lia);
        specialize (H Hfl); clear Hfl end;
      unfold adenot, v_addi in H; cbn [a_base a_off edenot] in H; ev_simpl_in E0 H; rewrite_getr_in H
    end.

  (* [comment removed for export] *)
  Ltac frame_of_log RS fixup :=
    lazymatch goal with
    | |- frame_mod ?M0 (mem_denot ?E0 ?M0 ?log) ?regions =>
        replace regions with (regions_denot E0 RS)
          by (cbn [regions_denot map fst snd]; unfold adenot; cbn [a_base a_off edenot]; ev_simpl E0; fixup; reflexivity);
        apply (frame_mod_mem_denot E0 M0 log RS);
          [ lazymatch goal with H : log_flat _ log |- _ => exact H end
          | repeat (apply Forall_cons); [..|apply Forall_nil]; cbn [fst snd]; unfold flat, estart; cbn [a_base a_off edenot]; ev_simpl E0; fixup; lia
          | vm_compute; reflexivity ]
    end.

  (* [comment removed for export] *)
  Ltac post_regs :=
    lazymatch goal with
    | |- exists FPI' regs' mem', @mkst ?I ?R' _ ?M' _ = _ /\ _ =>
      lazymatch goal with
      | HR : regs_ok ?E1 ?sr R', HF : fregs_ok _ ?sfr (@fp_regs I), HR0 : id (regs_ok _ ?sr0 ?regs0), HF0 : id (fregs_ok _ ?sfr0 ?fr0) |- _ =>
        lift_id HR0 HR; lift_id HF0 HF;
        exists I, R', M'; split; [regv HR (1%bv:reg); rewrite_getr; reflexivity|];
        split; [exact (regs_same_on E1 sr0 sr regs0 R' abi_kept HR0 HR ltac:(vm_compute; reflexivity))|];
        split; [exact (fregs_same_on E1 sfr0 sfr fr0 _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity))|]
      end
    end.

  Ltac subst_triv := repeat match goal with H : ?a = ?b |- _ => is_var a; is_var b; subst a end.

  (* [comment removed for export] *)
  Ltac post_exit HFR Hcok :=
    run_fp 100%nat (@nil Z) noscr true; subst_triv; fin_ret; post_regs;
    split; [ eapply frame_mod_in2l; [ | | exact HFR]; lia
           | eapply curve_ok_frame; [exact HFR | exact Hcok | lia | lia | solve_apart] ].

  Theorem canon_ok :
    exists (FPI' : FPState) regs' mem',
      msteps SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x15ca8) mem rom)
                  (mkst (FP:=FPI') regs' ret mem' rom)
      /\ regs_kept abi_kept regs regs'
      /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI'))
      /\ (frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 160), 160%Z); (C, 32%Z)]
          /\ curve_ok SEGS mem' data len (bv_unsigned C)).
  Proof.
    apply runs_to_contract with
      (P := fun FPI' regs' mem' => regs_kept abi_kept regs regs'
              /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI'))
              /\ (frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 160), 160%Z); (C, 32%Z)]
                  /\ curve_ok SEGS mem' data len (bv_unsigned C))).
    assert (HR : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [bs])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [bs])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    pose proof (u64_range C) as HCr. pose proof (u64_range sp) as Hspr. pose proof (u64_range data) as Hdr.
    pose proof Hwst as (W1 & W2 & W3 & W4). pose proof Hwc as (V1 & V2 & V3 & V4).
    assert (Hcok : curve_ok SEGS mem data len (bv_unsigned C)).
    { exists n, t8, t16. split; [split; [exact Hn32| rewrite <- (Z.add_0_r (bv_unsigned C)); exact Hn]|].
      split; [exact Ht8|]. split; [exact Ht16|]. exact Hcurve. }
    destruct Hcurve as [Hn0 | (Hnr & Hsome & H8 & H16)].
    - (* [comment removed for export] *)
      assert (K64 : kentry_ok SEGS E mem (KRange (EVar 64) 0 0)).
      { apply krange_intro; cbn; rewrite u_small by lia; lia. }
      assert (HK : know_ok SEGS E mem (KRange (EVar 64) 0 0 :: kn0)) by (constructor; [exact K64|apply kn0_ok]).
      run_fp 100%nat [0x15b14%Z] noscr true.
      fin_ret.
      exists FPI0, R, M. split; [regv HR (1%bv:reg); rewrite_getr; reflexivity|].
      split; [exact (regs_same_on E _ _ regs R abi_kept HR0 HR ltac:(vm_compute; reflexivity))|].
      split; [exact (fregs_same_on E _ _ _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity))|].
      assert (HFR1 : frame_mod mem M [(Z_to_bv 64 (bv_unsigned sp - 160), 160%Z)]).
      { rewrite EQM.
        replace [(Z_to_bv 64 (bv_unsigned sp - 160), 160%Z)] with (regions_denot E [(SA (EVar 2) (-160), 160%Z)]).
        2:{ cbn [regions_denot map fst snd]. unfold adenot. cbn [a_base a_off edenot]. ev_simpl E. rewrite Hsp.
            unfold v_addi. repeat f_equal; lia. }
        apply (frame_mod_mem_denot E mem _ [(SA (EVar 2) (-160), 160%Z)]); [exact HLF | | reflexivity].
        constructor; [|constructor]. cbn [fst snd]. unfold flat, estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite Hsp. lia. }
      split.
      + eapply frame_mod_in2l; [ | | exact HFR1]; lia.
      + eapply curve_ok_frame; [exact HFR1 | exact Hcok | lia | lia | solve_apart].
    - (* [comment removed for export] *)
      assert (K64 : kentry_ok SEGS E mem (KRange (EVar 64) 2 (2^24))).
      { apply krange_intro; cbn; rewrite u_small by lia; lia. }
      assert (HK : know_ok SEGS E mem (KRange (EVar 64) 2 (2^24) :: kn0)) by (constructor; [exact K64|apply kn0_ok]).
      pose proof Hdok as (Hlen & Hbs & Hdnz & Hdhi & Hblob).
      pose proof (writable_rodata_apart_S1 mem _ _ 0x103ec 0x1048c ltac:(lia) ltac:(lia) ltac:(lia) Hwst Hro) as Hsro.
      run_fp 100%nat [0x15b14%Z] noscr true.
      assert (HFR1 : frame_mod mem M [(Z_to_bv 64 (bv_unsigned sp - 160), 160%Z)]).
      { rewrite EQM. frame_of_log [(SA (EVar 2) (-160), 160%Z)] ltac:(rewrite Hsp). }
      (* [comment removed for export] *)
      kcell HK (EVar 2) (-36)%Z 4%nat (ELit 0) HCc.
      kcell HK (EVar 10) 0%Z 4%nat (EExt false 0 4 (EVar 64)) HCn.
      rewrite ext_val_zx4_lit in HCn by lia.
      kcell HK (EVar 10) 8%Z 8%nat (EVar 65) HC8.
      kcell HK (EVar 10) 16%Z 8%nat (EVar 66) HC16.
      eapply rt_call.
      { eapply (Hfit data len bs (Z_to_bv 64 (bv_unsigned sp - 48)) C n t8 t16 FPI0 R M rom (Z_to_bv 64 0x15cfc)).
        - regv HR (1%bv:reg). reflexivity.
        - apply ret_ok_even. rewrite u_small by lia. reflexivity.
        - unfold fitlin_pre. cbv zeta. cbn [w3_fitlin_fr w3_ro_lo w3_ro_hi wp3_src1].
          rewrite !(u_small (bv_unsigned sp - 48)) by lia.
          split; [regv_lin HR (2%bv:reg); rewrite Hsp; f_equal; lia|].
          split; [regv HR (10%bv:reg); exact Hc|].
          split; [regv HR (11%bv:reg); reflexivity|].
          split; [regv_lin HR (12%bv:reg); rewrite Hsp; f_equal; lia|].
          split; [regv_lin HR (13%bv:reg); rewrite Hsp; f_equal; lia|].
          split; [regv_lin HR (14%bv:reg); rewrite Hsp; f_equal; lia|].
          split; [apply mod_sub_multiple; [lia | exact Hal16 | reflexivity]|].
          split; [eapply writable_frame; [exact HFR1|]; eapply writable_sub; [exact Hwst| lia | lia | lia]|].
          split; [exists (Z_to_bv 64 0); unfold cell;
                  replace (bv_unsigned sp - 48 + 12)%Z with (bv_unsigned sp + -36)%Z by lia; exact HCc|].
          split; [exact Hcal|]. split; [lia|].
          split.
          { unfold table_curve. split; [split; [exact Hn32| unfold cell; rewrite <- (Z.add_0_r (bv_unsigned C)); exact HCn]|].
            split; [exact HC8|]. split; [exact HC16|]. split; [exact Hnr|]. split; [exact H8|]. split; [exact H16|]. exact Hsome. }
          split; [eapply data_ok_frame; [exact HFR1 | exact Hdok | solve_apart]|].
          split; [eapply rodata_clear_frame; [exact HFR1 | exact Hro | lia | lia | solve_apart]|].
          lia. }
      cbv beta. intros FPI1 regs1 mem1 (Hkeep & Hfkeep & Hpost).
      unfold fitlin_post in Hpost. cbv zeta in Hpost. cbn [w3_fitlin_fr wp3_src1] in Hpost.
      rewrite !(u_small (bv_unsigned sp - 48)) in Hpost by lia.
      destruct Hpost as (Hfr & (wc & HWc) & (wf & HWf) & (r & Hr10 & Hrr)).
      change (112 + 16)%Z with 128%Z in Hfr.
      assert (HFR2 : frame_mod mem mem1 [(Z_to_bv 64 (bv_unsigned sp - 160), 160%Z)]).
      { eapply frame_mod_trans_same; [exact HFR1|]. eapply frame_mod_grow1; [| |exact Hfr]; rewrite !u_small by lia; lia. }
      clear HCc HCn HC8 HC16.
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep. after_call Hkeep Hfkeep FPI1.
      know_frame HK Hfr [(SA (EVar 2) (-160), 128%Z)].
      { rewrite Hsp. unfold v_addi. repeat f_equal; lia. }
      env_extend [wc; wf].
      unfold cell in HWc, HWf.
      lazymatch type of HK with know_ok _ ?E1 _ ?kn1 =>
        assert (HK' : know_ok SEGS E1 mem1 (KWord (SA (EVar 2) (-36)) 4 (EVar 131) :: KWord (SA (EVar 2) (-44)) 4 (EVar 132) :: kn1));
        [ constructor; [eapply (kword_intro SEGS E1 mem1 (EVar 2) sp (-36) 4 (EVar 131) wc); cbn [edenot]; ev_simpl E1;
                        first [exact Hsp | reflexivity | lia
                              | replace (bv_unsigned sp + -36)%Z with (bv_unsigned sp - 48 + 12)%Z by lia; exact HWc] |];
          constructor; [eapply (kword_intro SEGS E1 mem1 (EVar 2) sp (-44) 4 (EVar 132) wf); cbn [edenot]; ev_simpl E1;
                        first [exact Hsp | reflexivity | lia
                              | replace (bv_unsigned sp + -44)%Z with (bv_unsigned sp - 48 + 4)%Z by lia; exact HWf] |];
          exact HK
        | clear HK; rename HK' into HK ]
      end.
      (* [comment removed for export] *)
      branch_case as Hb1; [post_exit HFR2 Hcok|].
      run_fp 100%nat (@nil Z) noscr true; subst_triv.
      branch_case as Hb2; [post_exit HFR2 Hcok|].
      run_fp 100%nat (@nil Z) noscr true; subst_triv.
      branch_case as Hb3; [post_exit HFR2 Hcok|].
      (* [comment removed for export] *)
      run_fp 100%nat [0x1dfe4%Z] noscr true.
      lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
        lazymatch goal with EQMx : M' = mem_denot _ mem1 _ |- _ =>
        assert (HFRB : frame_mod mem1 M' [(C, 32%Z)])
          by (rewrite EQMx; frame_of_log [(SA (EVar 10) 0, 32%Z)] ltac:(rewrite Hc, ?v_addi_0));
        eapply rt_call;
        [ eapply (Hmemset (Z_to_bv 64 (bv_unsigned C + 12)) I R' M' rom (Z_to_bv 64 0x15d40));
          [ regv HR (1%bv:reg); reflexivity
          | apply ret_ok_even; rewrite u_small by lia; reflexivity
          | unfold memset_pre; rewrite !(u_small (bv_unsigned C + 12)) by lia;
            split; [regv_lin HR (10%bv:reg); rewrite Hc; f_equal; lia|];
            split; [regv HR (11%bv:reg); reflexivity|];
            split; [regv HR (12%bv:reg); reflexivity|];
            split; [apply mod8_mod4_12; exact Hcal|];
            split; [eapply writable_frame; [exact HFRB|]; eapply writable_frame; [exact HFR2|];
                    eapply writable_sub; [exact Hwc|lia|lia|lia]|];
            lia ]
        | ] end end.
      cbv beta. intros FPI9 regs9 mem9 (Hkeep9 & Hfkeep9 & Hfr9 & Hz9 & _).
      unfold regs_kept in Hkeep9. unfold fregs_kept in Hfkeep9.
      rewrite !(u_small (bv_unsigned C + 12)) in Hz9 by lia.
      after_call Hkeep9 Hfkeep9 FPI9.
      know_frame HK Hfr9 [(SA (EVar 10) 12, 20%Z)].
      { rewrite Hc. reflexivity. }
      run_fp 100%nat (@nil Z) noscr true; subst_triv.
      fin_ret. post_regs.
      kcell HK (EVar 10) 0%Z 4%nat (ELit 0) HC0.
      kcell HK (EVar 10) 8%Z 4%nat (ELit 1065353216) HC8.
      assert (HT8 : exists t8', LibDefs.cell SEGS mem9 (bv_unsigned C + 8) 8 t8').
      { eapply cell_of_rdn; [|lia]. change 8%nat with (4 + 4)%nat. eapply rdn_app; [exact HC8|].
        rewrite u_small by lia. change (Z.of_nat 4) with 4%Z.
        replace (bv_unsigned C + 8 + 4)%Z with (bv_unsigned C + 12)%Z by lia.
        apply rdn_zeros; [lia|lia|lia|]. change (Z.of_nat 4) with 4%Z. intros i Hi. apply Hz9. lia. }
      destruct HT8 as (t8' & HT8).
      split.
      + eapply frame_mod_trans_same; [eapply frame_mod_in2l; [| | exact HFR2]; lia|].
        eapply frame_mod_trans_same; [eapply frame_mod_in2r; [| | exact HFRB]; lia|].
        eapply frame_mod_in2r; [| | exact Hfr9]; rewrite ?u_small by lia; lia.
      + exists 0%Z, t8', (Z_to_bv 64 0). split; [|split; [exact HT8|split; [|left; reflexivity]]].
        * split; [lia|]. unfold LibDefs.cell. rewrite Z.add_0_r in HC0. exact HC0.
        * unfold cell64. apply cell_zeros; [lia|lia|lia|]. change (Z.of_nat 8) with 8%Z.
          intros i Hi. replace (bv_unsigned C + 16 + i)%Z with (bv_unsigned C + 12 + (i + 4))%Z by lia. apply Hz9. lia.
  Qed.
End Proof.

Theorem canonicalize_src1 :
  fit_linear_contract SEGS wp3_src1 -> memset20_contract SEGS wp1_src1 ->
  canonicalize_contract SEGS wp3_src1.
Proof.
  intros Hfit Hmemset data len bs sp C FPI regs mem rom ret Hra Hret PRE.
  destruct PRE as (Hsp & Hc & Hal16 & Hwst & Hcal & Hwc & Hc32 & Hcurve & Hdok & Hro & Hd1 & Hd2 & Hd3).
  cbn [w3_canon_d w3_ro_lo w3_ro_hi wp3_src1] in *.
  destruct Hcurve as (n & t8 & t16 & [Hn32 Hn] & H8c & H16c & Hcase).
  unfold cell64, LibDefs.cell in H8c, H16c. unfold LibDefs.cell in Hn.
  destruct (canon_ok Hfit Hmemset FPI regs mem rom ret sp C data t8 t16 n len bs Hra Hret Hsp Hc Hal16 Hwst Hcal Hwc Hc32
              Hn32 ltac:(rewrite Z.add_0_r; exact Hn) H8c H16c Hcase Hdok Hro Hd1 Hd3)
    as (FPI' & regs' & mem' & Hms & Hk1 & Hk2 & Hpost).
  exists FPI', regs', mem'. split; [exact Hms|]. split; [exact Hk1|]. split; [exact Hk2|]. exact Hpost.
Qed.
End LibCanonS1.

Module LibCanonUb.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP1Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFPSpec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibRodata OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFPLib.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PerfKc.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf.SymDriveLB.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveLZ.
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.ev_simpl E ::= ev_simpl_lz E.
#[local] Ltac SymDriveFP.ev_simpl_in E H ::= ev_simpl_in_lz E H.
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.run_fp_with_h HR HF HK fuel stops scr chints keep extra ::= run_fp_with_h_lz HR HF HK fuel stops scr chints keep extra.
#[local] Ltac SymDriveFP.branch_case_with HR HF HK Hc ::= branch_case_with_lz HR HF HK Hc.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SXF. Import SXFS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation SEGS := Ubsan.M.loaded_segments.

Section Proof.
  Hypothesis Hfit : fit_linear_contract SEGS wp3_infoub.
  Hypothesis Hmemset : memset20_contract SEGS wp1_infoub.

  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp C data t8 t16 : word) (n len : Z) (bs : list byte).

  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis Hc : getr regs 10 = C.
  Hypothesis Hal16 : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis Hwst : writable SEGS mem (bv_unsigned sp - 176) 176.
  Hypothesis Hcal : (bv_unsigned C mod 8 = 0)%Z.
  Hypothesis Hwc : writable SEGS mem (bv_unsigned C) 32.
  Hypothesis Hc32 : (bv_unsigned C + 32 < 2 ^ 64)%Z.
  Hypothesis Hn32 : (0 <= n < 2 ^ 32)%Z.
  Hypothesis Hn   : rdn SEGS mem (Z_to_bv 64 (bv_unsigned C + 0)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 n)).
  Hypothesis Ht8  : rdn SEGS mem (Z_to_bv 64 (bv_unsigned C + 8)) 8 = Some (word_to_le_bytes 8 t8).
  Hypothesis Ht16 : rdn SEGS mem (Z_to_bv 64 (bv_unsigned C + 16)) 8 = Some (word_to_le_bytes 8 t16).
  Hypothesis Hcurve : n = 0%Z \/
     ((2 <= n <= 2 ^ 24)%Z
      /\ (bv_unsigned t8 <> 0%Z \/ bv_unsigned t16 <> 0%Z)
      /\ (bv_unsigned t8 <> 0%Z -> inDATA data len (bv_unsigned t8) n)
      /\ (bv_unsigned t16 <> 0%Z -> inDATA data len (bv_unsigned t16) (2 * n))).
  Hypothesis Hdok : data_ok mem data len bs.
  Hypothesis Hro : rodata_clear mem 0x103ec 0x10490.
  Hypothesis Hdisj_sc : (bv_unsigned sp <= bv_unsigned C \/ bv_unsigned C + 32 <= bv_unsigned sp - 176)%Z.
  Hypothesis Hdisj_dc : (bv_unsigned data + len <= bv_unsigned C \/ bv_unsigned C + 32 <= bv_unsigned data)%Z.
  Hypothesis Hdisj_ds : (bv_unsigned data + len <= bv_unsigned sp - 176 \/ bv_unsigned sp <= bv_unsigned data)%Z.

  Let E : env := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI))
                                ++ [Z_to_bv 64 n; t8; t16])) (blobs_ev [bs]).

  Definition kn0 : list kentry :=
    [KAlign (EVar 10) 8; KAlign (EVar 2) 16;
     KWord (SA (EVar 10) 0) 4 (EVar 64); KWord (SA (EVar 10) 8) 8 (EVar 65); KWord (SA (EVar 10) 16) 8 (EVar 66);
     KWr (SA (EVar 2) (-176)) 176; KWr (SA (EVar 10) 0) 32;
     KDisj (SA (EVar 2) (-176)) 176 (SA (EVar 10) 0) 32].

  Lemma kn0_ok : know_ok SEGS E mem kn0.
  Proof.
    unfold kn0. pose proof (u64_range C). pose proof (u64_range sp).
    destruct Hwst as (W1 & W2 & W3 & W4). destruct Hwc as (V1 & V2 & V3 & V4).
    constructor; [apply kalign_intro; [lia | cbn; rewrite Hc; exact Hcal]|].
    constructor; [apply kalign_intro; [lia | cbn; rewrite Hsp; exact Hal16]|].
    constructor; [eapply (kword_intro SEGS E mem (EVar 10) C 0 4 (EVar 64) (Z_to_bv 64 n)); cbn; try lia; auto|].
    constructor; [eapply (kword_intro SEGS E mem (EVar 10) C 8 8 (EVar 65) t8); cbn; try lia; auto|].
    constructor; [eapply (kword_intro SEGS E mem (EVar 10) C 16 8 (EVar 66) t16); cbn; try lia; auto|].
    constructor; [apply (kwr_intro SEGS E mem (EVar 2) sp (-176) 176);
                  [cbn [edenot]; ev_simpl E; exact Hsp | lia | lia | lia |
                   replace (bv_unsigned sp + -176)%Z with (bv_unsigned sp - 176)%Z by lia; exact W4]|].
    constructor; [apply (kwr_intro SEGS E mem (EVar 10) C 0 32);
                  [cbn [edenot]; ev_simpl E; exact Hc | lia | lia | lia | rewrite Z.add_0_r; exact V4]|].
    constructor; [cbn [kentry_ok]; unfold estart; cbn [a_base a_off edenot]; ev_simpl E; rewrite Hsp, Hc; lia|].
    constructor.
  Qed.

  Ltac rewrite_getr_in H :=
    repeat match goal with G : getr ?R ?r = _ |- _ => rewrite G in H end.

  (* [comment removed for export] *)
  Ltac kcell HK b k n v H :=
    lazymatch type of HK with know_ok _ ?E0 ?M0 ?kn =>
      let KR := fresh "KR" in let Hfl := fresh "Hfl" in
      kread_rdn_fast SEGS E0 M0 kn b k n v HK H;
      lazymatch type of H with ?FL -> _ =>
        assert (Hfl : FL) by (unfold flat, estart; cbn [a_base a_off edenot]; ev_simpl E0; rewrite_getr; lia);
        specialize (H Hfl); clear Hfl end;
      unfold adenot, v_addi in H; cbn [a_base a_off edenot] in H; ev_simpl_in E0 H; rewrite_getr_in H
    end.

  (* [comment removed for export] *)
  Ltac frame_of_log RS fixup :=
    lazymatch goal with
    | |- frame_mod ?M0 (mem_denot ?E0 ?M0 ?log) ?regions =>
        replace regions with (regions_denot E0 RS)
          by (cbn [regions_denot map fst snd]; unfold adenot; cbn [a_base a_off edenot]; ev_simpl E0; fixup; reflexivity);
        apply (frame_mod_mem_denot E0 M0 log RS);
          [ lazymatch goal with H : log_flat _ log |- _ => exact H end
          | repeat (apply Forall_cons); [..|apply Forall_nil]; cbn [fst snd]; unfold flat, estart; cbn [a_base a_off edenot]; ev_simpl E0; fixup; lia
          | vm_compute; reflexivity ]
    end.

  (* [comment removed for export] *)
  Ltac post_regs :=
    lazymatch goal with
    | |- exists FPI' regs' mem', @mkst ?I ?R' _ ?M' _ = _ /\ _ =>
      lazymatch goal with
      | HR : regs_ok ?E1 ?sr R', HF : fregs_ok _ ?sfr (@fp_regs I), HR0 : id (regs_ok _ ?sr0 ?regs0), HF0 : id (fregs_ok _ ?sfr0 ?fr0) |- _ =>
        lift_id HR0 HR; lift_id HF0 HF;
        exists I, R', M'; split; [regv HR (1%bv:reg); rewrite_getr; reflexivity|];
        split; [exact (regs_same_on E1 sr0 sr regs0 R' abi_kept HR0 HR ltac:(vm_compute; reflexivity))|];
        split; [exact (fregs_same_on E1 sfr0 sfr fr0 _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity))|]
      end
    end.

  Ltac subst_triv := repeat match goal with H : ?a = ?b |- _ => is_var a; is_var b; subst a end.

  (* [comment removed for export] *)
  Ltac post_exit HFR Hcok :=
    run_fp 100%nat (@nil Z) noscr true; subst_triv; fin_ret; post_regs;
    split; [ eapply frame_mod_in2l; [ | | exact HFR]; lia
           | eapply curve_ok_frame; [exact HFR | exact Hcok | lia | lia | solve_apart] ].

  Theorem canon_ok :
    exists (FPI' : FPState) regs' mem',
      msteps SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x165ac) mem rom)
                  (mkst (FP:=FPI') regs' ret mem' rom)
      /\ regs_kept abi_kept regs regs'
      /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI'))
      /\ (frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 176), 176%Z); (C, 32%Z)]
          /\ curve_ok SEGS mem' data len (bv_unsigned C)).
  Proof.
    apply runs_to_contract with
      (P := fun FPI' regs' mem' => regs_kept abi_kept regs regs'
              /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI'))
              /\ (frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 176), 176%Z); (C, 32%Z)]
                  /\ curve_ok SEGS mem' data len (bv_unsigned C))).
    assert (HR : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [bs])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [bs])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    pose proof (u64_range C) as HCr. pose proof (u64_range sp) as Hspr. pose proof (u64_range data) as Hdr.
    pose proof Hwst as (W1 & W2 & W3 & W4). pose proof Hwc as (V1 & V2 & V3 & V4).
    assert (Hcok : curve_ok SEGS mem data len (bv_unsigned C)).
    { exists n, t8, t16. split; [split; [exact Hn32| rewrite <- (Z.add_0_r (bv_unsigned C)); exact Hn]|].
      split; [exact Ht8|]. split; [exact Ht16|]. exact Hcurve. }
    destruct Hcurve as [Hn0 | (Hnr & Hsome & H8 & H16)].
    - (* [comment removed for export] *)
      assert (K64 : kentry_ok SEGS E mem (KRange (EVar 64) 0 0)).
      { apply krange_intro; cbn; rewrite u_small by lia; lia. }
      assert (HK : know_ok SEGS E mem (KRange (EVar 64) 0 0 :: kn0)) by (constructor; [exact K64|apply kn0_ok]).
      run_fp 100%nat [0x163f0%Z] noscr true.
      fin_ret.
      exists FPI0, R, M. split; [regv HR (1%bv:reg); rewrite_getr; reflexivity|].
      split; [exact (regs_same_on E _ _ regs R abi_kept HR0 HR ltac:(vm_compute; reflexivity))|].
      split; [exact (fregs_same_on E _ _ _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity))|].
      assert (HFR1 : frame_mod mem M [(Z_to_bv 64 (bv_unsigned sp - 176), 176%Z)]).
      { rewrite EQM.
        replace [(Z_to_bv 64 (bv_unsigned sp - 176), 176%Z)] with (regions_denot E [(SA (EVar 2) (-176), 176%Z)]).
        2:{ cbn [regions_denot map fst snd]. unfold adenot. cbn [a_base a_off edenot]. ev_simpl E. rewrite Hsp.
            unfold v_addi. repeat f_equal; lia. }
        apply (frame_mod_mem_denot E mem _ [(SA (EVar 2) (-176), 176%Z)]); [exact HLF | | reflexivity].
        constructor; [|constructor]. cbn [fst snd]. unfold flat, estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite Hsp. lia. }
      split.
      + eapply frame_mod_in2l; [ | | exact HFR1]; lia.
      + eapply curve_ok_frame; [exact HFR1 | exact Hcok | lia | lia | solve_apart].
    - (* [comment removed for export] *)
      assert (K64 : kentry_ok SEGS E mem (KRange (EVar 64) 2 (2^24))).
      { apply krange_intro; cbn; rewrite u_small by lia; lia. }
      assert (HK : know_ok SEGS E mem (KRange (EVar 64) 2 (2^24) :: kn0)) by (constructor; [exact K64|apply kn0_ok]).
      pose proof Hdok as (Hlen & Hbs & Hdnz & Hdhi & Hblob).
      pose proof (writable_rodata_apart_Ub mem _ _ 0x103ec 0x10490 ltac:(lia) ltac:(lia) ltac:(lia) Hwst Hro) as Hsro.
      run_fp 100%nat [0x163f0%Z] noscr true.
      assert (HFR1 : frame_mod mem M [(Z_to_bv 64 (bv_unsigned sp - 176), 176%Z)]).
      { rewrite EQM. frame_of_log [(SA (EVar 2) (-176), 176%Z)] ltac:(rewrite Hsp). }
      (* [comment removed for export] *)
      kcell HK (EVar 2) (-36)%Z 4%nat (ELit 0) HCc.
      kcell HK (EVar 10) 0%Z 4%nat (EExt false 0 4 (EVar 64)) HCn.
      rewrite ext_val_zx4_lit in HCn by lia.
      kcell HK (EVar 10) 8%Z 8%nat (EVar 65) HC8.
      kcell HK (EVar 10) 16%Z 8%nat (EVar 66) HC16.
      eapply rt_call.
      { eapply (Hfit data len bs (Z_to_bv 64 (bv_unsigned sp - 48)) C n t8 t16 FPI0 R M rom (Z_to_bv 64 0x16618)).
        - regv HR (1%bv:reg). reflexivity.
        - apply ret_ok_even. rewrite u_small by lia. reflexivity.
        - unfold fitlin_pre. cbv zeta. cbn [w3_fitlin_fr w3_ro_lo w3_ro_hi wp3_infoub].
          rewrite !(u_small (bv_unsigned sp - 48)) by lia.
          split; [regv_lin HR (2%bv:reg); rewrite Hsp; f_equal; lia|].
          split; [regv HR (10%bv:reg); exact Hc|].
          split; [regv HR (11%bv:reg); reflexivity|].
          split; [regv_lin HR (12%bv:reg); rewrite Hsp; f_equal; lia|].
          split; [regv_lin HR (13%bv:reg); rewrite Hsp; f_equal; lia|].
          split; [regv_lin HR (14%bv:reg); rewrite Hsp; f_equal; lia|].
          split; [apply mod_sub_multiple; [lia | exact Hal16 | reflexivity]|].
          split; [eapply writable_frame; [exact HFR1|]; eapply writable_sub; [exact Hwst| lia | lia | lia]|].
          split; [exists (Z_to_bv 64 0); unfold cell;
                  replace (bv_unsigned sp - 48 + 12)%Z with (bv_unsigned sp + -36)%Z by lia; exact HCc|].
          split; [exact Hcal|]. split; [lia|].
          split.
          { unfold table_curve. split; [split; [exact Hn32| unfold cell; rewrite <- (Z.add_0_r (bv_unsigned C)); exact HCn]|].
            split; [exact HC8|]. split; [exact HC16|]. split; [exact Hnr|]. split; [exact H8|]. split; [exact H16|]. exact Hsome. }
          split; [eapply data_ok_frame; [exact HFR1 | exact Hdok | solve_apart]|].
          split; [eapply rodata_clear_frame; [exact HFR1 | exact Hro | lia | lia | solve_apart]|].
          lia. }
      cbv beta. intros FPI1 regs1 mem1 (Hkeep & Hfkeep & Hpost).
      unfold fitlin_post in Hpost. cbv zeta in Hpost. cbn [w3_fitlin_fr wp3_infoub] in Hpost.
      rewrite !(u_small (bv_unsigned sp - 48)) in Hpost by lia.
      destruct Hpost as (Hfr & (wc & HWc) & (wf & HWf) & (r & Hr10 & Hrr)).
      change (128 + 16)%Z with 144%Z in Hfr.
      assert (HFR2 : frame_mod mem mem1 [(Z_to_bv 64 (bv_unsigned sp - 176), 176%Z)]).
      { eapply frame_mod_trans_same; [exact HFR1|]. eapply frame_mod_grow1; [| |exact Hfr]; rewrite !u_small by lia; lia. }
      clear HCc HCn HC8 HC16.
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep. after_call Hkeep Hfkeep FPI1.
      know_frame HK Hfr [(SA (EVar 2) (-176), 144%Z)].
      { rewrite Hsp. unfold v_addi. repeat f_equal; lia. }
      env_extend [wc; wf].
      unfold cell in HWc, HWf.
      lazymatch type of HK with know_ok _ ?E1 _ ?kn1 =>
        assert (HK' : know_ok SEGS E1 mem1 (KWord (SA (EVar 2) (-36)) 4 (EVar 131) :: KWord (SA (EVar 2) (-44)) 4 (EVar 132) :: kn1));
        [ constructor; [eapply (kword_intro SEGS E1 mem1 (EVar 2) sp (-36) 4 (EVar 131) wc); cbn [edenot]; ev_simpl E1;
                        first [exact Hsp | reflexivity | lia
                              | replace (bv_unsigned sp + -36)%Z with (bv_unsigned sp - 48 + 12)%Z by lia; exact HWc] |];
          constructor; [eapply (kword_intro SEGS E1 mem1 (EVar 2) sp (-44) 4 (EVar 132) wf); cbn [edenot]; ev_simpl E1;
                        first [exact Hsp | reflexivity | lia
                              | replace (bv_unsigned sp + -44)%Z with (bv_unsigned sp - 48 + 4)%Z by lia; exact HWf] |];
          exact HK
        | clear HK; rename HK' into HK ]
      end.
      (* [comment removed for export] *)
      branch_case as Hb1; [post_exit HFR2 Hcok|].
      run_fp 100%nat (@nil Z) noscr true; subst_triv.
      branch_case as Hb2; [post_exit HFR2 Hcok|].
      run_fp 100%nat (@nil Z) noscr true; subst_triv.
      branch_case as Hb3; [post_exit HFR2 Hcok|].
      (* [comment removed for export] *)
      run_fp 100%nat [0x1eae0%Z] noscr true.
      lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
        lazymatch goal with EQMx : M' = mem_denot _ mem1 _ |- _ =>
        assert (HFRB : frame_mod mem1 M' [(C, 32%Z)])
          by (rewrite EQMx; frame_of_log [(SA (EVar 10) 0, 32%Z)] ltac:(rewrite Hc, ?v_addi_0));
        eapply rt_call;
        [ eapply (Hmemset (Z_to_bv 64 (bv_unsigned C + 12)) I R' M' rom (Z_to_bv 64 0x16660));
          [ regv HR (1%bv:reg); reflexivity
          | apply ret_ok_even; rewrite u_small by lia; reflexivity
          | unfold memset_pre; rewrite !(u_small (bv_unsigned C + 12)) by lia;
            split; [regv_lin HR (10%bv:reg); rewrite Hc; f_equal; lia|];
            split; [regv HR (11%bv:reg); reflexivity|];
            split; [regv HR (12%bv:reg); reflexivity|];
            split; [apply mod8_mod4_12; exact Hcal|];
            split; [eapply writable_frame; [exact HFRB|]; eapply writable_frame; [exact HFR2|];
                    eapply writable_sub; [exact Hwc|lia|lia|lia]|];
            lia ]
        | ] end end.
      cbv beta. intros FPI9 regs9 mem9 (Hkeep9 & Hfkeep9 & Hfr9 & Hz9 & _).
      unfold regs_kept in Hkeep9. unfold fregs_kept in Hfkeep9.
      rewrite !(u_small (bv_unsigned C + 12)) in Hz9 by lia.
      after_call Hkeep9 Hfkeep9 FPI9.
      know_frame HK Hfr9 [(SA (EVar 10) 12, 20%Z)].
      { rewrite Hc. reflexivity. }
      run_fp 100%nat (@nil Z) noscr true; subst_triv.
      fin_ret. post_regs.
      kcell HK (EVar 10) 0%Z 4%nat (ELit 0) HC0.
      kcell HK (EVar 10) 8%Z 4%nat (ELit 1065353216) HC8.
      assert (HT8 : exists t8', LibDefs.cell SEGS mem9 (bv_unsigned C + 8) 8 t8').
      { eapply cell_of_rdn; [|lia]. change 8%nat with (4 + 4)%nat. eapply rdn_app; [exact HC8|].
        rewrite u_small by lia. change (Z.of_nat 4) with 4%Z.
        replace (bv_unsigned C + 8 + 4)%Z with (bv_unsigned C + 12)%Z by lia.
        apply rdn_zeros; [lia|lia|lia|]. change (Z.of_nat 4) with 4%Z. intros i Hi. apply Hz9. lia. }
      destruct HT8 as (t8' & HT8).
      split.
      + eapply frame_mod_trans_same; [eapply frame_mod_in2l; [| | exact HFR2]; lia|].
        eapply frame_mod_trans_same; [eapply frame_mod_in2r; [| | exact HFRB]; lia|].
        eapply frame_mod_in2r; [| | exact Hfr9]; rewrite ?u_small by lia; lia.
      + exists 0%Z, t8', (Z_to_bv 64 0). split; [|split; [exact HT8|split; [|left; reflexivity]]].
        * split; [lia|]. unfold LibDefs.cell. rewrite Z.add_0_r in HC0. exact HC0.
        * unfold cell64. apply cell_zeros; [lia|lia|lia|]. change (Z.of_nat 8) with 8%Z.
          intros i Hi. replace (bv_unsigned C + 16 + i)%Z with (bv_unsigned C + 12 + (i + 4))%Z by lia. apply Hz9. lia.
  Qed.
End Proof.

Theorem canonicalize_infoub :
  fit_linear_contract SEGS wp3_infoub -> memset20_contract SEGS wp1_infoub ->
  canonicalize_contract SEGS wp3_infoub.
Proof.
  intros Hfit Hmemset data len bs sp C FPI regs mem rom ret Hra Hret PRE.
  destruct PRE as (Hsp & Hc & Hal16 & Hwst & Hcal & Hwc & Hc32 & Hcurve & Hdok & Hro & Hd1 & Hd2 & Hd3).
  cbn [w3_canon_d w3_ro_lo w3_ro_hi wp3_infoub] in *.
  destruct Hcurve as (n & t8 & t16 & [Hn32 Hn] & H8c & H16c & Hcase).
  unfold cell64, LibDefs.cell in H8c, H16c. unfold LibDefs.cell in Hn.
  destruct (canon_ok Hfit Hmemset FPI regs mem rom ret sp C data t8 t16 n len bs Hra Hret Hsp Hc Hal16 Hwst Hcal Hwc Hc32
              Hn32 ltac:(rewrite Z.add_0_r; exact Hn) H8c H16c Hcase Hdok Hro Hd1 Hd3)
    as (FPI' & regs' & mem' & Hms & Hk1 & Hk2 & Hpost).
  exists FPI', regs', mem'. split; [exact Hms|]. split; [exact Hk1|]. split; [exact Hk2|]. exact Hpost.
Qed.
End LibCanonUb.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require LibReadA2BS1h LibReadA2BUbh LibReadB2AS1 LibReadB2AUbh LibGetTagS1 LibGetTagUb LibGetIdxS1 LibGetIdxUb LibToXyzS1 LibToXyzUb.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require LibTagsLib.

Module LibCicpUb.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsSpec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsLib.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf.SymDriveLB.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveLZ.
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.ev_simpl E ::= ev_simpl_lz E.
#[local] Ltac SymDriveFP.ev_simpl_in E H ::= ev_simpl_in_lz E H.
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.run_fp_with_h HR HF HK fuel stops scr chints keep extra ::= run_fp_with_h_lz HR HF HK fuel stops scr chints keep extra.
#[local] Ltac SymDriveFP.branch_case_with HR HF HK Hc ::= branch_case_with_lz HR HF HK Hc.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SXF. Import SXFS.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].

#[local] Abbreviation SEGS := Ubsan.M.loaded_segments.

Section CI.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret T C data buf : word) (ty sz len : Z) (bs : list byte).

  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis HT : getr regs 10 = T.
  Hypothesis HC : getr regs 11 = C.
  Hypothesis Hlen : (0 <= len < 2 ^ 26)%Z.
  Hypothesis Hbs : Z.of_nat (length bs) = len.
  Hypothesis Hdnz : (0 < bv_unsigned data)%Z.
  Hypothesis Hdata : (bv_unsigned data + len < 2 ^ 47)%Z.
  Hypothesis Hblob : forall k, (0 <= k < len)%Z ->
      mem (Z_to_bv 64 (bv_unsigned data + k)) = Some (nth (Z.to_nat k) bs (Z_to_bv 8 0)).
  Hypothesis Hty : rdn SEGS mem (Z_to_bv 64 (bv_unsigned T + 4)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 ty)).
  Hypothesis Htyr : (0 <= ty < 2 ^ 32)%Z.
  Hypothesis Hsz : rdn SEGS mem (Z_to_bv 64 (bv_unsigned T + 8)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 sz)).
  Hypothesis Hszr : (0 <= sz < 2 ^ 32)%Z.
  Hypothesis Hbuf : rdn SEGS mem (Z_to_bv 64 (bv_unsigned T + 16)) 8 = Some (word_to_le_bytes 8 buf).
  Hypothesis Hin1 : (bv_unsigned data <= bv_unsigned buf)%Z.
  Hypothesis Hin2 : (bv_unsigned buf + sz <= bv_unsigned data + len)%Z.
  Hypothesis Htal : (bv_unsigned T mod 8 = 0)%Z.
  Hypothesis Ht24 : (bv_unsigned T + 24 <= 2 ^ 64)%Z.
  Hypothesis HCst : store_ok SEGS mem (Z_to_bv 64 (bv_unsigned C)) (Z.to_nat 4) = true.
  Hypothesis HC4 : (bv_unsigned C + 4 <= 2 ^ 64)%Z.
  Hypothesis HCD : (bv_unsigned data + len <= bv_unsigned C \/ bv_unsigned C + 4 <= bv_unsigned data)%Z.

  Let E : env := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI))
                                ++ [buf; Z_to_bv 64 ty; Z_to_bv 64 sz; Z_to_bv 64 len; data])) (blobs_ev [bs]).
  (* [comment removed for export] *)

  Definition kn0 : list kentry :=
    [KRange (EVar 10) 0 (2^64 - 24);
     KRange (EVar 11) 0 (2^64 - 4);
     KRange (EVar 64) 1 (2^47);
     KRange (EVar 68) 1 (2^47);
     KAlign (EVar 10) 8;
     KWord (SA (EVar 10) 4) 4 (EVar 65);
     KWord (SA (EVar 10) 8) 4 (EVar 66);
     KWord (SA (EVar 10) 16) 8 (EVar 64);
     KWr (SA (EVar 11) 0) 4;
     KBlobD (SA (EVar 68) 0) (EVar 67) 0].

  Lemma kblob_ok : kentry_ok SEGS E mem (KBlobD (SA (EVar 68) 0) (EVar 67) 0).
  Proof using FPI Hblob Hbs Hdata Hdnz Hlen Hszr Htyr T buf regs rom.
    pose proof (u64_range data).
    cbn [kentry_ok]. unfold flat, estart, elenZ. cbn. rewrite u_small by lia.
    split; [lia|]. split; [exact Hbs|]. intros k Hk. rewrite Z.add_0_r. apply Hblob. exact Hk.
  Qed.

  Lemma kn0_ok : know_ok SEGS E mem kn0.
  Proof using FPI HC HC4 HCst HT Hblob Hbs Hbuf Hdata Hdnz Hin1 Hin2 Hlen Hsz Hszr Ht24 Htal Hty Htyr rom.
    unfold kn0. pose proof (u64_range data). pose proof (u64_range T). pose proof (u64_range buf).
    pose proof (u64_range C).
    unfold know_ok.
    repeat (apply Forall_cons); [..|apply Forall_nil].
    - apply krange_intro; cbn. rewrite HT. lia.
    - apply krange_intro; cbn. rewrite HC. lia.
    - apply krange_intro; cbn. lia.
    - apply krange_intro; cbn. lia.
    - apply kalign_intro; [lia|]. cbn. rewrite HT. exact Htal.
    - eapply (kword_intro SEGS E mem (EVar 10) T 4 4 (EVar 65) (Z_to_bv 64 ty)); cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (EVar 10) T 8 4 (EVar 66) (Z_to_bv 64 sz)); cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (EVar 10) T 16 8 (EVar 64) buf); cbn; try lia; auto.
    - apply (kwr_intro SEGS E mem (EVar 11) C 0 4); cbn; try lia. exact HC. rewrite Z.add_0_r. exact HCst.
    - apply kblob_ok.
  Qed.

  (* [comment removed for export] *)
  Definition knA : list kentry :=
    KRange (EVar 66) 12 (2^26) ::
    KDisj (SA (EVar 11) 0) 4 (SA (EVar 64) 8) 4 :: kn0.
  Definition knB : list kentry := KRange (EVar 66) 0 11 :: kn0.

  Lemma knA_ok : (12 <= sz)%Z -> know_ok SEGS E mem knA.
  Proof using FPI HC HC4 HCD HCst HT Hblob Hbs Hbuf Hdata Hdnz Hin1 Hin2 Hlen Hsz Hszr Ht24 Htal Hty Htyr rom.
    intros Hc. pose proof (u64_range buf).
    apply know_ok_cons; [| apply know_ok_cons; [| apply kn0_ok]].
    - apply krange_intro; cbn. rewrite u_small by lia. lia.
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite HC. lia.
  Qed.

  Lemma knB_ok : (sz < 12)%Z -> know_ok SEGS E mem knB.
  Proof using FPI HC HC4 HCst HT Hblob Hbs Hbuf Hdata Hdnz Hin1 Hin2 Hlen Hsz Hszr Ht24 Htal Hty Htyr rom.
    intros Hc. apply know_ok_cons; [| apply kn0_ok].
    apply krange_intro; cbn. rewrite u_small by lia. lia.
  Qed.

  Definition POST (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
    frame_mod mem mem' [(C, 4%Z)] /\
    exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1)%Z.

  Definition RS : list (saddr * Z) := [(SA (EVar 11) 0, 4%Z)].

  Lemma RS_denot : regions_denot E RS = [(C, 4%Z)].
  Proof using FPI HC bs buf data len sz ty.
    unfold regions_denot, RS. cbn [map fst snd]. unfold adenot. cbn [a_base a_off edenot]. ev_simpl E.
    rewrite HC. unfold v_addi. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned. reflexivity.
  Qed.

  Ltac finish HR0 HF0 :=
    fin_ret;
    lazymatch goal with
    | HR : regs_ok _ ?sr ?R2, HF : fregs_ok _ ?sfr (@fp_regs ?FP2), HK : know_ok _ _ ?M2 _ |- _ =>
      exists FP2, R2, M2;
      split; [regv HR (1%bv:reg); rewrite Hra; reflexivity|];
      split; [exact (regs_same_on E _ _ regs _ abi_kept HR0 HR ltac:(vm_compute; reflexivity))|];
      split; [exact (fregs_same_on E _ _ _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity))|];
      unfold POST; split; [| eexists; split; [regv HR (10%bv:reg); reflexivity | lia]]
    end.

  Lemma cicp_run :
    runs_to SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x1633c) mem rom)
      (fun st' => exists (FPI' : FPState) regs' mem',
          st' = mkst (FP:=FPI') regs' ret mem' rom /\
          regs_kept abi_kept regs regs' /\
          fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI')) /\
          POST regs' mem').
  Proof using E HC HC4 HCD HCst HT Hblob Hbs Hbuf Hdata Hdnz Hin1 Hin2 Hlen Hra Hret Hsz Hszr Ht24 Htal Hty Htyr.
    pose proof (u64_range data) as Rd. pose proof (u64_range T) as RT. pose proof (u64_range buf) as Rb.
    pose proof (u64_range C) as RC.
    assert (HR : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [bs])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [bs])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    destruct (Z_lt_le_dec sz 12) as [Hc|Hc].
    - pose proof (knB_ok Hc) as HK.
      run_fp 20%nat (@nil Z) noscr false.
      branch_case as Hbr.
      + run_fp 20%nat (@nil Z) noscr false. finish HR0 HF0. apply frame_mod_refl.
      + run_fp 20%nat (@nil Z) noscr false. finish HR0 HF0. apply frame_mod_refl.
    - pose proof (knA_ok Hc) as HK.
      run_fp 20%nat (@nil Z) noscr false.
      branch_case as Hbr.
      + run_fp 20%nat (@nil Z) noscr false. finish HR0 HF0. apply frame_mod_refl.
      + run_fp 60%nat (@nil Z) noscr true.
        finish HR0 HF0.
        rewrite EQM, <- RS_denot. apply (frame_mod_mem_denot E _ _ RS HLF); [flats_auto | vm_compute; reflexivity].
  Qed.
End CI.

Theorem cicp_Ub_ok : cicp_contract SEGS tags_infoub.
Proof.
  intros data len bs T C FPI regs mem rom ret Hra Hret PRE.
  destruct PRE as (HT & HC & (Hlen & Hbs & Hdnz & Hdata & Hblob) & [ty [Htyr Hty]] &
                   (sz & buf & [Hszr Hsz] & Hbuf & Hsz4 & (Hin1 & _ & Hin2)) & Htal & Ht24 &
                   (_ & _ & HC4 & HCst) & HCD & HCT).
  unfold cell64, cell in Hbuf. unfold cell in Hty, Hsz.
  destruct (cicp_run FPI regs mem rom ret T C data buf ty sz len bs Hra Hret HT HC
              Hlen Hbs Hdnz Hdata Hblob Hty Htyr Hsz Hszr Hbuf Hin1 Hin2 Htal Ht24 HCst HC4 HCD)
    as (st' & Hms & (FPI' & regs' & mem' & -> & Hk1 & Hk2 & Hpost)).
  exists FPI', regs', mem'. split; [exact Hms|]. split; [exact Hk1|]. split; [exact Hk2|]. exact Hpost.
Qed.
End LibCicpUb.

Module LibUsableUb.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsSpec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsLib.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf.SymDriveLB.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveLZ.
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.ev_simpl E ::= ev_simpl_lz E.
#[local] Ltac SymDriveFP.ev_simpl_in E H ::= ev_simpl_in_lz E H.
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.run_fp_with_h HR HF HK fuel stops scr chints keep extra ::= run_fp_with_h_lz HR HF HK fuel stops scr chints keep extra.
#[local] Ltac SymDriveFP.branch_case_with HR HF HK Hc ::= branch_case_with_lz HR HF HK Hc.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SXF. Import SXFS.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

#[local] Abbreviation SEGS := Ubsan.M.loaded_segments.

Section US.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret P : word).

  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis HP : getr regs 10 = P.
  Hypothesis HPal : (bv_unsigned P mod 8 = 0)%Z.
  Hypothesis HP976 : (bv_unsigned P + 976 <= 2 ^ 64)%Z.

  Let E : env := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ [])) (blobs_ev []).

  Definition kn_of (a b c : Z) : list kentry :=
    [KRange (EVar 10) 0 (2^64 - 976);
     KAlign (EVar 10) 8;
     KWord (SA (EVar 10) 966) 1 (ELit a);
     KWord (SA (EVar 10) 964) 1 (ELit b);
     KWord (SA (EVar 10) 965) 1 (ELit c)].

  Lemma kn_of_ok : forall a b c,
    cell8 SEGS mem (bv_unsigned P + 966) a -> cell8 SEGS mem (bv_unsigned P + 964) b ->
    cell8 SEGS mem (bv_unsigned P + 965) c -> know_ok SEGS E mem (kn_of a b c).
  Proof.
    intros a b c [Ra Ca] [Rb Cb] [Rc Cc]. unfold cell in Ca, Cb, Cc.
    unfold kn_of. pose proof (u64_range P).
    unfold know_ok.
    repeat (apply Forall_cons); [..|apply Forall_nil].
    - apply krange_intro; cbn. rewrite HP. lia.
    - apply kalign_intro; [lia|]. cbn. rewrite HP. exact HPal.
    - eapply (kword_intro SEGS E mem (EVar 10) P 966 1 (ELit a) (Z_to_bv 64 a)); cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (EVar 10) P 964 1 (ELit b) (Z_to_bv 64 b)); cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (EVar 10) P 965 1 (ELit c) (Z_to_bv 64 c)); cbn; try lia; auto.
  Qed.

  Definition POST (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
    mem' = mem /\
    exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1)%Z.

  Ltac leaf HR0 HF0 :=
    run_fp 40%nat (@nil Z) noscr false;
    fin_ret;
    lazymatch goal with
    | HR : regs_ok _ ?sr ?R2, HF : fregs_ok _ ?sfr (@fp_regs ?FP2), HK : know_ok _ _ ?M2 _ |- _ =>
      exists FP2, R2, M2;
      split; [regv HR (1%bv:reg); rewrite Hra; reflexivity|];
      split; [exact (regs_same_on E _ _ regs _ abi_kept HR0 HR ltac:(vm_compute; reflexivity))|];
      split; [exact (fregs_same_on E _ _ _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity))|];
      unfold POST; split; [reflexivity | eexists; split; [regv HR (10%bv:reg); reflexivity | lia]]
    end.

  Lemma usable_run : forall a b c,
    (a = 0 \/ a = 1)%Z -> (b = 0 \/ b = 1)%Z -> (c = 0 \/ c = 1)%Z ->
    cell8 SEGS mem (bv_unsigned P + 966) a -> cell8 SEGS mem (bv_unsigned P + 964) b ->
    cell8 SEGS mem (bv_unsigned P + 965) c ->
    runs_to SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x1639c) mem rom)
      (fun st' => exists (FPI' : FPState) regs' mem',
          st' = mkst (FP:=FPI') regs' ret mem' rom /\
          regs_kept abi_kept regs regs' /\
          fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI')) /\
          POST regs' mem').
  Proof.
    intros a b c Ha Hb Hc Ca Cb Cc.
    assert (HR : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    pose proof (kn_of_ok a b c Ca Cb Cc) as HK.
    destruct Ha as [-> | ->]; destruct Hb as [-> | ->]; destruct Hc as [-> | ->]; leaf HR0 HF0.
  Qed.
End US.

Theorem usable_Ub_ok : usable_contract SEGS tags_infoub.
Proof.
  intros P FPI regs mem rom ret Hra Hret PRE.
  destruct PRE as (HP & HPal & HP976 & (b & Cb & Hb) & (c & Cc & Hc) & (a & Ca & Ha)).
  destruct (usable_run FPI regs mem rom ret P Hra Hret HP HPal HP976 a b c Ha Hb Hc Ca Cb Cc)
    as (st' & Hms & (FPI' & regs' & mem' & -> & Hk1 & Hk2 & Hpost)).
  exists FPI', regs', mem'. split; [exact Hms|]. split; [exact Hk1|]. split; [exact Hk2|]. exact Hpost.
Qed.
End LibUsableUb.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require LibReadCurvesS1 LibReadCurvesUb LibReadCurveS1 LibReadCurveUb LibFuzzS1 LibFuzzUb LibParseS1 LibParseUb.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.skcms.iccprofile_info.images Require Import Plain.
From OSSVerify.skcms.iccprofile_info.images Require Import Ubsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec FuzzContract LibDefs LibWP1Spec LibWP2Spec LibCurveSpec LibFPSpec LibTagsSpec. Import LibMemsetS1. Import LibMemsetUb. Import LibRteS1. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibRteUb LibClassifyS1 LibClassifyUb LibEvalCurveS1W LibEvalCurveUb LibFitLinearS1 LibFitLinearUb. Import LibCanonS1. Import LibCanonUb. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require LibReadA2BS1h. Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibReadA2BS1h.LibMftcA2BS1. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require LibReadA2BUbh. Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibReadA2BUbh.LibMftcA2BUb. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require LibReadB2AS1. Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibReadB2AS1.LibMftcB2AS1. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require LibReadB2AUbh. Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibReadB2AUbh.LibMftcB2AUb. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require LibReadA2BS1h. Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibReadA2BS1h.LibItabA2BS1. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require LibReadA2BUbh. Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibReadA2BUbh.LibItabA2BUb. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require LibReadB2AS1. Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibReadB2AS1.LibItabB2AS1. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require LibReadB2AUbh. Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibReadB2AUbh.LibItabB2AUb. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibGetTagS1 LibGetTagUb LibGetIdxS1 LibGetIdxUb. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require LibToXyzS1. Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibToXyzS1.LibTagXyzS1. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require LibToXyzUb. Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibToXyzUb.LibTagXyzUb. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibToXyzS1 LibToXyzUb. Import LibCicpUb. Import LibUsableUb. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibReadCurvesS1 LibReadCurvesUb LibReadCurveS1 LibReadCurveUb LibFuzzS1 LibFuzzUb LibReadA2BS1h LibReadA2BUbh LibReadB2AS1 LibReadB2AUbh LibParseS1 LibParseUb.
Unset Lia Cache.

Section S1.
  #[local] Notation SEGS := Plain.M.loaded_segments.

  Theorem fuzz_contract_src1 : fuzz_contract SEGS src1_abi.
  Proof.
    pose proof (read_curve_S1_ok memset20_src1 classify_S1_ok) as RC.
    pose proof (canonicalize_src1 (fit_linear_src1 eval_curve_src1) memset20_src1) as CAN.
    pose proof (read_curves_S1_ok RC) as RCS.
    pose proof (read_a2b_S1_ok read_mft_common_a2b_S1_ok init_tables_a2b_S1_ok RCS CAN) as A2B.
    pose proof (read_b2a_S1_ok read_mft_common_b2a_S1_ok init_tables_b2a_S1_ok RCS CAN) as B2A.
    pose proof (parse_S1_ok memset976_src1 gettag_S1_ok RC xyzd50_S1_ok A2B B2A) as PARSE.
    exact (fuzz_S1_ok PARSE getidx_S1_ok rte_S1_ok).
  Qed.
End S1.

Section Ub.
  #[local] Notation SEGS := Ubsan.M.loaded_segments.

  Theorem fuzz_contract_infoub : fuzz_contract SEGS infoub_abi.
  Proof.
    pose proof (read_curve_Ub_ok classify_Ub_ok) as RC.
    pose proof (canonicalize_infoub (fit_linear_infoub eval_curve_infoub) memset20_infoub) as CAN.
    pose proof (read_curves_Ub_ok RC) as RCS.
    pose proof (read_a2b_Ub_ok read_mft_common_a2b_Ub_ok init_tables_a2b_Ub_ok RCS CAN) as A2B.
    pose proof (read_b2a_Ub_ok read_mft_common_b2a_Ub_ok init_tables_b2a_Ub_ok RCS CAN) as B2A.
    pose proof (parse_Ub_ok memset976_infoub gettag_Ub_ok RC xyzd50_Ub_ok A2B B2A cicp_Ub_ok usable_Ub_ok) as PARSE.
    exact (fuzz_Ub_ok PARSE getidx_Ub_ok rte_Ub_ok).
  Qed.
End Ub.
