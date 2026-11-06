(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import ShapeAlg DivergeSim SpinAlg SpinAlgX ShapeEF KillFree VmLimitFrame Spec BigintSpec HeapIface LibIface LibIfaceFp LibIfaceFpW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import HalfOk SpecG PmPhiX Pm6DrvMainW Pm6HeapBridgeW Pm6DrvLibL Pm6DrvG.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Bridge Require Import PmHeapInst6.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AsanAcct HeapIfaceA PmHeapIfaceA IcptIfaceA PmIcptIfaceA PmLibIfaceA PmLibIfaceAW Pm5ArtIfaceInst Pm5ArtIfaceInstX
  Pm5DrvLibL Pm5DrvLibLW Pm5DrvLibInit Pm5DrvMain Pm5MainPhaseAW Pm5DrvC Pm5DrvD PmXbothFinalW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Pm6DrvC Pm6DrvD.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require PropExec.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PmXbothBaseW.
Abbreviation IMG_xsrc := (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs).
Abbreviation IMG_xboth := (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).

Lemma cfg0_eq : PmPhiX.cfg0 = PmXbothFinalW.cfg0.  Proof. reflexivity. Qed.
Lemma lim_source_eq : SanitizerBudgets.lim_source = 2 ^ 31.  Proof. reflexivity. Qed.
Lemma lim_source_le : SanitizerBudgets.lim_source <= 2 ^ 31.  Proof. rewrite lim_source_eq. lia. Qed.

(* [comment removed for export] *)
Lemma payload_eq : forall data, Pm6DrvD.payload data = Pm5DrvD.payloadA data.
Proof. intros data. reflexivity. Qed.
Lemma hdr_okD_of_A : forall data, Z.of_nat (length data) < 67108864 -> (6 <= length data)%nat -> 6 + Pm5DrvC.CFGA data <= Z.of_nat (length data) -> SpecG.hdr_okD data.
Proof.
  intros data H1 H2 H3. unfold SpecG.hdr_okD. change (SpecG.cfgD data) with (Pm5DrvC.CFGA data).
  pose proof (Z.mod_pos_bound (bv_unsigned (nth 0 data (Z_to_bv 8 0)) + 256 * bv_unsigned (nth 1 data (Z_to_bv 8 0))) 32768 ltac:(lia)) as HC.
  change ((bv_unsigned (nth 0 data (Z_to_bv 8 0)) + 256 * bv_unsigned (nth 1 data (Z_to_bv 8 0))) mod 32768) with (Pm5DrvC.CFGA data) in HC.
  split; [exact H1 | split; [exact H2 | lia]].
Qed.

Section FPX_1.
#[local] Existing Instance PropExec.fx0.
Section Glue.
  (* [comment removed for export] *)
  Variable PHI : list byte -> Prop.
  (* [comment removed for export] *)
  Variable Lay0F : word -> lib_layout.
  Variable LS0F : word -> lib_statics.
  Hypothesis DLL0 : forall sp, valid_sp sp -> Pm6DrvLibL.drv_lib_layout (Lay0F sp) (PmHeapInst6.L0 (bv_unsigned sp)).
  Hypothesis LIOKW0 : forall sp, valid_sp sp -> lib_iface_ok_fpw (Lay0F sp) PmPhiX.cfg0 (PmHeapInst6.HI0 (bv_unsigned sp)) (LS0F sp) PHI.
  Hypothesis LX0 : forall sp, valid_sp sp -> Pm6DrvLibL.lib_exit_ok (LS0F sp).
  Hypothesis BUD0 : forall sp n, valid_sp sp -> 0 <= n < 67108864 ->
    Pm6DrvG.cred (PmHeapInst6.L0 (bv_unsigned sp))
      (PmHeapInst6.KPM + 4 * fst (ll_credit (Lay0F sp) n)) (n + PmHeapInst6.BOV + 4 * snd (ll_credit (Lay0F sp) n)) 0
      (debit (PmHeapInst6.L0 (bv_unsigned sp)) (PmHeapInst6.K0, PmHeapInst6.B0) 65536).
  (* [comment removed for export] *)
  Variable LayA : lib_layoutA.
  Variable LStA : asan_run -> lib_statics.
  Hypothesis DLLA : drv_lib_layoutA LayA art_L.
  Hypothesis DLCA : drv_lib_cellsA LayA.
  Hypothesis BUDA : drv_budgetA art_L LayA PmXbothFinalW.BUDGET0.
  Hypothesis LIBA : lib_ok_stmtW PmXbothFinalW.cfg0 art_L art_LX art_C PmXbothFinalW.art_IL PmXbothFinalW.art_ILX LayA LStA PHI.

  (* [comment removed for export] *)
  Lemma phi_of_premise : forall sp brk mb rnd inp,
    valid_entry IMG_xsrc (mkEntry sp brk mb rnd) inp -> valid_input_abort inp ->
    ~ run_scfg_budget_refused PmPhiX.cfg0 IMG_xsrc SanitizerBudgets.lim_source (mkEntry sp brk mb rnd) inp ->
    forall a0 path data, in_argv inp = [a0; path] -> (length path < 4096)%nat -> path <> [] -> path <> dot_path ->
      fs_lookup (in_fs inp) path = Some data -> SpecG.hdr_okD data -> PHI (Pm6DrvD.payload data).
  Proof.
    intros sp brk mb rnd inp Hen Hvalid Hwb a0 path data Hargv Hlen Hne Hnd Hlk Hhdr.
    exact (PmPhiX.phi_xsrc_at Lay0F LS0F PHI DLL0 LIOKW0 LX0 BUD0 SanitizerBudgets.lim_source sp brk mb rnd inp a0 path data lim_source_le Hen Hvalid Hwb
             Hargv Hlen Hne Hnd Hlk Hhdr).
  Qed.

  (* [comment removed for export] *)
  Theorem xsrc_half : forall en_s inp,
    valid_entry IMG_xsrc en_s inp -> valid_input_abort inp -> ~ run_scfg_budget_refused PmPhiX.cfg0 IMG_xsrc SanitizerBudgets.lim_source en_s inp ->
    half_ok PmPhiX.cfg0 IMG_xsrc SanitizerBudgets.lim_source en_s inp (spec (in_argv inp) (in_fs inp)).
  Proof.
    intros [sp brk mb rnd] inp Hen Hvalid Hwb.
    apply half_ok_of_srealizes.
    - apply (srz_conseq _ _ _ (specG (fun d => PHI (Pm6DrvD.payload d)) (in_argv inp) (in_fs inp))).
      + exact (PmPhiX.srealizes_specG_init Lay0F LS0F PHI DLL0 LIOKW0 LX0 BUD0 SanitizerBudgets.lim_source sp brk mb rnd inp lim_source_le Hen Hvalid).
      + apply specG_eq. intros a0 path data Hargv Hlen Hne Hnd Hlk Hhdr.
        exact (phi_of_premise sp brk mb rnd inp Hen Hvalid Hwb a0 path data Hargv Hlen Hne Hnd Hlk Hhdr).
    - apply Safe_init_within_budget. exact Hwb.
    - apply kill_free_spec.
  Qed.

  (* [comment removed for export] *)
  Theorem xboth_half : forall en_s en_t inp,
    valid_entry IMG_xsrc en_s inp -> valid_entry IMG_xboth en_t inp -> valid_input_abort inp ->
    ~ run_scfg_budget_refused PmPhiX.cfg0 IMG_xsrc SanitizerBudgets.lim_source en_s inp ->
    half_ok PmXbothFinalW.cfg0 IMG_xboth SanitizerBudgets.lim_target en_t inp (spec (in_argv inp) (in_fs inp)).
  Proof.
    intros [ssp sbrk smb srnd] [sp brk mb rnd] inp Hens Hent Hvalid Hwb.
    pose proof (valid_input_abort_va_size _ Hvalid) as Hsv48.
    pose proof Hent as Hent'. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent'. destruct Hent' as [Hsp [Hbrk [Hmb Hfit]]].
    pose proof Hvalid as (Hargv & Henvp & Hfs & _ & Hcreds & _ & _ & Hhw & _).
    apply half_ok_of_srealizes.
    - apply (pm_xboth_tgt PHI LayA LStA DLLA DLCA BUDA LIBA sp brk mb rnd inp Hsp Hbrk Hmb Hfit Hargv Henvp Hfs Hcreds Hhw Hsv48).
      intros a0s path Hinargv. unfold phi_okD. intros Hlen Hne Hnd data Hlk H1 H2 H3.
      rewrite <- payload_eq.
      exact (phi_of_premise ssp sbrk smb srnd inp Hens Hvalid Hwb a0s path data Hinargv Hlen Hne Hnd Hlk (hdr_okD_of_A data H1 H2 H3)).
    - apply Safe_init_big. exact nbr_limit_target.
    - apply kill_free_spec.
  Qed.

  (* [comment removed for export] *)
  Theorem xboth_base :
    strong_universal_error_free_T_scfg_budgets_abort PmXbothFinalW.cfg0 SanitizerBudgets.lim_source SanitizerBudgets.lim_target IMG_xsrc IMG_xboth.
  Proof.
    apply (base_abort_of_halves_dep PmXbothFinalW.cfg0 _ _ IMG_xsrc IMG_xboth (fun inp => spec (in_argv inp) (in_fs inp))).
    - exact xsrc_half.
    - exact xboth_half.
  Qed.
End Glue.
End FPX_1.
End PmXbothBaseW.
