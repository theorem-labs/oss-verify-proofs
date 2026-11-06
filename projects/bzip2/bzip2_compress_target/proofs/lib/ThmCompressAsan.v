(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.bzip2.bzip2_compress_target.images Require Import Plain.
From OSSVerify.bzip2.bzip2_compress_target.images Require Asan AsanUbsan.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW StartupRnd ShapeAlg Spec04.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocIface AllocCover AllocLayout0 AllocDcv S0H_Iface S0H_Cover S0H_Dcv.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams S0F_glueB2B.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import S0HarnStmt S0B2BCStmt S0B2BDStmt S0HarnBody S0B2BC ThmCompressUbsan.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Common.BudgetBridge Require Import LimStep.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition S0img : Image :=
  mkImage Plain.M.loaded_segments Plain.M.init_pc
          Plain.M.phdrs.
Definition A0img : Image :=
  mkImage Asan.M.loaded_segments Asan.M.init_pc
          Asan.M.phdrs.
Definition B0img : Image :=
  mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc
          AsanUbsan.M.phdrs.

(* [comment removed for export] *)
Definition tgt_side04 (timg : Image) : Prop :=
  forall en inp, valid_entry timg en inp -> valid_input inp ->
    error_free (run_scfg (alloc_only_cfg false) timg target_alloc_limit en inp)
    /\ trace_equiv (bh_traces (run_scfg (alloc_only_cfg false) timg target_alloc_limit en inp)) (spec04 (in_argv inp) (in_fs inp)).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma harn_S0 : forall (ACEIL__ : ACeil) (RUNW__ : RunW), harn_spec S0_alloc S0_cover S0I.
Proof.
  intros AC RW. apply (harn_s0 S0_alloc S0_cover S0_dcv S0_freev).
  - intros BZP. exact (@b2bC_s0 BZP AC RW S0_alloc S0_cover).
  - exact (S0F_b2bD S0_alloc S0_cover S0_dcv S0_freev).
Qed.

Lemma s0_side04 : forall en inp, valid_entry S0img en inp -> valid_input inp ->
  error_free (run_scfg (alloc_only_cfg false) S0img source_alloc_limit en inp)
  /\ trace_equiv (bh_traces (run_scfg (alloc_only_cfg false) S0img source_alloc_limit en inp)) (spec04 (in_argv inp) (in_fs inp)).
Proof.
  intros [rsp rbrk rmb rrnd] inp Hens Hvalid.
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens.
  destruct Hens as [Hrsp [Hrbrk [Hrmb Hrfit]]]. destruct Hvalid as [Hargv [Henvp [Hfs Hrest]]].
  assert (R : realizes s0segs
                (init_config s0segs Plain.M.init_pc Plain.M.phdrs
                             rsp rbrk rmb rrnd source_alloc_limit inp)
                (spec04 (in_argv inp) (in_fs inp))).
  { apply (@s0_realizes04 (aceil_of_sp (bv_unsigned rsp)) (mkRunW (canary_w rrnd) (secret_word rrnd))
             (harn_S0 _ _) rsp rbrk rmb rrnd inp Hrsp Hrbrk Hrfit Hargv Henvp Hfs).
    - rewrite (aceil_of_sp_valid rsp Hrsp). reflexivity.
    - reflexivity.
    - reflexivity. }
  split.
  - cbn. exact (realizes_no_error s0segs _ _ R).
  - intro tr. cbn. exact (realizes_obs_iff s0segs _ _ R tr).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sanitizer_le_source : (sanitizer_source_limit <= source_alloc_limit)%Z.
Proof. unfold sanitizer_source_limit, source_alloc_limit. apply Z.leb_le. reflexivity. Qed.

Lemma s0_side_san : forall en inp, valid_entry S0img en inp -> valid_input inp ->
  ~ run_scfg_budget_refused (alloc_only_cfg false) S0img sanitizer_source_limit en inp ->
  error_free (run_scfg (alloc_only_cfg false) S0img sanitizer_source_limit en inp)
  /\ trace_equiv (bh_traces (run_scfg (alloc_only_cfg false) S0img sanitizer_source_limit en inp)) (spec04 (in_argv inp) (in_fs inp)).
Proof.
  intros en inp He Hi NB. destruct (s0_side04 en inp He Hi) as [EF TR]. split.
  - exact (proj2 (run_scfg_relimit_error_free (alloc_only_cfg false) S0img en inp _ _ sanitizer_le_source NB) EF).
  - intro tr. rewrite (run_scfg_relimit_traces (alloc_only_cfg false) S0img en inp _ _ sanitizer_le_source NB tr). exact (TR tr).
Qed.

(* [comment removed for export] *)
Theorem join_san : forall timg, tgt_side04 timg ->
  strong_universal_error_free_T_scfg_budgets (alloc_only_cfg false)
    SanitizerBudgets.lim_source SanitizerBudgets.lim_target S0img timg.
Proof.
  intros timg HT enS enT inp HeS HeT Hi HB.
  destruct (s0_side_san enS inp HeS Hi HB) as [ES TS]. destruct (HT enT inp HeT Hi) as [ET TT].
  split; [exact ES|]. split; [exact ET|].
  intro tr. rewrite (TS tr). symmetry. exact (TT tr).
Qed.

Section Targets.
  Hypothesis TGT_asan : tgt_side04 A0img.
  Hypothesis TGT_both : tgt_side04 B0img.

  Theorem compress_asan_san :
    strong_universal_error_free_T_scfg_budgets (alloc_only_cfg false)
      SanitizerBudgets.lim_source SanitizerBudgets.lim_target S0img A0img.
  Proof. exact (join_san A0img TGT_asan). Qed.
  Theorem compress_both_san :
    strong_universal_error_free_T_scfg_budgets (alloc_only_cfg false)
      SanitizerBudgets.lim_source SanitizerBudgets.lim_target S0img B0img.
  Proof. exact (join_san B0img TGT_both). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
End Targets.
