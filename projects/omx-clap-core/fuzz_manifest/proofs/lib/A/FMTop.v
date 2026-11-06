(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v and lib/Halts_tfib.v for fuzz_manifest, in the form proofs/libreac/fuzz_grant/lib/A/AsanTop.v (a working branch) gives them: the plain side is fuzz_manifest's proved realization (FMPlain.v), the halting corollary takes srealizes, module paths changed. *)
(* fuzz_manifest's two ASan statements from the ASan side TFIB_T (FMTfibT.v):
   - asan_agrees: shape_strong_equiv_efs_relim (Reusable/YM09.v) over the plain build's proved realization of SPECX
     at 2^34 (FMPlain.fm_plain_rz, at ag_shape checksum_shape), the statement's plain budget premise (which also
     discharges the plain realization's cuts, lib/A/RelimCut.v), TFIB_T, and t_eq of the two SPECX (same LIBK);
   - asan_halts: halts_budgets_of_srealizes (Reusable/HaltsKitB.v) over TFIB_T, with exits 0 and 2 from
     ZTraceSpec.checksum_SPECX_exits_allowed. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.omx_clap_core.fuzz_manifest Require Statements Images.
From OSSVerify.omx_clap_core.fuzz_manifest.images Require Plain Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
  YK11 YK15 YK18 YM02 YM09 YO05 YO09 YO06 HaltsKitB.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest Require Import lib.Agree lib.AgreeShape lib.ZTraceSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMTfibT FMPlain.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

Lemma wr_congr_fm : forall ch bs T T', t_eq T T' -> t_eq (wr ch bs T) (wr ch bs T').
Proof.
  intros ch bs T T' H tr. unfold wr, t_emit.
  split; (intros [Hp | (tr' & -> & HT)]; [left; exact Hp | right; exists tr'; split; [reflexivity | apply H; exact HT]]).
Qed.

(* SPECX depends on the library shape only through LIBK. The proof goes by the structure of SPECX: a plain
   conversion check between the two SPECX would evaluate the driver's model tree. *)
Section LIBKeq.
Variables L1 L2 : lib_shape.
Hypothesis HL : forall pl fs K, @LIBK L1 pl fs K = @LIBK L2 pl fs K.

Lemma lib_iter_LIBK : forall pl j K fs, t_eq (lib_iter (LS:=L1) pl j K fs) (lib_iter (LS:=L2) pl j K fs).
Proof.
  intros pl j. induction j as [|j IH]; intros K fs; cbn [lib_iter]; [apply t_eq_refl|].
  rewrite HL. apply (@LIBK_ext L2). intros l. apply IH.
Qed.

Lemma run_shape_LIBK : forall pl k fs, t_eq (run_shape (LS:=L1) pl k fs) (run_shape (LS:=L2) pl k fs).
Proof.
  intros pl [|k] fs; cbn [run_shape]; [apply t_eq_refl|].
  rewrite HL. apply (@LIBK_ext L2). intros l. apply wr_congr_fm. apply lib_iter_LIBK.
Qed.

Lemma SPECX_LIBK : forall inp, t_eq (SPECX (LS:=L1) inp) (SPECX (LS:=L2) inp).
Proof.
  intros inp. unfold SPECX, SPECX_args.
  destruct (in_argv inp) as [|a0 [|p [|x l]]]; lazy beta iota; [apply t_eq_refl | apply t_eq_refl | | apply t_eq_refl].
  destruct (classify_open p (in_fs inp)) as [| |data]; lazy beta iota; [apply t_eq_refl | apply t_eq_refl |].
  apply t_alt2_congr; [apply t_eq_refl|].
  unfold SPECX_loaded. apply tset_congr. intros [d s]. unfold leaf_shapeX. cbn [fst].
  destruct d; lazy beta iota;
    lazymatch goal with
    | |- t_eq (run_shape _ _ _) _ => apply run_shape_LIBK
    | |- _ => apply t_eq_refl
    end.
Qed.
End LIBKeq.

(* The plain proof's SPECX (ag_shape checksum_shape) and TFIB_T's (checksum_shape) have the same LIBK. *)
Lemma SPECX_ag_t_eq : forall inp, t_eq (SPECX (LS:=ag_shape checksum_shape) inp) (SPECX (LS:=checksum_shape) inp).
Proof. exact (SPECX_LIBK (ag_shape checksum_shape) checksum_shape (ag_LIBK checksum_shape)). Qed.

Lemma SPECX_checksum_shape_ok : forall inp, shape_ok Exits.ok_or_refused (SPECX (LS:=checksum_shape) inp).
Proof. intros inp. exact (checksum_SPECX_exits_allowed checksum_permitted inp). Qed.

Lemma asan_lim_source_le : SanitizerBudgets.lim_source <= ShippedBudgets.lim_source.
Proof. unfold SanitizerBudgets.lim_source, sanitizer_source_limit, ShippedBudgets.lim_source, source_alloc_limit. cbn. lia. Qed.

Lemma lim_source_le_target : ShippedBudgets.lim_source <= target_alloc_limit.
Proof. unfold ShippedBudgets.lim_source, source_alloc_limit, target_alloc_limit. cbn. lia. Qed.

Section a.
Hypothesis TFIB : TFIB_T.

Theorem fm_asan_agrees : Statements.asan_agrees.
Proof.
  unfold Statements.asan_agrees, agrees_in.
  intros en_s [sp' brk' mb' rnd'] inp Hens Hent Hinp SWB.
  pose proof (fm_plain_rz en_s inp Hens Hinp) as HP.
  destruct en_s as [sp brk mb rnd].
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  unfold Images.asan in Hent.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent. destruct Hent as [Hsp' [Hbrk' [Hmb' Hfit']]].
  exact (shape_strong_equiv_efs_relim SanitizerBudgets.lim_source ShippedBudgets.lim_source SanitizerBudgets.lim_target
    Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mb rnd
    tfibsegs0 Asan.M.init_pc Asan.M.phdrs sp' brk' mb' rnd'
    (SPECX (LS:=ag_shape checksum_shape) inp) (SPECX (LS:=checksum_shape) inp) inp
    asan_lim_source_le SWB HP (TFIB sp' brk' mb' rnd' inp Hsp' Hbrk' Hmb' Hfit' Hinp) (SPECX_ag_t_eq inp)).
Qed.

Theorem fm_asan_halts : Statements.asan_halts.
Proof.
  unfold Statements.asan_halts, Images.asan.
  change (halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source Exits.ok_or_refused
    (mkImage tfibsegs0 Asan.M.init_pc Asan.M.phdrs)).
  apply (halts_budgets_of_srealizes forced_only_cfg Exits.ok_or_refused tfibsegs0 Asan.M.init_pc Asan.M.phdrs
    target_alloc_limit ShippedBudgets.lim_source lim_source_le_target (forced_only_cfg_least _)).
  intros sp brk mb rnd inp Hen Hinp. exists (SPECX (LS:=checksum_shape) inp). split.
  - pose proof (valid_input_va_size _ Hinp) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
    exact (TFIB sp brk mb rnd inp Hsp Hbrk Hmb Hfit Hinp).
  - exact (SPECX_checksum_shape_ok inp).
Qed.
End a.

Theorem fm_asan_agrees_of_tfib : TFIB_T -> Statements.asan_agrees.
Proof. exact fm_asan_agrees. Qed.

Theorem fm_asan_halts_of_tfib : TFIB_T -> Statements.asan_halts.
Proof. exact fm_asan_halts. Qed.
