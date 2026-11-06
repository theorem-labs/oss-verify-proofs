(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from projects/openssl/bndiv/proofs/lib/TopBndivHaltsA.v at 874e3397a35 and moved to the ASan+UBSan build: the AsanUbsan image, the AxB, AxBdB and B modules, TopBndivBoth.main_both, and the names imgB, realizes_both, must_exit_both_big and halts_bndiv_both. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Cfg ImageA.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require LimTransfer.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prog Canon.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require CanonNoKill.
From OSSVerify.Proofs.openssl.bndiv.lib.AS Require ShapeHalts.
From OSSVerify.Proofs.openssl.bndiv.lib Require TopHalts TopBndivBoth.
From OSSVerify.Proofs.openssl.bndiv.lib.B Require Import RT_iface RT_rep D_defs D_libiface I_iodefs X_xdefs.
From OSSVerify.Proofs.openssl.bndiv.lib.AxB Require ArtA.
From OSSVerify.Proofs.openssl.bndiv.lib.AxBdB Require BdAStartCert.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require ShapeAlgCfg.
From OSSVerify.Proofs.openssl.bndiv.lib.AxA Require RzBridge.
From OSSVerify.Proofs.openssl.bndiv.lib.AxB Require StartA.
Require OSSVerify.openssl.bndiv.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation imgB := (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs) (only parsing).

Lemma canonT_exits_in : forall argv fs, ShapeHalts.shape_exits_in TopHalts.codes02 (canonT argv fs).
Proof.
  intros argv fs tr Htr. split.
  - intros e Hin Hk. destruct e as [? ? | ? ? | ? ? | sig fs']; try exact Hk.
    exact (CanonNoKill.canonT_nokill argv fs tr sig fs' Htr Hin).
  - intros tr0 code fs' E. exact (TopHalts.canonT_exits02 argv fs tr Htr tr0 code fs' E).
Qed.

Lemma realizes_both : forall en inp, valid_entry imgB en inp -> valid_input inp ->
  VCommon.ShapeAlgCfg.realizes_cfg AsanUbsan.M.loaded_segments ncfg
    (init_config AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs
       (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) target_alloc_limit inp)
    (canonT (argv_Z (in_argv inp)) (in_fs inp)).
Proof.
  intros en inp He Hi.
  exact (AxB.StartA.startA_realizes RTA OUT_repA ERR_repA XENVA lib_startA ArtA.fin_mainA ArtA.fin_mainA_out ArtA.bridgeA_final
           AxBdB.BdAStartCert.bda_cert_main TopBndivBoth.main_both en inp He Hi).
Qed.

Theorem must_exit_both_big : forall en inp, valid_entry imgB en inp -> valid_input inp ->
  must_exit_in_scfg forced_only_cfg TopHalts.codes02 imgB target_alloc_limit en inp.
Proof.
  intros en inp He Hi. pose proof (realizes_both en inp He Hi) as Hr.
  destruct en as [sp brk mb rnd]. cbn [must_exit_in_scfg en_sp en_brk en_mmap_base en_draw] in *.
  apply (AxA.RzBridge.realizes_cfg_must_exit_forced_only _ TopHalts.codes02 _ _ Hr).
  - apply canonT_exits_in.
  - reflexivity.
Qed.

Lemma lim_source_le_target : ShippedBudgets.lim_source <= target_alloc_limit.
Proof. unfold ShippedBudgets.lim_source, source_alloc_limit, target_alloc_limit. lia. Qed.

Theorem halts_bndiv_both :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source [Z_to_bv 64 0; Z_to_bv 64 2] imgB.
Proof.
  intros en inp He Hi Hbud.
  apply (LimTransfer.lim_transfer_scfg forced_only_cfg _ imgB en inp ShippedBudgets.lim_source target_alloc_limit lim_source_le_target).
  - exact (must_exit_both_big en inp He Hi).
  - exact Hbud.
Qed.

Check (halts_bndiv_both :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    LinuxProcessSemantics.LinuxProcessSem.Run.forced_only_cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    [stdpp.bitvector.definitions.Z_to_bv 64 0; stdpp.bitvector.definitions.Z_to_bv 64 2]
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.openssl.bndiv.images.AsanUbsan.M.loaded_segments OSSVerify.openssl.bndiv.images.AsanUbsan.M.init_pc OSSVerify.openssl.bndiv.images.AsanUbsan.M.phdrs)).
