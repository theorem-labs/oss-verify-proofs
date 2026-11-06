(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Cfg. 
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require LimTransfer.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Prog Canon.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require CanonNoKill.
From OSSVerify.Proofs.openssl.bignum.lib.AS Require ShapeHalts.
From OSSVerify.Proofs.openssl.bignum.lib Require TopHalts TopBignumBoth.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import RT_iface RT_rep D_defs D_libiface I_iodefs X_xdefs.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import LibaBg.
From OSSVerify.Proofs.openssl.bignum.lib.BgAxB Require ArtB.
From OSSVerify.Proofs.openssl.bignum.lib.BgAxBdB Require BdBStartCert.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require ShapeAlgCfg.
From OSSVerify.Proofs.openssl.bignum.lib.AxA Require RzBridge.
From OSSVerify.Proofs.openssl.bignum.lib.BgAxB Require StartB.
Require OSSVerify.openssl.bignum.images.AsanUbsan.
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

Lemma lim_source_le_target : ShippedBudgets.lim_source <= target_alloc_limit.
Proof. unfold ShippedBudgets.lim_source, source_alloc_limit, target_alloc_limit. lia. Qed.

Section Debt.

  Lemma realizes_both : forall en inp, valid_entry imgB en inp -> valid_input inp ->
    VCommon.ShapeAlgCfg.realizes_cfg AsanUbsan.M.loaded_segments ncfg
      (init_config AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs
         (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) target_alloc_limit inp)
      (canonT (argv_Z (in_argv inp)) (in_fs inp)).
  Proof.
    intros en inp He Hi.
    exact (BgAxB.StartB.startB_realizes RTA OUT_repA ERR_repA XENVA lib_startA ArtB.fin_mainB ArtB.fin_mainB_out ArtB.bridgeB_final
             BgAxBdB.BdBStartCert.bdb_cert_main TopBignumBoth.main_both en inp He Hi).
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

  Theorem halts_bignum_both :
    halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source [Z_to_bv 64 0; Z_to_bv 64 2] imgB.
  Proof.
    intros en inp He Hi Hbud.
    apply (LimTransfer.lim_transfer_scfg forced_only_cfg _ imgB en inp ShippedBudgets.lim_source target_alloc_limit lim_source_le_target).
    - exact (must_exit_both_big en inp He Hi).
    - exact Hbud.
  Qed.

  Check (halts_bignum_both :
    LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
      LinuxProcessSemantics.LinuxProcessSem.Run.forced_only_cfg
      LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
      [stdpp.bitvector.definitions.Z_to_bv 64 0; stdpp.bitvector.definitions.Z_to_bv 64 2]
      (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.openssl.bignum.images.AsanUbsan.M.loaded_segments OSSVerify.openssl.bignum.images.AsanUbsan.M.init_pc OSSVerify.openssl.bignum.images.AsanUbsan.M.phdrs)).
End Debt.
