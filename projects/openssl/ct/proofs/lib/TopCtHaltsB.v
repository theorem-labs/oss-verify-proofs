(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start-up over the run's entry stack; named per-field kernel facts in place of a whole-kernel hypothesis). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Cfg RzCPS.
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require LimTransfer.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prog Canon.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require CanonNoKill.
From OSSVerify.Proofs.openssl.ct.lib.AS Require ShapeHalts.
From OSSVerify.Proofs.openssl.ct.lib Require TopHalts TopCtBoth.
From OSSVerify.Proofs.openssl.ct.lib.CtB Require Import RT_iface RT_rep RT_closed D_defs D_libiface I_iodefs X_xdefs.
From OSSVerify.Proofs.openssl.ct.lib.CtKitB Require ARun EdgesInstA.
From OSSVerify.Proofs.openssl.ct.lib.CtRepB Require CtFuzzStmtA CtFuzzGapA.
From OSSVerify.Proofs.openssl.ct.lib.CtAxB Require ArtB.
From OSSVerify.Proofs.openssl.ct.lib.CtAxBdB Require BdBStartCert BdBStartCertNoRseq.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require ShapeAlgCfg.
From OSSVerify.Proofs.openssl.ct.lib.AxA Require RzBridge.
From OSSVerify.Proofs.openssl.ct.lib.CtAxB Require StartB.
Require OSSVerify.openssl.ct.images.AsanUbsan.
From OSSVerify.Proofs.openssl.ct.lib.CtHarB Require HarStmtA.
From OSSVerify.Proofs.openssl.ct.lib.CtSctB Require SctStmtA SctStmtA2 RtGenStmtA O2iSctStmtB O2iSctListStmtB.
From OSSVerify.Proofs.openssl.ct.lib.CtRepB Require I_strcpyA.
From OSSVerify.Proofs.openssl.ct.lib.CtEncB Require EncStmtA.
From OSSVerify.Proofs.openssl.ct.lib.CtFrameB Require AFrameKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation imgBct := (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs) (only parsing).

Lemma canonT_exits_in : forall argv fs, ShapeHalts.shape_exits_in TopHalts.codes02 (canonT argv fs).
Proof.
  intros argv fs tr Htr. split.
  - intros e Hin Hk. destruct e as [? ? | ? ? | ? ? | sig fs']; try exact Hk.
    exact (CanonNoKill.canonT_nokill argv fs tr sig fs' Htr Hin).
  - intros tr0 code fs' E. exact (TopHalts.canonT_exits02 argv fs tr Htr tr0 code fs' E).
Qed.

Lemma lim_source_le_target : ShippedBudgets.lim_source <= target_alloc_limit.
Proof. unfold ShippedBudgets.lim_source, source_alloc_limit, target_alloc_limit. lia. Qed.

Section OpenObligations.
(* The two kernel fields the ASan start-up witness reads (the auxv's cache words and
   AT_MINSIGSTKSZ) come from the model's own per-field accessors, Run.valid_input_cache_words
   and Run.valid_input_min_sigframe_size.  rseq, aslr, guard, rnd_bits and thp are NOT read
   as fixed values. *)
(* [comment removed for export] *)
Local Notation ARo SP0 PMc FD MST := (CtRepB.CtFuzzGapA.ar_of RTA rta_contracts_all SP0 PMc FD MST).
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma realizes_both_ct : forall en inp, valid_entry imgBct en inp -> valid_input inp ->
  VCommon.ShapeAlgCfg.realizes_cfg AsanUbsan.M.loaded_segments ncfg
    (init_config AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs
       (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) target_alloc_limit inp)
    (canonT (argv_Z (in_argv inp)) (in_fs inp)).
Proof.
  intros en inp He Hi.
  exact (CtAxB.StartB.startB_realizes RTA OUT_repA ERR_repA XENVA lib_startA ArtB.fin_mainB ArtB.fin_mainB_out ArtB.bridgeB_final
           CtAxBdB.BdBStartCert.bdb_cert_main CtAxBdB.BdBStartCertNoRseq.bdb_cert_main_norseq
           TopCtBoth.main_both_ct en inp He Hi
           (valid_input_cache_words inp Hi) (valid_input_min_sigframe_size inp (in_hwcap inp) Hi)).
Qed.

(* [comment removed for export] *)
Theorem must_exit_both_ct_big : forall en inp, valid_entry imgBct en inp -> valid_input inp ->
  must_exit_in_scfg forced_only_cfg TopHalts.codes02 imgBct target_alloc_limit en inp.
Proof.
  intros en inp He Hi. pose proof (realizes_both_ct en inp He Hi) as Hr.
  destruct en as [sp brk mb rnd]. cbn [must_exit_in_scfg en_sp en_brk en_mmap_base en_draw] in *.
  (* LPS 08b1429: the binary carries no vDSO segment of its own *)
  assert (Hvi : vdso_image AsanUbsan.M.loaded_segments = None) by reflexivity.
  apply (AxA.RzBridge.realizes_cfg_must_exit_forced_only_init _ TopHalts.codes02 _ _ _ _ _ _ _ inp _ Hvi Hr).
  - apply canonT_exits_in.
  - reflexivity.
Qed.

(* [comment removed for export] *)
Theorem halts_ct_both :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source [Z_to_bv 64 0; Z_to_bv 64 2] imgBct.
Proof.
  intros en inp He Hi Hbud.
  apply (LimTransfer.lim_transfer_scfg forced_only_cfg _ imgBct en inp ShippedBudgets.lim_source target_alloc_limit lim_source_le_target).
  - exact (must_exit_both_ct_big en inp He Hi).
  - exact Hbud.
Qed.

(* [comment removed for export] *)
Check (halts_ct_both :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    LinuxProcessSemantics.LinuxProcessSem.Run.forced_only_cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    [stdpp.bitvector.definitions.Z_to_bv 64 0; stdpp.bitvector.definitions.Z_to_bv 64 2]
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.openssl.ct.images.AsanUbsan.M.loaded_segments OSSVerify.openssl.ct.images.AsanUbsan.M.init_pc OSSVerify.openssl.ct.images.AsanUbsan.M.phdrs)).
End OpenObligations.
