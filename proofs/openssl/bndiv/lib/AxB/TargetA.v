(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Cfg Mem ImageA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Prog Canon.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require ShapeAlg.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface RT_rep D_defs D_libiface I_iodefs X_xdefs.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxState AxSys AxRun.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AxBdB Require Import BdAParams BdAStart BdAStartCert.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AxB Require Import ArtA StartA.
Require OssFuzzTheorems.openssl.bndiv.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem target_canon_A_main :
  (forall (argv : list (list byte)) (fs : Fs.Fs) c, valid_argv argv ->
     START RTA OUT_repA ERR_repA XENVA lib_startA argv fs c -> AS.ShapeAlg.realizes bsegs c (canonT (argv_Z argv) fs)) ->
  forall en inp, valid_entry (mkImage BDA_SEGS BDA_PC BDA_PH) en inp -> valid_input inp ->
    trace_equiv (bh_traces (Run.run_scfg ncfg (mkImage BDA_SEGS BDA_PC BDA_PH) target_alloc_limit en inp)) (canonT (argv_Z (in_argv inp)) (in_fs inp))
    /\ ~ bh_errors (Run.run_scfg ncfg (mkImage BDA_SEGS BDA_PC BDA_PH) target_alloc_limit en inp).
Proof.
  intros Hmain. exact (target_canon_A RTA OUT_repA ERR_repA XENVA lib_startA fin_mainA fin_mainA_out bridgeA_final bda_cert_main Hmain).
Qed.

(* [comment removed for export] *)
