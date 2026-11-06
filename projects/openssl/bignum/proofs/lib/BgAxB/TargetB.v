(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Cfg Mem. 
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Prog Canon.
From OSSVerify.Proofs.openssl.bignum.lib.AS Require ShapeAlg.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import RT_iface RT_rep D_defs D_libiface I_iodefs X_xdefs.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxState AxSys AxRun.
From OSSVerify.Proofs.openssl.bignum.lib.BgAxBdB Require Import BdBParams BdBStart BdBStartCert.
From OSSVerify.Proofs.openssl.bignum.lib.BgAxB Require Import ArtB StartB.
Require OSSVerify.openssl.bignum.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem target_canon_B_main :
  (forall (argv : list (list byte)) (fs : Fs.Fs) c, valid_argv argv ->
     START RTA OUT_repA ERR_repA XENVA lib_startA argv fs c -> AS.ShapeAlg.realizes bgbsegs c (canonT (argv_Z argv) fs)) ->
  forall en inp, valid_entry (mkImage BDB_SEGS BDB_PC BDB_PH) en inp -> valid_input inp ->
    trace_equiv (bh_traces (Run.run_scfg ncfg (mkImage BDB_SEGS BDB_PC BDB_PH) target_alloc_limit en inp)) (canonT (argv_Z (in_argv inp)) (in_fs inp))
    /\ ~ bh_errors (Run.run_scfg ncfg (mkImage BDB_SEGS BDB_PC BDB_PH) target_alloc_limit en inp).
Proof.
  intros Hmain. exact (target_canon_B RTA OUT_repA ERR_repA XENVA lib_startA fin_mainB fin_mainB_out bridgeB_final bdb_cert_main Hmain).
Qed.

