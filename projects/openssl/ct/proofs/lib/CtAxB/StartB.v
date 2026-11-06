(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Cfg Mem. 
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prog Canon.
From OSSVerify.Proofs.openssl.ct.lib.AS Require ShapeAlg SpinAlg.
From OSSVerify.Proofs.openssl.ct.lib.Common Require Import RegEqv.
From OSSVerify.Proofs.openssl.ct.lib.A Require Import SrzEqv.   (* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.CtB Require Import RT_iface D_defs.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxLin AxState AxSys AxRun AxEntryRel AxModelRel AxFd AxStart.
From OSSVerify.Proofs.openssl.ct.lib.CtAxBdB Require Import BdBParams BdBHints BdBStart.
From OSSVerify.Proofs.openssl.ct.lib.AxA Require Import RzBridge.
Require OSSVerify.openssl.ct.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Notation IMG := (mkImage BDB_SEGS BDB_PC BDB_PH).

Section TargetA.
(* [comment removed for export] *)
Variable RT : rt_sig.
Variable OUT_rep : Stdio.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable XENV : mem -> Prop.
Variable LIB : mem -> Prop.

Variable fin : AST -> bool.
Hypothesis Hfin_out : forall B, fin B = true -> am_out (a_model B) = [].
Hypothesis Hbridge : forall (fs0 : Fs.Fs) (B : AST), fin B = true ->
  forall ρ c, R BDB_SEGS amodel (MR BDB_SEGS fs0 ρ) target_alloc_limit ρ B c ->
  exists c', cfg_eqv c' c /\ START RT OUT_rep ERR_rep XENV LIB (dec_argvB ρ) fs0 c'.
Hypothesis Hcert : bdb_cert fin = true.
Hypothesis Hmain : forall (argv : list (list byte)) (fs : Fs.Fs) c, valid_argv argv ->
  START RT OUT_rep ERR_rep XENV LIB argv fs c -> AS.ShapeAlg.realizes ctbsegs c (canonT (argv_Z argv) fs).

Theorem startB_realizes : forall en inp,
  valid_entry IMG en inp -> valid_input inp ->
  ShapeAlgCfg.realizes_cfg BDB_SEGS ncfg
    (init_config BDB_SEGS BDB_PC BDB_PH (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) target_alloc_limit inp)
    (canonT (argv_Z (in_argv inp)) (in_fs inp)).
Proof.
  intros en inp Hent Hinp.
  apply (bdb_startup (fun argv fs c => exists c', cfg_eqv c' c /\ START RT OUT_rep ERR_rep XENV LIB argv fs c') fin Hfin_out) with
    (TT := fun argv => canonT (argv_Z argv) (in_fs inp)); [ | exact Hcert | exact Hinp | exact Hent | ].
  - intros fs0 B HB ρ c HR T Hk. exact (Hk c (Hbridge fs0 B HB ρ c HR)).
  - intros argv c Hva (c' & Heq & HS). exact (realizes_cfg_of_realizes_eqv ctbsegs c' c _ (Hmain argv (in_fs inp) c' Hva HS) Heq).
Qed.

Theorem target_canon_B : forall en inp,
  valid_entry IMG en inp -> valid_input inp ->
  trace_equiv (bh_traces (Run.run_scfg ncfg IMG target_alloc_limit en inp)) (canonT (argv_Z (in_argv inp)) (in_fs inp))
  /\ ~ bh_errors (Run.run_scfg ncfg IMG target_alloc_limit en inp).
Proof.
  intros en inp Hent Hinp. exact (T_canon_cfg BDB_SEGS BDB_PC BDB_PH target_alloc_limit en inp _ (startB_realizes en inp Hent Hinp)).
Qed.

End TargetA.
