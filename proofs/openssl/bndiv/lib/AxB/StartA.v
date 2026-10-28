(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Cfg Mem ImageA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Prog Canon.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require ShapeAlg SpinAlg.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Common Require Import RegEqv.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface D_defs. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import SrzEqv.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.VCommon Require ShapeAlg ShapeAlgCfg.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxLin AxState AxSys AxRun AxEntryRel AxModelRel AxFd AxStart.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AxBdB Require Import BdAParams BdAHints BdAStart.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AxA Require Import RzBridge.
Require OssFuzzTheorems.openssl.bndiv.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Notation IMG := (mkImage BDA_SEGS BDA_PC BDA_PH).

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
  forall ρ c, R BDA_SEGS amodel (MR BDA_SEGS fs0 ρ) target_alloc_limit ρ B c ->
  exists c', cfg_eqv c' c /\ START RT OUT_rep ERR_rep XENV LIB (dec_argvB ρ) fs0 c'.
Hypothesis Hcert : bda_cert fin = true.
Hypothesis Hmain : forall (argv : list (list byte)) (fs : Fs.Fs) c, valid_argv argv ->
  START RT OUT_rep ERR_rep XENV LIB argv fs c -> AS.ShapeAlg.realizes bsegs c (canonT (argv_Z argv) fs).

Theorem startA_realizes : forall en inp,
  valid_entry IMG en inp -> valid_input inp ->
  ShapeAlgCfg.realizes_cfg BDA_SEGS ncfg
    (init_config BDA_SEGS BDA_PC BDA_PH (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) target_alloc_limit inp)
    (canonT (argv_Z (in_argv inp)) (in_fs inp)).
Proof.
  intros en inp Hent Hinp.
  apply (bda_startup (fun argv fs c => exists c', cfg_eqv c' c /\ START RT OUT_rep ERR_rep XENV LIB argv fs c') fin Hfin_out) with
    (TT := fun argv => canonT (argv_Z argv) (in_fs inp)); [ | exact Hcert | exact Hinp | exact Hent | ].
  - intros fs0 B HB ρ c HR T Hk. exact (Hk c (Hbridge fs0 B HB ρ c HR)).
  - intros argv c Hva (c' & Heq & HS). exact (realizes_cfg_of_realizes_eqv bsegs c' c _ (Hmain argv (in_fs inp) c' Hva HS) Heq).
Qed.

Theorem target_canon_A : forall en inp,
  valid_entry IMG en inp -> valid_input inp ->
  trace_equiv (bh_traces (Run.run_scfg ncfg IMG target_alloc_limit en inp)) (canonT (argv_Z (in_argv inp)) (in_fs inp))
  /\ ~ bh_errors (Run.run_scfg ncfg IMG target_alloc_limit en inp).
Proof.
  intros en inp Hent Hinp. exact (T_canon_cfg BDA_SEGS BDA_PC BDA_PH target_alloc_limit en inp _ (startA_realizes en inp Hent Hinp)).
Qed.

End TargetA.
