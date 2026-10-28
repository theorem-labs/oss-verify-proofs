(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Uint63.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame SysStep Exec Arr.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Export AsIfaceMemalign.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import W64 ITrie FxInstr FxState FxMem FxExec FxImage I2Image I2Run I2RunA.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.I2A Require Import I2AInv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Sig.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable IMX : fimage.
  Variable A : i2aconsts.

  Definition anode_concl (Q : i2aenv) (st' : i2ast) (msF : machine_state) (mo : Model) : Prop :=
    as_SR H (fun c' => exists rho', I2RA H IMX A Q st' rho' (cfg_ms c') (cfg_model c')) (mkCfg msF mo).

  (* [comment removed for export] *)
  Definition anode_fsmalloc_sig : Prop :=
    forall Q st st' rho msF mo (k : int),
      anode_fsmalloc A k st = Some st' ->
      fsm_class (f_pc (a_F st)) (ka_fsm A) = Some k ->
      cells0_in A (f_mem (a_F st)) ->
      I2RA H IMX A Q st rho msF mo ->
      anode_concl Q st' msF mo.

  (* [comment removed for export] *)
  Definition anode_fsfree_sig (code : itrie finstr) : Prop :=
    forall Q st st' rho msF mo,
      anode_fsfree code st = Some st' ->
      cells0_in A (f_mem (a_F st)) ->
      I2RA H IMX A Q st rho msF mo ->
      anode_concl Q st' msF mo.

  (* [comment removed for export] *)
  Definition anode_memset_sig : Prop :=
    forall Q st st' rho msF mo,
      anode_memset (im_ro IMX) A st = Some st' ->
      f_pc (a_F st) = ka_memset A ->
      cells0_in A (f_mem (a_F st)) ->
      I2RA H IMX A Q st rho msF mo ->
      anode_concl Q st' msF mo.

  (* [comment removed for export] *)
  Definition anode_memcpy_sig : Prop :=
    forall Q st st' rho msF mo,
      anode_memcpy (im_ro IMX) A st = Some st' ->
      (inl (f_pc (a_F st)) (ka_memcpy A) = true \/ f_pc (a_F st) = ka_memmove A) ->
      cells0_in A (f_mem (a_F st)) ->
      I2RA H IMX A Q st rho msF mo ->
      anode_concl Q st' msF mo.

  (* [comment removed for export] *)
  Definition anode_strlen_sig : Prop :=
    forall Q st st' rho msF mo,
      anode_strlen (im_ro IMX) A st = Some st' ->
      f_pc (a_F st) = ka_strlen A ->
      cells0_in A (f_mem (a_F st)) ->
      I2RA H IMX A Q st rho msF mo ->
      anode_concl Q st' msF mo.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition anode_memalign_sig : Prop :=
    forall Q st st' rho msF mo,
      anode_memalign A st = Some st' ->
      f_pc (a_F st) = ka_memalign A ->
      cells0_in A (f_mem (a_F st)) ->
      I2RA H IMX A Q st rho msF mo ->
      anode_concl Q st' msF mo.
End Sig.
