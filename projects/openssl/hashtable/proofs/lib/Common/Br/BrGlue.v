(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Run.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cfg Require Import ShapeAlgBase ShapeCfg NodesCfg LedgerCfg AllocCfg.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxRn FxHandoff FxDrive.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import
  PropExec AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore CxPlan CxPlanSound.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Br Require Import BrEnv BrMem BrPure BrLedger BrKeep BrMain.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Glue.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.
Variable A : CAP.atable.
Variable Lim : Z.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Variable ISP : Z.
Variable FS0 : Fs.Fs.
Variable CS : CAP.acs.
Variable TS : AX2.env -> Fs.Fs -> TSet.
Hypothesis TAIL : forall E R FULL model,
  CXS.cs_ok segs A Lim SINV argH ISP FS0 E CS R FULL model ->
  realizes_cfg cfg segs (mkCfg (mkst R (Z_to_bv 64 (CAP.pc CS)) FULL (seg_rom segs)) model) (TS E (m_fs model)).

Theorem bridge_realizes : forall E ms m,
  ms = mkst (ms_regs ms) (Z_to_bv 64 (CAP.pc CS)) (ms_mem ms) (seg_rom segs)
  /\ CXS.cs_ok segs A Lim SINV argH ISP FS0 E CS (ms_regs ms) (ms_mem ms) m ->
  realizes_cfg cfg segs (mkCfg ms m) (TS E (m_fs m)).
Proof. intros E ms m [Hms HC]. rewrite Hms. exact (TAIL E _ _ m HC). Qed.
End Glue.

(* [comment removed for export] *)
Section AddKn.
Variable segs : list Segment.
Variable A : CAP.atable.
Variable Lim : Z.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Variable ISP : Z.
Variable FS0 : Fs.Fs.

Theorem cs_ok_add_kn : forall E cs R FULL model ks,
  CXS.cs_ok segs A Lim SINV argH ISP FS0 E cs R FULL model ->
  Forall (AX2S.kentry_ok segs E (CXS.Mr A argH E cs model FULL)) ks ->
  CXS.cs_ok segs A Lim SINV argH ISP FS0 E (CAP.add_kn cs ks) R FULL model.
Proof.
  intros E cs R FULL model ks HC Hks. destruct HC.
  constructor; try assumption.
  - reflexivity.
  - unfold AX2S.know_ok in *. change (CAP.kn (CAP.add_kn cs ks)) with (ks ++ CAP.kn cs).
    apply Forall_app. split; assumption.
Qed.
End AddKn.

