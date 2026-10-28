(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import SReach LazyRestrict LazySR ShapeAlg.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Exec MState.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil}.

Definition ADRV_LIVE : Z := 2^28.
Definition ADRV_CNT  : Z := 2850.

Record asan_driver_laws (H : asr) : Prop := ADL {
  (* [comment removed for export] *)
  adl_sr : forall (Q : config -> Prop) c T,
      as_SR H Q c -> (forall c', Q c' -> ShapeAlg.realizes asegs c' T) -> ShapeAlg.realizes asegs c T;
  (* [comment removed for export] *)
  adl_lazy : forall s, exists L S Zr,
         (forall msF, as_VIS H s msF = restrict L S msF)
      /\ (forall c, as_AKREL H s c -> lzok asegs L S Zr c)
      /\ (forall ms mo ms' mo', as_AKREL H s (mkCfg ms mo) -> lzok asegs L S Zr (mkCfg ms' mo') ->
            m_vmmaps mo' = m_vmmaps mo -> m_vm_lazy mo' = m_vm_lazy mo -> as_AKREL H s (mkCfg ms' mo'));
  (* [comment removed for export] *)
  adl_mpres : forall mo mo', as_MPRES H mo mo' -> m_fs mo' = m_fs mo /\ m_fds mo' = m_fds mo /\ m_halted mo' = m_halted mo;
  (* [comment removed for export] *)
  adl_sb : forall mo mo', same_but_materialized mo mo' -> as_MPRES H mo mo';
  (* [comment removed for export] *)
  adl_live : ADRV_LIVE <= as_LIVE_MAX H /\ ADRV_CNT <= as_LIVE_CNT_MAX H }.

End HCW.

