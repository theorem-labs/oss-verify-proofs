(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import SReach LazyRestrict LazySR ShapeAlg.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Exec MState.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AsConst AsIface.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z46Stdlib6ZArith6BinInt1Zhc3powhc3add" s.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil}.

Definition ADRV_LIVE : ltac2:(zQ "10!h9$0") := ltac2:(zQ "20!j4!ja@2$1@2$0+2+i0@2$0+2+hc").
Definition ADRV_CNT : ltac2:(zQ "10!h9$0") := ltac2:(zQ "20!ja!j4@2$0+3@2$0@2$1+2+h9@2$1+2+a").

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

