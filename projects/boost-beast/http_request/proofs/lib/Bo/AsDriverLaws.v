(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import SReach LazyRestrict LazySR ShapeAlg.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Exec MState.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil}.

Definition ADRV_LIVE : Z := 2^27 + 2^26 + 2^30.
Definition ADRV_CNT  : Z := 3 + 2100.

Record asan_driver_laws (H : asr) : Prop := ADL {
  (* [comment removed for export] *)
  adl_sr : forall (Q : config -> Prop) c T,
      as_SR H Q c -> (forall c', Q c' -> ShapeAlg.realizes bsegs c' T) -> ShapeAlg.realizes bsegs c T;
  (* [comment removed for export] *)
  adl_lazy : forall s, exists L S Zr,
         (forall msF, as_VIS H s msF = restrict L S msF)
      /\ (forall c, as_AKREL H s c -> lzok bsegs L S Zr c)
      /\ (forall ms mo ms' mo', as_AKREL H s (mkCfg ms mo) -> lzok bsegs L S Zr (mkCfg ms' mo') ->
            m_vmmaps mo' = m_vmmaps mo -> m_vm_lazy mo' = m_vm_lazy mo -> as_AKREL H s (mkCfg ms' mo'));
  (* [comment removed for export] *)
  adl_mpres : forall mo mo', as_MPRES H mo mo' -> m_fs mo' = m_fs mo /\ m_fds mo' = m_fds mo /\ m_halted mo' = m_halted mo;
  (* [comment removed for export] *)
  adl_sb : forall mo mo', same_but_materialized mo mo' -> as_MPRES H mo mo';
  (* A write to a channel needs [m_channel_reader mo = true]
     (Bo/AsDrvIO.v:61), and [adl_mpres] carries no reader fact, so a step model gets the
     launch's reader through this law.  The instance's [as_MPRES] is [SecLazy.nonvm_same],
     which equates [m_proc]; [m_channel_reader] is a projection of [m_proc].  Every
     consumer of this record uses named projections; the only application of [ADL] is
     Bo/AS_InstLaws1.v [inst_driver_laws], which is plain bullets. *)
  adl_rdr : forall mo mo', as_MPRES H mo mo' -> m_channel_reader mo' = m_channel_reader mo;
  (* [comment removed for export] *)
  adl_live : ADRV_LIVE <= as_LIVE_MAX H /\ ADRV_CNT <= as_LIVE_CNT_MAX H }.

End HCW.

