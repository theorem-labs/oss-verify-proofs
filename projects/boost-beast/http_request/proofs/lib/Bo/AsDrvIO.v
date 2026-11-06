(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib SReach RegsEquivM MainEqv HeapCeil Frame Spec
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame SymAux RefPrintfLib LibTail RefMemcpyLib
  LazyRestrict LazySR LazyFdNodes LazySym.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Mem Cells Step Frame MState SysStep Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface AsCXXHeap AsDriverLaws.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AsLazyRun.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import RefExitBase RefStdioDefs AsStdioWrite AsStdioCall.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AsScLib.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AsPrintfFirst AsPrintfBuf AsHdrErr AsDrvRun.
Import OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Section IO.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis DL : asan_driver_laws H.

  Let rom := seg_rom bsegs.

  (* [comment removed for export] *)
  Theorem drv_msteps : forall s msF regs pc mem regs' pc' mem' mo T,
    as_VIS H s msF = mkst regs pc mem rom -> as_AKREL H s (mkCfg msF mo) ->
    CatSim.msteps bsegs (mkst regs pc mem rom) (mkst regs' pc' mem' rom) ->
    (forall msF' mo', as_VIS H s msF' = mkst regs' pc' mem' rom -> as_AKREL H s (mkCfg msF' mo') ->
       same_but_materialized mo mo' -> realizes bsegs (mkCfg msF' mo') T) ->
    realizes bsegs (mkCfg msF mo) T.
  Proof.
    intros s msF regs pc mem regs' pc' mem' mo T HV HA Hms HK.
    apply (drv_lazy H DL s msF mo regs pc mem T HV HA). intros L S Zr OK RS BACK.
    eapply (rz_msteps_lazy_mkst bsegs L S Zr msF regs pc mem rom regs' pc' mem' mo T OK RS Hms).
    intros msF' mo' OK' SB' HS' RS'. destruct (BACK msF' mo' _ OK' (same_vm_sb _ _ SB') RS') as [HV' HA'].
    exact (HK msF' mo' HV' HA' SB').
  Qed.

  (* [comment removed for export] *)
  Theorem drv_printf_first : forall s msF mo regs mem (sp : word) (can : Z) (K : TSet),
    ap1H regs mem sp can ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 0x0a43f4) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    K [] ->
    (forall regs' mem' msF' mo', ap1Post regs mem sp can regs' mem' ->
       as_VIS H s msF' = mkst regs' (Z_to_bv 64 0x0a4348) mem' rom -> as_AKREL H s (mkCfg msF' mo') ->
       same_but_materialized mo mo' ->
       realizes bsegs (mkCfg msF' mo') K) ->
    realizes bsegs (mkCfg msF mo) (t_emit [WriteEv (Z_to_bv 64 1) (Z_to_bv 8 48); WriteEv (Z_to_bv 64 1) (Z_to_bv 8 10)] K).
  Proof.
    intros s msF mo regs mem sp can K PH HV HA Hfd1 HKnil HK.
    apply (drv_lazy H DL s msF mo regs _ mem _ HV HA). intros L S Zr OK RS BACK.
    apply (aprintf0_first L S Zr regs mem msF mo sp can K PH OK RS Hfd1 HKnil).
    intros regs' mem' msF' mo' PO OK' SB' HS' RS'. destruct (BACK msF' mo' _ OK' (same_vm_sb _ _ SB') RS') as [HV' HA'].
    exact (HK regs' mem' msF' mo' PO HV' HA' SB').
  Qed.

  (* [comment removed for export] *)
  Theorem drv_printf_buf : forall (j : nat) s msF mo regs mem (sp : word) (can : Z) (K : TSet),
    (j <= 2)%nat ->
    apbH mem sp (ABUF + 2 * Z.of_nat j) can ->
    getr regs 1 = Z_to_bv 64 0x0a4348 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 0x0a43f4) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    (forall regs' mem' msF' mo',
       keeps_cs regs regs' ->
       frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 3400), 3400); (Z_to_bv 64 0x123fe0, 4);
                           (Z_to_bv 64 0x124008, 8); (Z_to_bv 64 (ABUF + 2 * Z.of_nat j), 2)] ->
       rdn bsegs mem' (Z_to_bv 64 (ABUF + 2 * Z.of_nat j)) 2 = Some [Z_to_bv 8 0x30; Z_to_bv 8 0x0a] ->
       rdn bsegs mem' (Z_to_bv 64 0x124008) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (ABUF + 2 * Z.of_nat j + 2))) ->
       rdn bsegs mem' (Z_to_bv 64 0x123fe0) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5)) ->
       as_VIS H s msF' = mkst regs' (Z_to_bv 64 0x0a4348) mem' rom -> as_AKREL H s (mkCfg msF' mo') ->
       same_but_materialized mo mo' ->
       realizes bsegs (mkCfg msF' mo') K) ->
    realizes bsegs (mkCfg msF mo) K.
  Proof.
    intros j s msF mo regs mem sp can K Hj PH R1 R2 R11 HV HA HK.
    destruct (aprintf0_buffered j regs mem rom sp can Hj PH R1 R2 R11) as (regs' & mem' & RUN & KCS & FM & RD1 & RD2 & RD3).
    apply (drv_msteps s msF regs _ mem regs' _ mem' mo K HV HA RUN).
    intros msF' mo' HV' HA' SB'. exact (HK regs' mem' msF' mo' KCS FM RD1 RD2 RD3 HV' HA' SB').
  Qed.

  (* [comment removed for export] *)
  Theorem drv_hdr_short : forall s msF mo regs mem (sp : word) (can : Z) (K : TSet),
    hfH regs mem sp can ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 0x0a4154) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    K [] ->
    (forall regs' mem' msF' mo', hfPost regs mem sp can regs' mem' ->
       as_VIS H s msF' = mkst regs' (Z_to_bv 64 0x0a4190) mem' rom -> as_AKREL H s (mkCfg msF' mo') ->
       same_but_materialized mo mo' ->
       realizes bsegs (mkCfg msF' mo') K) ->
    realizes bsegs (mkCfg msF mo) (t_emit (W 2 msg_short) K).
  Proof.
    intros s msF mo regs mem sp can K PH HV HA Hfd2 HKnil HK.
    apply (drv_lazy H DL s msF mo regs _ mem _ HV HA). intros L S Zr OK RS BACK.
    apply (as_hdr_short_fwrite L S Zr regs mem msF mo sp can K PH OK RS Hfd2 HKnil).
    intros regs' mem' msF' mo' PO OK' SB' HS' RS'. destruct (BACK msF' mo' _ OK' (same_vm_sb _ _ SB') RS') as [HV' HA'].
    exact (HK regs' mem' msF' mo' PO HV' HA' SB').
  Qed.

  Theorem drv_hdr_overrun : forall s msF mo regs mem (sp : word) (can : Z) (K : TSet),
    hfH regs mem sp can ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 0x0a4170) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    K [] ->
    (forall regs' mem' msF' mo', hfPost regs mem sp can regs' mem' ->
       as_VIS H s msF' = mkst regs' (Z_to_bv 64 0x0a4190) mem' rom -> as_AKREL H s (mkCfg msF' mo') ->
       same_but_materialized mo mo' ->
       realizes bsegs (mkCfg msF' mo') K) ->
    realizes bsegs (mkCfg msF mo) (t_emit (W 2 msg_overrun) K).
  Proof.
    intros s msF mo regs mem sp can K PH HV HA Hfd2 HKnil HK.
    apply (drv_lazy H DL s msF mo regs _ mem _ HV HA). intros L S Zr OK RS BACK.
    apply (as_hdr_overrun_fwrite L S Zr regs mem msF mo sp can K PH OK RS Hfd2 HKnil).
    intros regs' mem' msF' mo' PO OK' SB' HS' RS'. destruct (BACK msF' mo' _ OK' (same_vm_sb _ _ SB') RS') as [HV' HA'].
    exact (HK regs' mem' msF' mo' PO HV' HA' SB').
  Qed.
End IO.
