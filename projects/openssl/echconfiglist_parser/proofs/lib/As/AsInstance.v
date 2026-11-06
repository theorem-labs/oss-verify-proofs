(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.openssl.echconfiglist_parser.images Require Import Asan.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As Require Import ASegs AsIface AsIfaceX AsDriverLaws ECH_Iface AsMainPre F_time AInstFacts.   (* [comment removed for export] *)   (* [comment removed for export] *)
Import OSSVerify.Proofs.openssl.echconfiglist_parser.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Instance.
  (* [comment removed for export] *)
  Variable P_main : word -> word -> word -> EntryDraw -> ProcInput -> config -> Prop.
  (* [comment removed for export] *)
  Variable L : alib.

  (* [comment removed for export] *)
  Definition as_instance_stmt : Prop :=
    forall (sp0 brk0 mbase : word) (rdraw : EntryDraw) (inp : ProcInput) (c : config),
      P_main sp0 brk0 mbase rdraw inp c ->
      exists (HCEIL : HeapCeil) (H : asr) (s0 : as_St H) (regs : bvmap 5 word) (mem : word -> option byte) (B tid can : Z),
        asan_rt_hyps_x H /\ ainst_facts H /\ asan_driver_laws H
        /\ (ADRV_LIVE <= as_LIVE_MAX H /\ ADRV_CNT <= as_LIVE_CNT_MAX H)
        /\ AMpre H L sp0 (in_argv inp) s0 (cfg_ms c) (cfg_model c) regs mem B tid can
        /\ m_fs (cfg_model c) = in_fs inp.
End Instance.
