(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the library is a function of the heap-ceiling record, L : HeapCeil -> alib, since its state carries the resolved vdso_func value hvdso; AMpre takes L HCEIL); the instance is the run instance, so it names the vDSO pair's two windows vlo vb vhi, its driver laws are the run's over the launch's pair vdso_segments (in_kernel inp) sp0 mbase, and it carries the three tail statements, which the main phase over the run's segment list takes as hypotheses and no longer proves from the binary's driver laws. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.openssl.echconfiglist_parser.images Require Import Asan.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As Require Import ASegs AsIface AsIfaceX AsDriverLaws ECH_Iface AsMainPre AsMainTop F_time AInstFacts.   (* [comment removed for export] *)   (* [comment removed for export] *)
Import OSSVerify.Proofs.openssl.echconfiglist_parser.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Instance.
  (* [comment removed for export] *)
  Variable P_main : word -> word -> word -> EntryDraw -> ProcInput -> config -> Prop.
  (* [comment removed for export] *)
  Variable L : HeapCeil -> alib.

  (* The single contract between the tops (As/AsTop.v) and the kit (As/AS_InstanceKit.v).
     [vlo], [vb] and [vhi] are the launch's vDSO pair: the vvar entry [vlo, vb) and the text
     entry [vb, vhi) ([Ref/VdsoLaunch.v] [vd_lo], [vd_mid], [vd_top]).  The instance's driver
     laws are the run's ([AsDriverLaws.asan_driver_laws_run]) over the tail the launch maps, so
     every walk above is over [asegs ++ vdso_segments (in_kernel inp) sp0 mbase].  The three
     tail statements are the instance's too: at the run instance [AsSRRun.KHr] they are no
     longer [AsMainTails]' (which proves them for the binary's driver laws), but its lifts
     ([As/AsTailsRun.v]). *)
  Definition as_instance_stmt : Prop :=
    forall (sp0 brk0 mbase : word) (rdraw : EntryDraw) (inp : ProcInput) (c : config),
      P_main sp0 brk0 mbase rdraw inp c ->
      exists (HCEIL : HeapCeil) (H : asr) (vlo vb vhi : Z) (s0 : as_St H) (regs : bvmap 5 word)
             (mem : word -> option byte) (B tid can : Z),
        asan_rt_hyps_x H /\ ainst_facts H
        /\ asan_driver_laws_run (vdso_segments (in_kernel inp) sp0 mbase) vlo vb vhi H
        /\ (ADRV_LIVE <= as_LIVE_MAX H /\ ADRV_CNT <= as_LIVE_CNT_MAX H)
        /\ (atail_usage_stmt H (L HCEIL) /\ atail_open_stmt H (L HCEIL) /\ atail_rderr_stmt H (L HCEIL))
        /\ AMpre H (L HCEIL) sp0 (in_argv inp) s0 (cfg_ms c) (cfg_model c) regs mem B tid can
        /\ m_fs (cfg_model c) = in_fs inp.
End Instance.
