(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made for libreac/fuzz_knock from proofs/cgif/cgif_file_fuzzer/lib/YD2o.v and YD2p.v at
   c8557374ad2e; the asan-ubsan twin of lib/A/AD2o.v, equal to it up to module names and image constants. This file is
   knock's closing assembly of lib/A/KnockClose.v's parts (rule 24: no function proved; kind: assembly): it instantiates
   KnockClose's asan_ubsan Section at closed parts, so fuzz_knock's two asan-ubsan statements rest on no Section hypothesis.
   cgif's YD2o keeps three program-walk hypotheses that its YD2p discharges; knock's program contract (lib/AU/APgLib.v
   knock_lib_x_all) takes none, so the closing is one file and there is no YD2p. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_knock Require Statements.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require AgreeKnock.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK11 YG00 YG01 YG0f YG0d YC5d YCbp YM05.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YG0q.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require AWalkFw0 YB01 YB12 YB1n YCejTfib YD2l YD2m YD1k YD1o YD1l YD1j YD1q.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require APgLib YKnockAllocClose.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require KnockAsanTop KnockClose.
Local Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance AgreeKnock.ag_sil_shape.

(* KnockClose's H_DRIVER_U at B_U := YD2l.TfibB, from lib/AU/YD1q.v DRV_MAINX; the same adapter as lib/A/AD2o.v
   knock_driver_TfibB, with the asan-ubsan parts (the program contract at RO_LO..RO_HI = 0x960b8..0x97310). *)
Lemma knock_driver_TfibB_U : forall rc : YM05.RunCeil,
  (forall fx : YK11.FPState, @amalloc_realizes fx rc AU.AWalkFw0.tfibsegs YD2l.TfibB) ->
  (forall fx : YK11.FPState, @afree_realizes fx rc AU.AWalkFw0.tfibsegs YD2l.TfibB) ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc AU.AWalkFw0.tfibsegs YD2l.TfibB OCpy (pc_wrap_memcpy (as_code YD2l.TfibB))) ->
  universe_ok (as_universe YD2l.TfibB) ->
  (forall t, In t YCejTfib.Tfib_drv_traces -> In t (as_universe YD2l.TfibB)) ->
  KnockClose.drv_mainU YB01.HS_tfib YB12.TFIB rc.
Proof.
  intros rc AM AF AI _ _.
  exact (@YD1q.DRV_MAINX rc YD2l.TfibB YD2l.TfibB_syms (AM YK11.fx0) (AF YK11.fx0) (AI YK11.fx0)
    (YD2m.tfib_ARDCHK YD2l.TfibB YD2l.TfibB_syms)
    ameter_triv AU.APgLib.XL0 AU.APgLib.XL0 AU.APgLib.RO_LO AU.APgLib.RO_HI (fun _ _ => I) (fun a H => or_intror H)
    (AU.APgLib.knock_lib_contract_x_all_tfib YD2l.TfibB ameter_triv AU.APgLib.XL0 AU.APgLib.XL0 AU.APgLib.RO_LO AU.APgLib.RO_HI
      (@AU.APgLib.knock_lib_x_all rc AgreeKnock.ag_sil_shape (fun _ _ _ => eq_refl)))
    YD1k.xst YD1k.tfib_xst_frame
    (YD1o.tfib_printf_first YD2l.TfibB YD2l.TfibB_syms (YG0q.AR_laws_ok AU.AWalkFw0.tfibsegs YD2l.TfibB) YD2l.TfibB_syms)
    (YD1o.tfib_printf_next YD2l.TfibB YD2l.TfibB_syms (YG0q.AR_laws_ok AU.AWalkFw0.tfibsegs YD2l.TfibB) YD2l.TfibB_syms)
    YD1k.est YD1k.tfib_est_img YD1k.tfib_est_frame
    (YD1k.tfib_fwrite_site YD2l.TfibB YD2l.TfibB_syms (YG0q.AR_laws_ok AU.AWalkFw0.tfibsegs YD2l.TfibB))
    (YD1k.tfib_refused_site YD2l.TfibB YD2l.TfibB_syms (YG0q.AR_laws_ok AU.AWalkFw0.tfibsegs YD2l.TfibB) YD2l.TfibB_syms)
    (YD1l.tfib_fprintf_open_site YD2l.TfibB YD2l.TfibB_syms (YG0q.AR_laws_ok AU.AWalkFw0.tfibsegs YD2l.TfibB) YD2l.TfibB_syms)
    (YD1l.tfib_fprintf_rderr_site YD2l.TfibB YD2l.TfibB_syms (YG0q.AR_laws_ok AU.AWalkFw0.tfibsegs YD2l.TfibB) YD2l.TfibB_syms)
    (YD1l.tfib_fprintf_usage_site YD2l.TfibB YD2l.TfibB_syms (YG0q.AR_laws_ok AU.AWalkFw0.tfibsegs YD2l.TfibB) YD2l.TfibB_syms)
    (YD1j.tfib_exit_site YD2l.TfibB YD2l.TfibB_syms (YG0q.AR_laws_ok AU.AWalkFw0.tfibsegs YD2l.TfibB))).
Qed.

(* KnockClose's asan_ubsan Section at its parts: HS_TBL_U / TFIB_TBL_U / H_STARTUP_U from the start-up certificate
   (YB01.HS_tfib, YB12.TFIB, YB1n.tfib_startup_T1), B_U := YD2l.TfibB with H_TRACES_B_U by reflexivity, the allocator
   parts from lib/AU/YKnockAllocClose.v, and H_DRIVER_U from knock_driver_TfibB_U. *)
Theorem ASAN_UBSAN_T_closed : KnockAsanTop.ASAN_UBSAN_T.
Proof.
  exact (KnockClose.ASAN_UBSAN_T_of_parts YB01.HS_tfib YB12.TFIB YB1n.tfib_startup_T1 YD2l.TfibB
    YKnockAllocClose.knock_amalloc_closed_U YKnockAllocClose.knock_afree_closed_U YKnockAllocClose.knock_aicpy_closed_U
    eq_refl knock_driver_TfibB_U).
Qed.
Theorem knock_asan_ubsan_agrees_closed : Statements.asan_ubsan_agrees.
Proof. exact (KnockAsanTop.asan_ubsan_agrees_of_asan_side ASAN_UBSAN_T_closed). Qed.
Theorem knock_asan_ubsan_halts_closed : Statements.asan_ubsan_halts.
Proof. exact (KnockAsanTop.asan_ubsan_halts_of_asan_side ASAN_UBSAN_T_closed). Qed.
