(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made for libreac/fuzz_knock from proofs/cgif/cgif_file_fuzzer/lib/A/AD2o.v and AD2p.v at
   c8557374ad2e. This file is knock's closing assembly of lib/A/KnockClose.v's parts (rule 24: no function proved; kind:
   assembly): it instantiates KnockClose's asan Section at closed parts, so fuzz_knock's two ASan statements rest on no
   Section hypothesis. cgif's AD2o keeps three program-walk hypotheses that its AD2p discharges; knock's program contract
   (lib/A/APgLib.v knock_lib_x_all) takes none, so the closing is one file and there is no AD2p. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_knock Require Statements.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require AgreeKnock.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK11 YG00 YG01 YG0f YG0d YC5d YCbp YM05.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YG0q.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require AWalkFw0 AB01 AB12 AB1n ACejTfib AD2l AD2m AD1k AD1o AD1l AD1j AD1q.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require APgLib KnockAllocClose KnockAsanTop KnockClose.
Local Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance AgreeKnock.ag_sil_shape.

(* KnockClose's H_DRIVER at B := AD2l.TfibB, from lib/A/AD1q.v DRV_MAINX (the core's driver walk). The adapter bridges two
   differences. (1) H_DRIVER hands over the three allocator parts for every FPState; DRV_MAINX takes them at YK11.fx0.
   (2) DRV_MAINX takes the driver's other parts, which H_DRIVER leaves inside itself; they are supplied here: TfibSyms
   (AD2l.TfibB_syms), the read check (AD2m.tfib_ARDCHK), the program contract LIBX (APgLib.knock_lib_x_all at
   ameter_triv / XL0 / RO_LO..RO_HI, through APgLib.knock_lib_contract_x_all_tfib; its LEAF holds by eq_refl at
   AgreeKnock.ag_sil_shape), MT_FREE (ameter_triv's mo_ok is True), RO_IN (RO_LO..RO_HI is in_ro_tfa's second disjunct)
   and the stdio sites (AD1k, AD1o, AD1l, AD1j). H_DRIVER's two trace premises are not used: AD2l.TfibB_syms carries
   them. *)
Lemma knock_driver_TfibB : forall rc : YM05.RunCeil,
  (forall fx : YK11.FPState, @amalloc_realizes fx rc AWalkFw0.tfibsegs AD2l.TfibB) ->
  (forall fx : YK11.FPState, @afree_realizes fx rc AWalkFw0.tfibsegs AD2l.TfibB) ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc AWalkFw0.tfibsegs AD2l.TfibB OCpy (pc_wrap_memcpy (as_code AD2l.TfibB))) ->
  universe_ok (as_universe AD2l.TfibB) ->
  (forall t, In t ACejTfib.Tfib_drv_traces -> In t (as_universe AD2l.TfibB)) ->
  KnockClose.drv_mainA AB01.HS_tfib AB12.TFIB rc.
Proof.
  intros rc AM AF AI _ _.
  exact (@AD1q.DRV_MAINX rc AD2l.TfibB AD2l.TfibB_syms (AM YK11.fx0) (AF YK11.fx0) (AI YK11.fx0)
    (AD2m.tfib_ARDCHK AD2l.TfibB AD2l.TfibB_syms)
    ameter_triv APgLib.XL0 APgLib.XL0 APgLib.RO_LO APgLib.RO_HI (fun _ _ => I) (fun a H => or_intror H)
    (APgLib.knock_lib_contract_x_all_tfib AD2l.TfibB ameter_triv APgLib.XL0 APgLib.XL0 APgLib.RO_LO APgLib.RO_HI
      (@APgLib.knock_lib_x_all rc AgreeKnock.ag_sil_shape (fun _ _ _ => eq_refl)))
    AD1k.xst AD1k.tfib_xst_frame
    (AD1o.tfib_printf_first AD2l.TfibB AD2l.TfibB_syms (YG0q.AR_laws_ok AWalkFw0.tfibsegs AD2l.TfibB) AD2l.TfibB_syms)
    (AD1o.tfib_printf_next AD2l.TfibB AD2l.TfibB_syms (YG0q.AR_laws_ok AWalkFw0.tfibsegs AD2l.TfibB) AD2l.TfibB_syms)
    AD1k.est AD1k.tfib_est_img AD1k.tfib_est_frame
    (AD1k.tfib_fwrite_site AD2l.TfibB AD2l.TfibB_syms (YG0q.AR_laws_ok AWalkFw0.tfibsegs AD2l.TfibB))
    (AD1k.tfib_refused_site AD2l.TfibB AD2l.TfibB_syms (YG0q.AR_laws_ok AWalkFw0.tfibsegs AD2l.TfibB) AD2l.TfibB_syms)
    (AD1l.tfib_fprintf_open_site AD2l.TfibB AD2l.TfibB_syms (YG0q.AR_laws_ok AWalkFw0.tfibsegs AD2l.TfibB) AD2l.TfibB_syms)
    (AD1l.tfib_fprintf_rderr_site AD2l.TfibB AD2l.TfibB_syms (YG0q.AR_laws_ok AWalkFw0.tfibsegs AD2l.TfibB) AD2l.TfibB_syms)
    (AD1l.tfib_fprintf_usage_site AD2l.TfibB AD2l.TfibB_syms (YG0q.AR_laws_ok AWalkFw0.tfibsegs AD2l.TfibB) AD2l.TfibB_syms)
    (AD1j.tfib_exit_site AD2l.TfibB AD2l.TfibB_syms (YG0q.AR_laws_ok AWalkFw0.tfibsegs AD2l.TfibB))).
Qed.

(* KnockClose's asan Section at its parts: HS_TBL / TFIB_TBL / H_STARTUP from the start-up certificate (AB01.HS_tfib,
   AB12.TFIB, AB1n.tfib_startup_T1), B := AD2l.TfibB with H_TRACES_B by reflexivity, the allocator parts from
   lib/A/KnockAllocClose.v, and H_DRIVER from knock_driver_TfibB. *)
Theorem ASAN_T_closed : KnockAsanTop.ASAN_T.
Proof.
  exact (KnockClose.ASAN_T_of_parts AB01.HS_tfib AB12.TFIB AB1n.tfib_startup_T1 AD2l.TfibB
    KnockAllocClose.knock_amalloc_closed KnockAllocClose.knock_afree_closed KnockAllocClose.knock_aicpy_closed eq_refl
    knock_driver_TfibB).
Qed.
Theorem knock_asan_agrees_closed : Statements.asan_agrees.
Proof. exact (KnockAsanTop.asan_agrees_of_asan_side ASAN_T_closed). Qed.
Theorem knock_asan_halts_closed : Statements.asan_halts.
Proof. exact (KnockAsanTop.asan_halts_of_asan_side ASAN_T_closed). Qed.
