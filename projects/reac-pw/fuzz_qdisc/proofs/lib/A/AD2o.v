(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made for libreac/fuzz_knock from proofs/cgif/cgif_file_fuzzer/lib/A/AD2o.v and AD2p.v at
   c8557374ad2e. This file is knock's closing assembly of lib/A/KnockClose.v's parts (rule 24: no function proved; kind:
   assembly): it instantiates KnockClose's asan Section at closed parts, so fuzz_knock's two ASan statements rest on no
   Section hypothesis. cgif's AD2o keeps three program-walk hypotheses that its AD2p discharges; knock's program contract
   (lib/A/APgLib.v knock_lib_x_all) takes none, so the closing is one file and there is no AD2p. *)
(* Modified by Theorem Labs, 2026-10: taken for reac-pw/fuzz_qdisc image A from proofs/libreac/fuzz_knock/lib/A/AD2o.v at
   origin/ossv/recipes 6ebe35ba632: it instantiates lib/A/QdiscClose.v's asan Section; the program contract is
   lib/A/QPgLib.v's (qdisc_lib_contract_x_all_tfib over qdisc_lib_x_all, in the roles of APgLib's knock_* lemmas); the
   allocator parts are lib/A/QdiscAllocClose.v's; names knock_* -> qdisc_*, module paths changed (h-small-a3). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.reac_pw.fuzz_qdisc Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib Require AgreeQdisc.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YK11 YG00 YG01 YG0f YG0d YC5d YCbp YM05.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.A Require AWalkFw0 AB01 AB12 AB1n ACejTfib AD2l AD2m AD1k AD1o AD1l AD1j AD1q.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.A Require QPgLib QdiscAllocClose QdiscAsanTop QdiscClose.
Local Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance AgreeQdisc.ag_sil_shape.

(* The library shape of A3's driver core, lib/A/AD1q.v qdisc_ag_sil_shape, is the shape ASAN_T states
   (QdiscAsanTop.qdisc_shape := AgreeQdisc.ag_sil_shape). AD1q may not Require lib/AgreeQdisc.v (it loads Reusable/YI5b
   and YI5c), so AD1q writes out the body of AgreeShape.ag_shape at ZTraceSpec.checksum_shape. qdisc_driver_TfibB below
   gives DRV_MAINX, whose CLOSEDX and LIBX are stated at AD1q's shape, terms stated at AgreeQdisc's; this lemma is that
   conversion as a named, checked fact (h-small-q1, 2026-10-30 10:28Z). *)
Lemma qdisc_ag_sil_shape_eq : AD1q.qdisc_ag_sil_shape = AgreeQdisc.ag_sil_shape.
Proof. reflexivity. Qed.

(* QdiscClose's H_DRIVER at B := AD2l.TfibB, from lib/A/AD1q.v DRV_MAINX (the core's driver walk). The adapter bridges two
   differences. (1) H_DRIVER hands over the three allocator parts for every FPState; DRV_MAINX takes them at YK11.fx0.
   (2) DRV_MAINX takes the driver's other parts, which H_DRIVER leaves inside itself; they are supplied here: TfibSyms
   (AD2l.TfibB_syms), the read check (AD2m.tfib_ARDCHK), the program contract LIBX (QPgLib.qdisc_lib_x_all at
   ameter_triv / XL0 / RO_LO..RO_HI, through QPgLib.qdisc_lib_contract_x_all_tfib; its LEAF holds by eq_refl at
   AgreeQdisc.ag_sil_shape), MT_FREE (ameter_triv's mo_ok is True), RO_IN (RO_LO..RO_HI is in_ro_tfa's second disjunct)
   and the stdio sites (AD1k, AD1o, AD1l, AD1j). H_DRIVER's two trace premises are not used: AD2l.TfibB_syms carries
   them. *)
Lemma qdisc_driver_TfibB : forall rc : YM05.RunCeil,
  (forall fx : YK11.FPState, @amalloc_realizes fx rc AWalkFw0.tfibsegs AD2l.TfibB) ->
  (forall fx : YK11.FPState, @afree_realizes fx rc AWalkFw0.tfibsegs AD2l.TfibB) ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc AWalkFw0.tfibsegs AD2l.TfibB OCpy (pc_wrap_memcpy (as_code AD2l.TfibB))) ->
  universe_ok (as_universe AD2l.TfibB) ->
  (forall t, In t ACejTfib.Tfib_drv_traces -> In t (as_universe AD2l.TfibB)) ->
  QdiscClose.drv_mainA AB01.HS_tfib AB12.TFIB rc.
Proof.
  intros rc AM AF AI _ _.
  exact (@AD1q.DRV_MAINX rc AD2l.TfibB AD2l.TfibB_syms (AM YK11.fx0) (AF YK11.fx0) (AI YK11.fx0)
    (AD2m.tfib_ARDCHK AD2l.TfibB AD2l.TfibB_syms)
    ameter_triv QPgLib.XL0 QPgLib.XL0 QPgLib.RO_LO QPgLib.RO_HI (fun _ _ => I) (fun a H => or_intror H)
    (QPgLib.qdisc_lib_contract_x_all_tfib AD2l.TfibB ameter_triv QPgLib.XL0 QPgLib.XL0 QPgLib.RO_LO QPgLib.RO_HI
      (@QPgLib.qdisc_lib_x_all rc AgreeQdisc.ag_sil_shape (fun _ _ _ => eq_refl)))
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

(* QdiscClose's asan Section at its parts: HS_TBL / TFIB_TBL / H_STARTUP from the start-up certificate (AB01.HS_tfib,
   AB12.TFIB, AB1n.tfib_startup_T1), B := AD2l.TfibB with H_TRACES_B by reflexivity, the allocator parts from
   lib/A/QdiscAllocClose.v, and H_DRIVER from qdisc_driver_TfibB. *)
Theorem ASAN_T_closed : QdiscAsanTop.ASAN_T.
Proof.
  exact (QdiscClose.ASAN_T_of_parts AB01.HS_tfib AB12.TFIB AB1n.tfib_startup_T1 AD2l.TfibB
    QdiscAllocClose.qdisc_amalloc_closed QdiscAllocClose.qdisc_afree_closed QdiscAllocClose.qdisc_aicpy_closed eq_refl
    qdisc_driver_TfibB).
Qed.
Theorem qdisc_asan_agrees_closed : Statements.asan_agrees.
Proof. exact (QdiscAsanTop.asan_agrees_of_asan_side ASAN_T_closed). Qed.
Theorem qdisc_asan_halts_closed : Statements.asan_halts.
Proof. exact (QdiscAsanTop.asan_halts_of_asan_side ASAN_T_closed). Qed.
