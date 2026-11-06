(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made for libreac/fuzz_knock from proofs/cgif/cgif_file_fuzzer/lib/YD2o.v and YD2p.v at
   c8557374ad2e; the asan-ubsan twin of lib/A/AD2o.v, equal to it up to module names and image constants. This file is
   knock's closing assembly of lib/A/KnockClose.v's parts (rule 24: no function proved; kind: assembly): it instantiates
   KnockClose's asan_ubsan Section at closed parts, so fuzz_knock's two asan-ubsan statements rest on no Section hypothesis.
   cgif's YD2o keeps three program-walk hypotheses that its YD2p discharges; knock's program contract (lib/AU/APgLib.v
   knock_lib_x_all) takes none, so the closing is one file and there is no YD2p. *)
(* Modified by Theorem Labs, 2026-10: taken for reac-pw/fuzz_qdisc image B (fuzz_qdisc.asan-ubsan, sha256
   eb657d77bd4b27038d93f75626dcc6b37a48be09c889fda664b4f451c6602062) from proofs/libreac/fuzz_knock/lib/AU/YD2o.v at
   origin/ossv/recipes 88154566652, in the form of this library's lib/A/AD2o.v: it instantiates lib/A/QdiscClose.v's
   asan_ubsan Section; the program contract is lib/AU/APgLib.v's (qdisc_lib_contract_x_all_tfib over qdisc_lib_x_all, in
   the roles of knock's APgLib knock_* lemmas); the allocator parts are lib/AU/YQdiscAllocClose.v's; QdiscClose takes
   image B's trace tables as Section arguments (Tfib_universe_U, Tfib_universe_ok_U, Tfib_drv_traces_U,
   Tfib_universe_drv_U), which this file passes from lib/AU/YCej.v and lib/AU/YCejTfib.v; names knock_* -> qdisc_*,
   module paths changed. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.reac_pw.fuzz_qdisc Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib Require AgreeQdisc.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YK11 YG00 YG01 YG0f YG0d YC5d YCbp YM05.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.AU Require AWalkFw0 YB01 YB12 YB1n YCej YCejTfib YD2l YD2m YD1k YD1o YD1l YD1j YD1q.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.AU Require APgLib YQdiscAllocClose.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.A Require QdiscAsanTop QdiscClose.
Local Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance AgreeQdisc.ag_sil_shape.

(* The library shape of image B's driver core, lib/AU/YD1q.v qdisc_ag_sil_shape, is the shape ASAN_UBSAN_T states
   (QdiscAsanTop.qdisc_shape := AgreeQdisc.ag_sil_shape). YD1q writes out the body of AgreeShape.ag_shape at
   ZTraceSpec.checksum_shape, as lib/A/AD1q.v does; qdisc_driver_TfibB_U below gives DRV_MAINX, whose CLOSEDX and LIBX are
   stated at YD1q's shape, terms stated at AgreeQdisc's; this lemma is that conversion as a named, checked fact. *)
Lemma qdisc_ag_sil_shape_eq_U : YD1q.qdisc_ag_sil_shape = AgreeQdisc.ag_sil_shape.
Proof. reflexivity. Qed.

(* QdiscClose's H_DRIVER_U at B_U := YD2l.TfibB, from lib/AU/YD1q.v DRV_MAINX (the core's driver walk); the same adapter
   as lib/A/AD2o.v qdisc_driver_TfibB, with image B's parts. (1) H_DRIVER_U hands over the three allocator parts for
   every FPState; DRV_MAINX takes them at YK11.fx0. (2) DRV_MAINX takes the driver's other parts, which H_DRIVER_U leaves
   inside itself; they are supplied here: TfibSyms (YD2l.TfibB_syms), the read check (YD2m.tfib_ARDCHK), the program
   contract LIBX (APgLib.qdisc_lib_x_all at ameter_triv / XL0 / RO_LO..RO_HI = 0x953a0..0x965f8, through
   APgLib.qdisc_lib_contract_x_all_tfib; its LEAF holds by eq_refl at AgreeQdisc.ag_sil_shape), MT_FREE (ameter_triv's
   mo_ok is True), RO_IN (RO_LO..RO_HI is in_ro_tfa's second disjunct) and the stdio sites (YD1k, YD1o, YD1l, YD1j).
   The program contract's meter is ameter_triv because the harness makes no allocator call (APgLib's EV_LIB = 0);
   the allocator parts hold at every RunCeil and FPState (lib/AU/YQdiscAllocClose.v), so at the run's own.
   H_DRIVER_U's two trace premises are not used: YD2l.TfibB_syms carries them. *)
Lemma qdisc_driver_TfibB_U : forall rc : YM05.RunCeil,
  (forall fx : YK11.FPState, @amalloc_realizes fx rc AU.AWalkFw0.tfibsegs YD2l.TfibB) ->
  (forall fx : YK11.FPState, @afree_realizes fx rc AU.AWalkFw0.tfibsegs YD2l.TfibB) ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc AU.AWalkFw0.tfibsegs YD2l.TfibB OCpy (pc_wrap_memcpy (as_code YD2l.TfibB))) ->
  universe_ok (as_universe YD2l.TfibB) ->
  (forall t, In t YCejTfib.Tfib_drv_traces -> In t (as_universe YD2l.TfibB)) ->
  QdiscClose.drv_mainU YB01.HS_tfib YB12.TFIB rc.
Proof.
  intros rc AM AF AI _ _.
  exact (@YD1q.DRV_MAINX rc YD2l.TfibB YD2l.TfibB_syms (AM YK11.fx0) (AF YK11.fx0) (AI YK11.fx0)
    (YD2m.tfib_ARDCHK YD2l.TfibB YD2l.TfibB_syms)
    ameter_triv AU.APgLib.XL0 AU.APgLib.XL0 AU.APgLib.RO_LO AU.APgLib.RO_HI (fun _ _ => I) (fun a H => or_intror H)
    (AU.APgLib.qdisc_lib_contract_x_all_tfib YD2l.TfibB ameter_triv AU.APgLib.XL0 AU.APgLib.XL0 AU.APgLib.RO_LO AU.APgLib.RO_HI
      (@AU.APgLib.qdisc_lib_x_all rc AgreeQdisc.ag_sil_shape (fun _ _ _ => eq_refl)))
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

(* QdiscClose's asan_ubsan Section at its parts: HS_TBL_U / TFIB_TBL_U / H_STARTUP_U from the start-up certificate
   (YB01.HS_tfib, YB12.TFIB, YB1n.tfib_startup_T1), B_U := YD2l.TfibB, the allocator parts from
   lib/AU/YQdiscAllocClose.v, the trace tables from lib/AU/YCej.v (Tfib_universe, Tfib_universe_ok) with H_TRACES_B_U by
   reflexivity (YD2l.TfibB's as_universe is YCej.Tfib_universe) and lib/AU/YCejTfib.v (Tfib_drv_traces,
   Tfib_universe_drv), and H_DRIVER_U from qdisc_driver_TfibB_U. *)
Theorem ASAN_UBSAN_T_closed : QdiscAsanTop.ASAN_UBSAN_T.
Proof.
  exact (QdiscClose.ASAN_UBSAN_T_of_parts YB01.HS_tfib YB12.TFIB YB1n.tfib_startup_T1 YD2l.TfibB
    YQdiscAllocClose.qdisc_amalloc_closed_U YQdiscAllocClose.qdisc_afree_closed_U YQdiscAllocClose.qdisc_aicpy_closed_U
    YCej.Tfib_universe YCej.Tfib_universe_ok eq_refl YCejTfib.Tfib_drv_traces YCejTfib.Tfib_universe_drv
    qdisc_driver_TfibB_U).
Qed.
Theorem qdisc_asan_ubsan_agrees_closed : Statements.asan_ubsan_agrees.
Proof. exact (QdiscAsanTop.asan_ubsan_agrees_of_asan_side ASAN_UBSAN_T_closed). Qed.
Theorem qdisc_asan_ubsan_halts_closed : Statements.asan_ubsan_halts.
Proof. exact (QdiscAsanTop.asan_ubsan_halts_of_asan_side ASAN_UBSAN_T_closed). Qed.
