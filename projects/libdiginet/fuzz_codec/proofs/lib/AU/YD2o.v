(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made for libreac/fuzz_knock from proofs/cgif/cgif_file_fuzzer/lib/YD2o.v and YD2p.v at
   c8557374ad2e; the asan-ubsan twin of lib/A/AD2o.v, equal to it up to module names and image constants. This file is
   knock's closing assembly of lib/A/KnockClose.v's parts (rule 24: no function proved; kind: assembly): it instantiates
   KnockClose's asan_ubsan Section at closed parts, so fuzz_knock's two asan-ubsan statements rest on no Section hypothesis.
   cgif's YD2o keeps three program-walk hypotheses that its YD2p discharges; knock's program contract (lib/AU/APgLib.v
   knock_lib_x_all) takes none, so the closing is one file and there is no YD2p. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_knock/lib/AU/YD2o.v, with its module paths and module names changed; 33 of its 66 lines of code are new or changed and 19 lines of the source are left out. *)
(* fuzz_codec's image-B closing assembly, the twin of lib/A/AD2o.v (projects/libreac/fuzz_knock/proofs/lib/AU/YD2o.v's form):
   lib/A/CodecClose.v's asan_ubsan Section at its parts. The start-up is image B's certificate (YB01.HS_tfib,
   YB12.TFIB, YB1n.tfib_startup_T1); the record is YD2l.TfibB; the allocator parts are lib/AU/YCodecAllocClose.v's;
   the driver main is lib/AU/YD1q.v DRV_MAINX with the program contract LIBX (YCfn.tfib_lib_contract_x_all at
   ameter_triv / XL0 / CB_RLO .. CB_RHI), which comes from the program walks through
   lib/AU/Prog/CPgCloseU.v codecU_lib_x_all_of_walks, so the two image-B statements rest on no premise. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libdiginet.fuzz_codec Require Statements.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require AgreeCodec.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YG00 YG01 YG0f YG0d YC5d YCbp YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YG0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require AWalkFw0 YB01 YB12 YB1n YCejTfib YD2l YD2m YD1k YD1o YD1l YD1j YD1q YCfn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require CodecAsanTop CodecClose.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require YCodecAllocClose.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require CPgWalkU CPgCloseU.
Local Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance YD1q.codec_ag_sil_shape.

(* The library shape of the driver core, YD1q.codec_ag_sil_shape, is the shape ASAN_UBSAN_T states
   (CodecAsanTop.codec_shape := AgreeCodec.ag_sil_shape): YD1q writes out AgreeShape.ag_shape at
   ZTraceSpec.checksum_shape, because it may not load lib/AgreeCodec.v. *)
Lemma codec_ag_sil_shape_eq : YD1q.codec_ag_sil_shape = AgreeCodec.ag_sil_shape.
Proof. reflexivity. Qed.

Section m.
(* The program contract the driver takes, at every run ceiling. *)
Hypothesis LIBX : forall rc : YM05.RunCeil,
  @YCfn.tfib_lib_contract_x_all rc YD1q.codec_ag_sil_shape YD2l.TfibB ameter_triv CPgCloseU.XL0 CPgCloseU.XL0
    CPgWalkU.CB_RLO CPgWalkU.CB_RHI.

(* CodecClose's H_DRIVER_U at B_U := YD2l.TfibB, from YD1q.DRV_MAINX. H_DRIVER_U hands over the three allocator parts
   for every FPState, DRV_MAINX takes them at YK11.fx0; DRV_MAINX's other parts are supplied here: TfibSyms
   (YD2l.TfibB_syms), the read check (YD2m.tfib_ARDCHK), MT_FREE (ameter_triv's mo_ok is True), RO_IN
   (CB_RLO .. CB_RHI is in_ro_tfa's second disjunct), LIBX, and the stdio sites (YD1k, YD1o, YD1l, YD1j).
   H_DRIVER's two trace premises are not used: YD2l.TfibB_syms carries them. *)
Lemma codec_driver_TfibB_U : forall rc : YM05.RunCeil,
  (forall fx : YK11.FPState, @amalloc_realizes fx rc AU.AWalkFw0.tfibsegs YD2l.TfibB) ->
  (forall fx : YK11.FPState, @afree_realizes fx rc AU.AWalkFw0.tfibsegs YD2l.TfibB) ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc AU.AWalkFw0.tfibsegs YD2l.TfibB OCpy (pc_wrap_memcpy (as_code YD2l.TfibB))) ->
  universe_ok (as_universe YD2l.TfibB) ->
  (forall t, In t YCejTfib.Tfib_drv_traces -> In t (as_universe YD2l.TfibB)) ->
  CodecClose.drv_mainU YB01.HS_tfib YB12.TFIB rc.
Proof.
  intros rc AM AF AI _ _.
  exact (@YD1q.DRV_MAINX rc YD2l.TfibB YD2l.TfibB_syms (AM YK11.fx0) (AF YK11.fx0) (AI YK11.fx0)
    (YD2m.tfib_ARDCHK YD2l.TfibB YD2l.TfibB_syms)
    ameter_triv CPgCloseU.XL0 CPgCloseU.XL0 CPgWalkU.CB_RLO CPgWalkU.CB_RHI (fun _ _ => I) (fun a H => or_intror H)
    (LIBX rc)
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

(* CodecClose's asan_ubsan Section at its parts. *)
Theorem ASAN_UBSAN_T_of_LIBX : CodecAsanTop.ASAN_UBSAN_T.
Proof.
  exact (CodecClose.ASAN_UBSAN_T_of_parts YB01.HS_tfib YB12.TFIB YB1n.tfib_startup_T1 YD2l.TfibB
    YCodecAllocClose.codec_amalloc_closed_U YCodecAllocClose.codec_afree_closed_U YCodecAllocClose.codec_aicpy_closed_U eq_refl
    codec_driver_TfibB_U).
Qed.
End m.

(* The image-B obligation and the two image-B statements, with no premise: LIBX from the program walks
   (lib/AU/Prog/CPgCloseU.v codecU_lib_x_all_of_walks); LEAF holds by eq_refl at the driver's shape, because the
   harness writes no file and returns 0. *)
Theorem codec_ASAN_UBSAN_T_closed :
  CodecAsanTop.ASAN_UBSAN_T.
Proof.
  apply ASAN_UBSAN_T_of_LIBX. intros rc.
  exact (CPgCloseU.codecU_lib_x_all_of_walks rc YD1q.codec_ag_sil_shape (fun _ _ _ => eq_refl)).
Qed.

Theorem codec_asan_ubsan_agrees_closed :
  Statements.asan_ubsan_agrees.
Proof.
  exact (CodecAsanTop.asan_ubsan_agrees_of_asan_side codec_ASAN_UBSAN_T_closed).
Qed.

Theorem codec_asan_ubsan_halts_closed :
  Statements.asan_ubsan_halts.
Proof.
  exact (CodecAsanTop.asan_ubsan_halts_of_asan_side codec_ASAN_UBSAN_T_closed).
Qed.
