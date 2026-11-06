(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made for libreac/fuzz_knock from proofs/cgif/cgif_file_fuzzer/lib/A/AD2o.v and AD2p.v at
   c8557374ad2e. This file is knock's closing assembly of lib/A/KnockClose.v's parts (rule 24: no function proved; kind:
   assembly): it instantiates KnockClose's asan Section at closed parts, so fuzz_knock's two ASan statements rest on no
   Section hypothesis. cgif's AD2o keeps three program-walk hypotheses that its AD2p discharges; knock's program contract
   (lib/A/APgLib.v knock_lib_x_all) takes none, so the closing is one file and there is no AD2p. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_knock/lib/A/AD2o.v, with its module paths and module names changed; 34 of its 65 lines of code are new or changed and 19 lines of the source are left out. *)
(* fuzz_codec's image-A closing assembly, in the form of projects/libreac/fuzz_knock/proofs/lib/A/AD2o.v: lib/A/CodecClose.v's
   asan Section at its parts. The start-up is the certificate (AB01.HS_tfib, AB12.TFIB, AB1n.tfib_startup_T1); the
   record is AD2l.TfibB, its trace universe by reflexivity; the allocator parts are lib/A/CodecAllocClose.v's; the
   driver main is lib/A/AD1q.v DRV_MAINX with TfibB's facts, the read check, the stdio sites and the program contract
   LIBX (ACfn.tfib_lib_contract_x_all at ameter_triv / XL0 / CA_RLO .. CA_RHI). LIBX comes from the program walks
   through lib/A/Prog/CPgClose.v codec_lib_x_all_of_walks, so the two image-A statements rest on no premise. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libdiginet.fuzz_codec Require Statements.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require AgreeCodec.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YG00 YG01 YG0f YG0d YC5d YCbp YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YG0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require AWalkFw0 AB01 AB12 AB1n ACejTfib AD2l AD2m AD1k AD1o AD1l AD1j AD1q ACfn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require CodecAllocClose CodecAsanTop CodecClose.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require CPgWalk CPgClose.
Local Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance AD1q.codec_ag_sil_shape.

(* The library shape of the driver core, AD1q.codec_ag_sil_shape, is the shape ASAN_T states
   (CodecAsanTop.codec_shape := AgreeCodec.ag_sil_shape): AD1q writes out AgreeShape.ag_shape at
   ZTraceSpec.checksum_shape, because it may not load lib/AgreeCodec.v. *)
Lemma codec_ag_sil_shape_eq : AD1q.codec_ag_sil_shape = AgreeCodec.ag_sil_shape.
Proof. reflexivity. Qed.

Section m.
(* The program contract the driver takes, at every run ceiling. *)
Hypothesis LIBX : forall rc : YM05.RunCeil,
  @ACfn.tfib_lib_contract_x_all rc AD1q.codec_ag_sil_shape AD2l.TfibB ameter_triv CPgClose.XL0 CPgClose.XL0
    CPgWalk.CA_RLO CPgWalk.CA_RHI.

(* CodecClose's H_DRIVER at B := AD2l.TfibB, from AD1q.DRV_MAINX. H_DRIVER hands over the three allocator parts for
   every FPState, DRV_MAINX takes them at YK11.fx0; DRV_MAINX's other parts are supplied here: TfibSyms
   (AD2l.TfibB_syms), the read check (AD2m.tfib_ARDCHK), MT_FREE (ameter_triv's mo_ok is True), RO_IN
   (CA_RLO .. CA_RHI is in_ro_tfa's second disjunct), LIBX, and the stdio sites (AD1k, AD1o, AD1l, AD1j).
   H_DRIVER's two trace premises are not used: AD2l.TfibB_syms carries them. *)
Lemma codec_driver_TfibB : forall rc : YM05.RunCeil,
  (forall fx : YK11.FPState, @amalloc_realizes fx rc AWalkFw0.tfibsegs AD2l.TfibB) ->
  (forall fx : YK11.FPState, @afree_realizes fx rc AWalkFw0.tfibsegs AD2l.TfibB) ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc AWalkFw0.tfibsegs AD2l.TfibB OCpy (pc_wrap_memcpy (as_code AD2l.TfibB))) ->
  universe_ok (as_universe AD2l.TfibB) ->
  (forall t, In t ACejTfib.Tfib_drv_traces -> In t (as_universe AD2l.TfibB)) ->
  CodecClose.drv_mainA AB01.HS_tfib AB12.TFIB rc.
Proof.
  intros rc AM AF AI _ _.
  exact (@AD1q.DRV_MAINX rc AD2l.TfibB AD2l.TfibB_syms (AM YK11.fx0) (AF YK11.fx0) (AI YK11.fx0)
    (AD2m.tfib_ARDCHK AD2l.TfibB AD2l.TfibB_syms)
    ameter_triv CPgClose.XL0 CPgClose.XL0 CPgWalk.CA_RLO CPgWalk.CA_RHI (fun _ _ => I) (fun a H => or_intror H)
    (LIBX rc)
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

(* CodecClose's asan Section at its parts. *)
Theorem ASAN_T_of_LIBX : CodecAsanTop.ASAN_T.
Proof.
  exact (CodecClose.ASAN_T_of_parts AB01.HS_tfib AB12.TFIB AB1n.tfib_startup_T1 AD2l.TfibB
    CodecAllocClose.codec_amalloc_closed CodecAllocClose.codec_afree_closed CodecAllocClose.codec_aicpy_closed eq_refl
    codec_driver_TfibB).
Qed.
End m.

(* The image-A obligation and the two image-A statements, with no premise: LIBX from the program walks
   (lib/A/Prog/CPgClose.v codec_lib_x_all_of_walks); LEAF holds by eq_refl at the driver's shape, because the
   harness writes no file and returns 0. *)
Theorem codec_ASAN_T_closed :
  CodecAsanTop.ASAN_T.
Proof.
  apply ASAN_T_of_LIBX. intros rc.
  exact (CPgClose.codec_lib_x_all_of_walks rc AD1q.codec_ag_sil_shape (fun _ _ _ => eq_refl)).
Qed.

Theorem codec_asan_agrees_closed :
  Statements.asan_agrees.
Proof.
  exact (CodecAsanTop.asan_agrees_of_asan_side codec_ASAN_T_closed).
Qed.

Theorem codec_asan_halts_closed :
  Statements.asan_halts.
Proof.
  exact (CodecAsanTop.asan_halts_of_asan_side codec_ASAN_T_closed).
Qed.
