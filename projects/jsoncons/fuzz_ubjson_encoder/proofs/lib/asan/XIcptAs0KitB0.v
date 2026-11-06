(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound SegRun SegPlan XIcptAB0.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_XIcptAs0KitB0 () := "C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan8XIcptAB03XIA8xstep_okC13~~~C79OSSVerify8jsonconsCfuzz_ubjson_encoder6images9AsanUbsan1M?loaded_segmentsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan8XIcptAB03XIA8AS0_MSETC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan8XIcptAB03XIA8AS0_MCPYC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan8XIcptAB03XIA9AS0_CELLSC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan8XIcptAB03XIA9AS0_TLSPCC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan8XIcptAB03XIA:AS0_TCELLSC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan8XIcptAB03XIA7AS0_TPVC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan8XIcptAB03XIA8AS0_ENTVC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan8XIcptAB03XIA;AS0_CTXSLOTC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan8XIcptAB03XIA;AS0_BLKSLOTC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan=XIcptAs0KitB05XIAS09fill_specC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan=XIcptAs0KitB05XIAS09copy_specC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan=XIcptAs0KitB05XIAS08tls_specC13~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import AX2.
Open Scope Z_scope.
Module XIAS0.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition fill_spec : Prop := XIA.icpt_fill_spec RSEGS XIA.AS0_MSET XIA.AS0_CELLS.
Definition copy_spec : Prop := XIA.icpt_copy_spec RSEGS XIA.AS0_MCPY XIA.AS0_CELLS.
Definition tls_spec : Prop := XIA.icpt_tls_spec RSEGS XIA.AS0_TLSPC XIA.AS0_TCELLS XIA.AS0_TPV XIA.AS0_ENTV XIA.AS0_CTXSLOT XIA.AS0_BLKSLOT.
Definition xstep : list SGP.region -> nat -> sym_state -> option sym_state :=
  XIA.xstep RSEGS XIA.AS0_MSET XIA.AS0_MCPY XIA.AS0_CELLS XIA.AS0_TLSPC XIA.AS0_TCELLS XIA.AS0_TPV XIA.AS0_ENTV XIA.AS0_CTXSLOT XIA.AS0_BLKSLOT.
Theorem xstep_ok : fill_spec -> copy_spec -> tls_spec -> forall nx0 BR F M0, SGP.XSTEP_ok RSEGS nx0 BR xstep F M0.
Proof.
ltac2:(KReplay.run1 (kr_t_XIcptAs0KitB0 ()) [] "h02HCh12HFh22HTp;=g0000l=0Tg001Eg002Wg003lg005Ag006Wg007mg009Dg00:Xg00;mg00=Ef2R0f1R1f0R2M=0p=1g00>]g00@:g00AWA1012W2W0W1o"). Qed.
End XIAS0.
