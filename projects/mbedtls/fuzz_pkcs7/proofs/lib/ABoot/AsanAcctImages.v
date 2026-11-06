(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State.
From OSSVerify.mbedtls.fuzz_pkcs7.images Require Import
  Asan AsanUbsan.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanAcct.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import PropExec.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanAcctImages () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.le"; "Asan_top"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.ABoot.AsanAcct.H_off_segments"; "OSSVerify.KrImg.Tgt_fuzz_pkcs7_asan.Tgt_fuzz_pkcs7_asan_loaded_segments"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.ABoot.AsanAcct.ranges_from_b"; "OSSVerify.KrLib.ABoot.AsanAcct.mkH"; "Both_top"; "OSSVerify.KrImg.Tgt_fuzz_pkcs7_both.Tgt_fuzz_pkcs7_both_loaded_segments"].


(* [comment removed for export] *)
Definition Asan_top : Z := 0x65b000%Z.
Lemma Asan_wx_nowrap : wx_segs_nowrap Asan_loaded_segments.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma Asan_segs_below : segs_below_b Asan_loaded_segments Asan_top = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Asan_H_off_above : ltac2:(CDefT.buildp (gd_tbl_AsanAcctImages ()) "PH,P,(0.&40.)$1.P,Pa,(0.&40.)P,(2.$1.A1.R2.R1.$3.)(4.$5.(6.&40.R2.))(7.$8.R2.)")
(* [comment removed for export] *).
Proof. intros H Ha. exact (H_off_segments_above _ H _ Asan_segs_below Ha). Qed.
Lemma Asan_H_off_mkH : ltac2:(CDefT.buildp (gd_tbl_AsanAcctImages ()) "PL,(9.(:.(0.&40.)(0.&40.)))PA,(9.(:.$;.$;.))P,(2.$1.(<.R2.$5.)$3.)(7.$8.(=.R3.R2.))")
(* [comment removed for export] *).
Proof. intros L A HL. exact (H_off_segments_mkH _ L A _ Asan_segs_below HL). Qed.

(* [comment removed for export] *)
Definition Both_top : Z := 0x65f000%Z.   (* [comment removed for export] *)
Lemma Both_wx_nowrap : wx_segs_nowrap AsanUbsan_loaded_segments.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma Both_segs_below : segs_below_b AsanUbsan_loaded_segments Both_top = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Both_H_off_above : ltac2:(CDefT.buildp (gd_tbl_AsanAcctImages ()) "PH,P,(0.&40.)$1.P,Pa,(0.&40.)P,(2.$1.A1.R2.R1.$3.)(4.$>.(6.&40.R2.))(7.$?.R2.)")
(* [comment removed for export] *).
Proof. intros H Ha. exact (H_off_segments_above _ H _ Both_segs_below Ha). Qed.
Lemma Both_H_off_mkH : ltac2:(CDefT.buildp (gd_tbl_AsanAcctImages ()) "PL,(9.(:.(0.&40.)(0.&40.)))PA,(9.(:.$;.$;.))P,(2.$1.(<.R2.$>.)$3.)(7.$?.(=.R3.R2.))")
(* [comment removed for export] *).
Proof. intros L A HL. exact (H_off_segments_mkH _ L A _ Both_segs_below HL). Qed.

