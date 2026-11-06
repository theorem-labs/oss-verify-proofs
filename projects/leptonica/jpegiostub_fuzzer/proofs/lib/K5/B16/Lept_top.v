(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.B16 Require Import RT_iface RT_gaps_iface Lept_iface
  Lept_stderr Lept_err Lept_hdr Lept_create LeptC_cmapdeser LeptC_cmapdestroy LeptC_cmapvalid LeptC_setcmap LeptM_destroy LeptC_padbits Lept_zero Lept_gmax Lept_fuzz.

Section Top.
Variable RT : rt_sig.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.

Definition AFt : art_facts RT := rc_facts RT RC.
Definition SEt : lept_stderr_cps RT := lept_stderr_ok RT AFt RC GP.
Definition REIt : returnError_cps RT e_returnErrorInt := returnError_ok RT AFt GP SEt e_returnErrorInt (or_introl eq_refl).
Definition REPt : returnError_cps RT e_returnErrorPtr := returnError_ok RT AFt GP SEt e_returnErrorPtr (or_intror eq_refl).
Definition HDRt : pixCreateHeader_cps RT := pixCreateHeader_ok RT AFt GP SEt REPt.
Definition ZEROt : pixZero_cps RT := pixZero_ok RT AFt GP.
Definition GMAXt : pixGetMaxColorIndex_cps RT := pixGetMaxColorIndex_ok RT AFt GP ZEROt.
Definition CMDESt : pixcmapDeserialize_cps RT := pixcmapDeserialize_ok RT AFt GP.
Definition CMDt : pixcmapDestroy_cps RT := pixcmapDestroy_ok RT AFt GP (gp_free RT GP).
Definition VALIDt : pixcmapIsValid_cps RT := pixcmapIsValid_ok RT AFt GP SEt REIt GMAXt.
Definition SETCMt : pixSetColormap_cps RT := pixSetColormap_ok RT AFt GP REIt VALIDt.
Definition DESTROYt : pixDestroy_cps RT := pixDestroy_ok RT AFt GP CMDt.

Definition PADt : pixSetPadBits_cps RT := pixSetPadBits_ok RT AFt GP SEt REIt.
Definition CREt : pixCreate_cps RT := pixCreate_ok RT AFt RC GP HDRt PADt REPt.

(* [comment removed for export] *)
Hypothesis DESER : pixDeserialize_cps RT.

Theorem cone_of_open : Lept_iface.fuzz_one_cps RT.
Proof. exact (fuzz_one_ok RT AFt RC GP DESER DESTROYt). Qed.
End Top.
