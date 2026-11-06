(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1d7 X1cx X1cy X1cj X1cs.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X0fy X0fg X0jc X0eh X081.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X16j X161 X19t X152 X0ys.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X152 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys.
Import ListNotations.
Open Scope Z_scope.

Lemma io_lib_consts : forall m, io_consts m -> lib_consts m.
Proof.
intros m (_ & H & _). unfold lib_consts, LIB_TABLES. unfold io_ro in H.
do 13 (apply Forall_cons_iff in H as [_ H]). exact H.
Qed.

Theorem rta_lib_consts : forall Σ m, ART_A Σ m -> lib_consts m.
Proof. intros Σ m HA. exact (io_lib_consts m (rta_io Σ m HA)). Qed.

Theorem rta_acc_stderr_var : forall Σ m, ART_A Σ m -> acc bsegs m 0xfc010 8.
Proof. intros Σ m HA. exact (io_acc_at m (rta_io Σ m HA) 0xfc010 8 ltac:(io_in)). Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.

Lemma io_lib_consts : forall m, io_consts m -> lib_consts m.
Proof.
intros m (_ & H & _). unfold lib_consts, LIB_TABLES. unfold io_ro in H.
do 13 (apply Forall_cons_iff in H as [_ H]). exact H.
Qed.

Theorem rta_lib_consts : forall Σ m, ART_A Σ m -> lib_consts m.
Proof. intros Σ m HA. exact (io_lib_consts m (rta_io Σ m HA)). Qed.

Theorem rta_acc_stderr_var : forall Σ m, ART_A Σ m -> acc asegs m 0xf3790 8.
Proof. intros Σ m HA. exact (io_acc_at m (rta_io Σ m HA) 0xf3790 8 ltac:(io_in)). Qed.
