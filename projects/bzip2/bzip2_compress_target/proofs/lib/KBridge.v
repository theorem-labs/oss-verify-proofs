(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics MemImageType.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Exec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Exec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module N := OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Exec.
Module K := OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib.Exec.

Lemma mstep_NK : forall segs a b, N.mstep segs a b <-> K.mstep segs a b.
Proof. intros; unfold N.mstep, K.mstep; tauto. Qed.

Lemma msteps_NK : forall segs a b, N.msteps segs a b -> K.msteps segs a b.
Proof. intros segs a b H; induction H; [apply K.msteps_refl|eapply K.msteps_cons; [apply mstep_NK; eassumption|assumption]]. Qed.

Lemma msteps_KN : forall segs a b, K.msteps segs a b -> N.msteps segs a b.
Proof. intros segs a b H; induction H; [apply N.msteps_refl|eapply N.msteps_cons; [apply mstep_NK; eassumption|assumption]]. Qed.

Theorem evt_NK : forall segs Q ms, N.evt segs Q ms <-> K.evt segs Q ms.
Proof.
  intros segs Q ms; split; intros (ms' & H & HQ); exists ms'; (split; [|exact HQ]).
  - apply msteps_NK; exact H.
  - apply msteps_KN; exact H.
Qed.
