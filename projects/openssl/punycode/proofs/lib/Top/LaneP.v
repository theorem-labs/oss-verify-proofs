(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.openssl.punycode.images Require Import Plain.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Ceiling Image Stage.
From OSSVerify.Proofs.openssl.punycode.lib.P Require Import Rnd Fz_iface.
From OSSVerify.Proofs.openssl.punycode.lib.P Require Impl_closed.
From OSSVerify.Proofs.openssl.punycode.lib.Spec Require Import ModelInv UnforcedK.
From OSSVerify.Proofs.openssl.punycode.lib Require Spec.
From OSSVerify.Proofs.openssl.punycode.lib.Top Require Import TopBridge PlainLane.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Theorem P_realizes_at :
  (forall (CE__ : Ceiling) (RN__ : RunRnd), @rfuzz_one_stmt CE__ RN__) ->
  forall lim : Z, (KLIM + SMALLREQ <= lim)%Z ->
  image_realizes psegs Plain.M.init_pc Plain.M.phdrs lim Spec.spec.
Proof.
  intros FUZZ lim Hlim. apply (plain_lane_realizes psegs pstage).
  - exact segs_low_psegs.
  - exact Hlim.
  - intros en inp Hve Hvi. exact (Impl_closed.impl_P_closed FUZZ en inp Hve Hvi).
Qed.

Theorem P_realizes_of :
  (forall (CE__ : Ceiling) (RN__ : RunRnd), @rfuzz_one_stmt CE__ RN__) ->
  image_realizes psegs Plain.M.init_pc Plain.M.phdrs source_alloc_limit Spec.spec.
Proof. intros FUZZ. apply (P_realizes_at FUZZ). unfold KLIM, SMALLREQ, source_alloc_limit. lia. Qed.

Theorem P_realizes_san_of :
  (forall (CE__ : Ceiling) (RN__ : RunRnd), @rfuzz_one_stmt CE__ RN__) ->
  image_realizes psegs Plain.M.init_pc Plain.M.phdrs sanitizer_source_limit Spec.spec.
Proof. intros FUZZ. apply (P_realizes_at FUZZ). unfold KLIM, SMALLREQ, sanitizer_source_limit. lia. Qed.
