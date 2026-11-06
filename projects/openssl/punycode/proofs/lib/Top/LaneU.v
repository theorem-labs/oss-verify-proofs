(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.openssl.punycode.images Require Import Ubsan.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Ceiling Image Stage.
From OSSVerify.Proofs.openssl.punycode.lib.P Require Import Rnd.
From OSSVerify.Proofs.openssl.punycode.lib.U Require Import Fz_iface.
From OSSVerify.Proofs.openssl.punycode.lib.U Require Impl_closed.
From OSSVerify.Proofs.openssl.punycode.lib.Spec Require Import ModelInv UnforcedK.
From OSSVerify.Proofs.openssl.punycode.lib Require Spec.
From OSSVerify.Proofs.openssl.punycode.lib.Top Require Import TopBridge PlainLane.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem U_realizes_of :
  (forall (CE__ : Ceiling) (RN__ : RunRnd), @rfuzz_one_stmt CE__ RN__) ->
  image_realizes usegs Ubsan.M.init_pc Ubsan.M.phdrs target_alloc_limit Spec.spec.
Proof.
  intros FUZZ. apply (plain_lane_realizes usegs ustage).
  - exact segs_low_usegs.
  - unfold KLIM, SMALLREQ, target_alloc_limit. lia.
  - intros en inp Hve Hvi. exact (Impl_closed.impl_U_closed FUZZ en inp Hve Hvi).
Qed.
