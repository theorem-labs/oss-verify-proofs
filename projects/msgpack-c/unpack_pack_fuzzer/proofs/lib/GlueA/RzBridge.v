(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require ShapeAlg SpinAlg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module RzBridge.
Module OUR := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Module DON := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.ShapeAlg.
Module SPN := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.SpinAlg.

Theorem realizes_bridge : forall segs c T, OUR.realizes segs c T -> DON.realizes segs c T.
Proof.
  intros segs c T H. induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq].
  - exact (DON.rz_node segs c I evs nx T i0 Hnode IH).
  - exact (DON.rz_halt segs c Hh).
  - exact (DON.rz_conseq segs c T T' IH Heq).
Qed.

Theorem srealizes_bridge : forall segs c T, OUR.realizes segs c T -> SPN.srealizes segs c T.
Proof. intros segs c T H. apply SPN.srealizes_of_realizes. apply realizes_bridge. exact H. Qed.

(* [comment removed for export] *)
Theorem realizes_bridge_inv : forall segs c T, DON.realizes segs c T -> OUR.realizes segs c T.
Proof.
  intros segs c T H. induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq].
  - exact (OUR.rz_node segs c I evs nx T i0 Hnode IH).
  - exact (OUR.rz_halt segs c Hh).
  - exact (OUR.rz_conseq segs c T T' IH Heq).
Qed.

Theorem realizes_of_srealizes_bridge : forall segs c T, SPN.srealizes segs c T -> OUR.realizes segs c T.
Proof. intros segs c T H. apply realizes_bridge_inv. apply SPN.realizes_of_srealizes. exact H. Qed.

End RzBridge.
