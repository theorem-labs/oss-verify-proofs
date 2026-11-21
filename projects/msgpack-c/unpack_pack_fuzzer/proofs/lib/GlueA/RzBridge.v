(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the bridges pass rz_node's RomBase.sys_rob premise; run_init_our lifts a walk over a binary's own segments to the run's segment list through AS.RomStable.run_init). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require ShapeAlg SpinAlg RomStable.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module RzBridge.
Module OUR := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Module DON := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.ShapeAlg.
Module SPN := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.SpinAlg.

Theorem realizes_bridge : forall segs c T, OUR.realizes segs c T -> DON.realizes segs c T.
Proof.
  intros segs c T H. induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq].
  - exact (DON.rz_node segs c I evs nx T i0 Hnode Hrob IH).
  - exact (DON.rz_halt segs c Hh).
  - exact (DON.rz_conseq segs c T T' IH Heq).
Qed.

Theorem srealizes_bridge : forall segs c T, OUR.realizes segs c T -> SPN.srealizes segs c T.
Proof. intros segs c T H. apply SPN.srealizes_of_realizes. apply realizes_bridge. exact H. Qed.

(* [comment removed for export] *)
Theorem realizes_bridge_inv : forall segs c T, DON.realizes segs c T -> OUR.realizes segs c T.
Proof.
  intros segs c T H. induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq].
  - exact (OUR.rz_node segs c I evs nx T i0 Hnode Hrob IH).
  - exact (OUR.rz_halt segs c Hh).
  - exact (OUR.rz_conseq segs c T T' IH Heq).
Qed.

Theorem realizes_of_srealizes_bridge : forall segs c T, SPN.srealizes segs c T -> OUR.realizes segs c T.
Proof. intros segs c T H. apply realizes_bridge_inv. apply SPN.realizes_of_srealizes. exact H. Qed.

(* LPS 727298f3 (run_segments, from 75d69e00): the run reads the binary against its segment list
   followed by the vDSO pair.  A walk over the binary's own list, from the binary's start, is a walk
   of the run from the run's start ([AS.RomStable.run_init], through the two bridges). *)
Theorem run_init_our : forall segs inp (sp mb : word) pc ph brk rnd lim T,
  vdso_image segs = None ->
  OUR.realizes segs (init_config segs pc ph sp brk mb rnd lim inp) T ->
  OUR.realizes (run_segments segs inp sp mb)
    (init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp) T.
Proof.
  intros segs inp sp mb pc ph brk rnd lim T Hvi H.
  apply realizes_bridge_inv. apply (RomStable.run_init segs inp sp mb pc ph brk rnd lim T Hvi).
  apply realizes_bridge. exact H.
Qed.

End RzBridge.
