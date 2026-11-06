(* Theorem Labs, 2026-10 (a Theorem Labs lane, a working branch): the free interface's quarantine byte premise
   YGcfInstFreeQ.QB_BYTES (YGcfInstFreeQ.v:44) at lane F2b's drain-entry premise QB := YGcfInstDrainR.QB_cf kQuarantineMax
   (YGcfInstDrainR.v:262), over image A's modules.  rule 24: proves no function (kind: statement text; a model fact).

   QB_BYTES QB says: for every allocator state X with QB X, qc_bytes (st_qthread X) + qc_bytes (st_qglobal X) <= 2 ^ 31
   (the two quarantine caches together hold at most 2 ^ 31 bytes; DMiface.qview's qv_bytes).  QB_cf NMAXD X is a
   conjunction whose FIRST conjunct is that bound, so the proof is its first projection.  It reads no numeral of the
   image and holds for every NMAXD; kQuarantineMax (lib/Reusable/YG00.v:28) is only the argument the consumer names.

   Relocated from cgif's YGcfInstFreeImgcgif.QB_BYTES_qbcf (a working branch 807fff6eccda,
   proofs/cgif/cgif_file_fuzzer/lib/YGcfInstFreeImgcgif.v:243), at NMAXD := kQuarantineMax.  The definitions of
   QB_BYTES and QB_cf are textually the same in that tree and in this one. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YM05 YG00 YGcfNames.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfInstFreeQ YGcfInstDrainR.

Section q. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

Theorem qb_bytes_reply_A : YGcfInstFreeQ.QB_BYTES (YGcfInstDrainR.QB_cf kQuarantineMax).
Proof. intros X H. exact (proj1 H). Qed.

End q.
