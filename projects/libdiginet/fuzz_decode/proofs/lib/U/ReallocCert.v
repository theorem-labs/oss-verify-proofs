From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import
  YK11 YM05 YO0d YH02 YN33.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import ZAllocator Contract AllocCut AllocForm.
Open Scope Z_scope.
(* The image's realloc contracts, in the sbound form (zlib_realloc, used by the sbound FrameProof) and the pack
(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/U/ReallocCert.v at bf7779f81ed764787b77895d2f5c0db2627f33f3 for libdiginet/fuzz_decode; no image value changed; module path OSSVerify.Proofs.libdiginet.fuzz_decode.lib. *)
   form (zlib_realloc_pack, used by the pack FrameProof). This image has no realloc (ms_realloc = None): vacuous.
   An image with realloc proves the one its FrameProof uses from realloc_contract_form /
   realloc_null_contract_form (sbound) or pack_realloc_contract / pack_realloc_null_contract (pack). *)
Section R. Context {fx : FPState} {rc : RunCeil}.
Lemma zlib_realloc : forall pc, ms_realloc src0_msyms = Some pc ->
  realloc_contract src0_msyms (@zlib_API rc) pc /\ realloc_null_contract src0_msyms (@zlib_API rc) pc.
Proof using. intros pc H. vm_compute in H. discriminate H. Qed.
Lemma zlib_realloc_pack : forall pc, ms_realloc src0_msyms = Some pc ->
  realloc_contract_r src0_msyms (@zlib_API rc) pack_form pc /\
  realloc_null_contract_r src0_msyms (@zlib_API rc) pack_form pc.
Proof using. intros pc H. vm_compute in H. discriminate H. Qed.
End R.
