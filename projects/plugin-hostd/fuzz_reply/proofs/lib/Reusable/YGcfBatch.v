(* CARRIED from a working branch 3dd49fa29fa14b99e3c465cacbfe79a09756bb26,
   proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcfBatch.v, sha256 2ef825b791be5437b281e02ce7a9eab3987c5c9f8cb5444385bcd3b1c7b314dd.
   DO NOT EDIT in this tree: change it on that branch and carry it again. The only change
   made here is the module prefix OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the event-free second allocator instance (suffix cf), the QUARANTINE BATCH BOUND.
   Every quarantine batch is a chunk of class kBatchClass (its b_self), so the batch count is bounded by that
   class's region: Compl0 ties the class's records to rg_alloc_user, and cls_ok_cf's re-based mapped bound caps
   rg_mapped_user at kFreeArrayOffset (nrec_bound_cf, YG01cf.v). class_size kBatchClass = 8,192 (YG00.v:44-48,
   c = 24: 512 << 4), so L24MAX_cf = 3,758,096,384 / 8,192 = 458,752. No event count, no address. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YGcfNames YG01cf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Definition L24MAX_cf : Z := kFreeArrayOffset / class_size kBatchClass.

Lemma L24MAX_cf_value : L24MAX_cf = 458752.
Proof. vm_compute. reflexivity. Qed.

Section B. Context {cp : CfParams}.

Theorem batches_bound_cf : forall U pp cc bb s, WfP_cf U pp cc bb s ->
Z.of_nat (length (all_batches s)) <= L24MAX_cf.
Proof.
intros U pp cc bb s W.
assert (Hc : 1 <= kBatchClass <= 31) by (unfold kBatchClass; lia).
destruct (nrec_bound_cf U pp cc bb s kBatchClass W Hc) as [H _].
pose proof (class_size_32 kBatchClass Hc) as Hcs.
assert (Hl : (length (all_batches s) <= length (class_elems s kBatchClass))%nat).
{ unfold class_elems, batch_offs. rewrite Z.eqb_refl.
rewrite !length_app, length_map. lia. }
apply Nat2Z.inj_le in Hl.
unfold L24MAX_cf. apply Z.div_le_lower_bound; [lia|]. nia.
Qed.

End B.
