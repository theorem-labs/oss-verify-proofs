(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/omx-clap-core/fuzz_preset/lib/AU/ErrnoWordB.v, with its module paths changed. *)
(* Theorem Labs, 2026-10: the instance witness, at image B' (fuzz_preset.asan-ubsan, #102 pin d663f82d7f48, unstripped
   twin c90d4fa54d43), of fuzz_preset row A4's image premise YGcfReallocCompose.errno_word_cf (YGcfReallocCompose.v:505:
   errno's four bytes are a 64-bit address range). errno_word_cf reads as_errno B only, so it takes the asyms record B
   alone (no segs). errno_word_cf_B states it at every B with TfibSyms B (Reusable/YF0m.v), the form its users take:
   AU/AllocAssembleB.v (:49, :75) at Reusable/YD2l.v's closed record TfibB with TfibB_syms, and
   AU/PresetUnitFactsB.v (:195) at its own record and TfibSyms. Image B''s closed record TfibB is not named
   here.
   as_errno = TFIB_ERRNO = 0x5de68c (Reusable/YF0m.v:20; TfibSyms's ts_errno) = builtin_tls + 0x24 = TFIB_TP - 0xa4 in
   the image's own .symtab (builtin_tls 0x5de668, TFIB_TP 0x5de730): the errno slot of musl's initial thread descriptor.
   Start-up facts only; no function is proved here (rule 24). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0f YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfReallocCompose.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Lemma errno_word_cf_B : forall B, YF0m.TfibSyms B -> YGcfReallocCompose.errno_word_cf B.
Proof.
intros B HT. assert (P : 2 ^ 64 = 18446744073709551616) by reflexivity.
unfold YGcfReallocCompose.errno_word_cf. rewrite (YF0m.ts_errno B HT), P. unfold YF0m.TFIB_ERRNO. lia.
Qed.

Print Assumptions errno_word_cf_B.
