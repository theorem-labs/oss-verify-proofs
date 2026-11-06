(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from part of proofs/cgif/cgif_file_fuzzer/lib/A/ACfi.v (link_ML, link_SMP, link_FFL, link_ASF, link_AMEMSET, link_AMEMCPY, tfib_ROB) for libreac/fuzz_grant: the facts are stated at GrantB and at the listing's instance PI_grant, the stack_malloc, bcmp and set_shadow_f5 entries of the memory-checking runtime, the walks' PALib and PALibF records, the shadow of the image and of its registered globals, the image's read-only tables and the image facts of ctrl_finish and reac_ctrl_parse are added; module paths changed. *)
(* Modified by Theorem Labs, 2026-10: adapted from lib/A/Prog/GrantClose.v for image B (fuzz_grant.asan-ubsan). *)
(* Modified by Theorem Labs, 2026-10: from proofs/libreac/fuzz_grant/lib/B/GrantBCloseInst.v only the malloc / free step (grantB_MALLOC / grantB_FREE) is kept, renamed uciB_MALLOC / uciB_FREE and stated at reac-repacer/fuzz_uci's image-B runtime record UciB with UciB_syms; module paths changed. *)
(* The memory-checking runtime's malloc and free entries at image B, PROVED at UciB (lib/B/YD2l.v:17). This file proves
   no function: each entry is taken by the B core's closed realizer of it, lib/B/YF0w.v tfib_amalloc_realizes and
   lib/B/YF0q.v afree_realizes_closed, whose two premises hold at UciB: the symbol record by UciB_syms
   (lib/B/YD2l.v:75), and the depot hash by reflexivity (UciB's as_dhash is tfib_dhash, lib/B/YD2l.v:35).
   Both lemmas are stated to the landed predicates amalloc_realizes / afree_realizes verbatim, for every float state
   fx and run ceiling rc, so uciB_FREE also gives the shape `forall fx, P fx -> afree_realizes (fx := fx) tfibsegs B`
   that lib/B/YD1q.v takes, for any P. *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK11 YM05 YG0f YG0d.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YB1v YF0m YD2l YF0w YF0q.

Lemma uciB_MALLOC : forall (fx : YK11.FPState) (rc : YM05.RunCeil), @amalloc_realizes fx rc tfibsegs UciB.
Proof. intros fx rc. exact (@tfib_amalloc_realizes fx rc UciB UciB_syms (fun t => eq_refl)). Qed.

Lemma uciB_FREE : forall (fx : YK11.FPState) (rc : YM05.RunCeil), @afree_realizes fx rc tfibsegs UciB.
Proof. intros fx rc. exact (@afree_realizes_closed fx rc UciB UciB_syms (fun t => eq_refl)). Qed.
