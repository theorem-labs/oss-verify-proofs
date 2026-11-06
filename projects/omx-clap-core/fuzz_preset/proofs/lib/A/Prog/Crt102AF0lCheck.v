(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the parts of sup_instance_info's ASan+UBSan walk (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan) that need no callee statement: the walk's points in B's listing, the 122 slots, the
   96-byte frame and its realignment, the entry seed, the two image literals it hands to a callee and to the
   snprintf entry, and the frame chain each callee gets for s0 (achain_push on afn_pre's chain). In the form of
   lib/B/Prog/sup_reset_aux.v (a working branch 93eeb37e147: the listing facts, the literal's shadow from
   the allocator record, the seeds) after the A walks lib/A/Prog/sup_instance_info.v (a working branch
   0de7ca03d26) and lib/A/Prog/answer_code.v (a working branch 2ba4488ce71: the side-stack frame, its header
   and shadow, the realignment arithmetic) and lib/A/Prog/arg_i_s0.v, arg_i_s1.v (a working branch
   12dc52bfe84: the "%d" text). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/sup_instance_info_aux.v, with its module paths and module names changed; 9 of its 18 lines of code are new or changed and 370 lines of the source are left out. *)
(* fuzz_preset, the crt102 walk: the AF0l BINDING CHECK at A' for the code addresses this lane's stand-ins read through
   `as_code B` (the family lead's standing item: take AF0l dfca6bb1a8d7, then vm_compute the binding and report it).

   Crt102Entry's MARKED STAND-IN `pal_stack_malloc3 : SIGMA AS___asan_stack_malloc_3 = pc_stack_malloc (as_code B) 3`
   and Crt102Kit's `crt102rw_free_trace` (`pc_free_ra0 (as_code B)`) read AF0l's Tfib_code once B is bound to the
   Tfib record. Under the BASE AF0l eb3d91d8c440 both were FALSE at A' (0x3ddb8 / 0x537e4, each 0x94 below the #102
   listing's 0x3de4c / AF0m's DRV_TRACES 0x53878). This file checks the #102 AF0l dfca6bb1a8d7 (the A' relocation
   at commit 8d8257111dff, taken by path from the #102 integration at commit b1f516db3e6) against the listing of record
   (listing v3, commit 74dcda1eda12) by vm_compute, for every pc field this lane's frame and call rules bind.
   The ADDRESS literals below are the claims being checked, not inputs to any proof. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0f YPsym YC4aP YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog AF0l.
Open Scope Z_scope.

(* PI_prog_A is stated over a run ceiling; the listing's pcs do not depend on it *)
Section s. Context {rc : YM05.RunCeil}.
(* the three frame classes' __asan_stack_malloc_N: the listing's symbol = AF0l's pc_stack_malloc N *)
Lemma crt102_af0l_stack_malloc0 : pa_sigma (PAImg := PI_prog_A) AS___asan_stack_malloc_0 = pc_stack_malloc Tfib_code 0.
Proof. vm_compute. reflexivity. Qed.
Lemma crt102_af0l_stack_malloc1 : pa_sigma (PAImg := PI_prog_A) AS___asan_stack_malloc_1 = pc_stack_malloc Tfib_code 1.
Proof. vm_compute. reflexivity. Qed.
Lemma crt102_af0l_stack_malloc3 : pa_sigma (PAImg := PI_prog_A) AS___asan_stack_malloc_3 = pc_stack_malloc Tfib_code 3.
Proof. vm_compute. reflexivity. Qed.
(* the wrappers the free / malloc traces start from *)
Lemma crt102_af0l_wrap_free : pa_sigma (PAImg := PI_prog_A) AS___wrap_free = pc_wrap_free Tfib_code.
Proof. vm_compute. reflexivity. Qed.
Lemma crt102_af0l_wrap_malloc : pa_sigma (PAImg := PI_prog_A) AS___wrap_malloc = pc_wrap_malloc Tfib_code.
Proof. vm_compute. reflexivity. Qed.
(* the value itself, so the log shows the number *)
Eval vm_compute in (pc_stack_malloc Tfib_code 3, pc_free_ra0 Tfib_code, pc_malloc_ra0 Tfib_code).
End s.
