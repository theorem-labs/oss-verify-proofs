(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bs X1c2 X1bn.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1qs X1ra X1qu X1r3 X1r6 X1og X1qw X1pe X1ot.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib Require Import TopLevel.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
Open Scope Z_scope.

Local Notation psegs := Plain.M.loaded_segments.
Local Notation usegs := Ubsan.M.loaded_segments.

Theorem prog_model_ok : forall segs rs pc ph lim en inp,
0 < reserved_top (segments_reserved segs) ->
reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling_lo ->
reserved_top (segments_reserved segs) + brk_aslr_max + PGSZ <= 2^40 ->
LBUDGET <= lim ->
valid_entry (mkImage segs pc ph) en inp -> valid_input_core inp ->
leaves_unreachable_m nstep (prog segs rs (ceil_of en) (in_argv inp)) (mo0 segs lim en inp)
/\ tsafe nstep nsafe (prog segs rs (ceil_of en) (in_argv inp)) (mo0 segs lim en inp).
Proof.
intros segs rs pc ph lim en inp Hpos Hceil H40 Hlim VE VI.
apply (X1qw.prog_model_ok segs rs pc ph lim en inp Hpos Hceil VE VI).
exact (X1ot.prog_no_enomem segs rs pc ph lim en inp Hpos Hceil H40 Hlim VE VI).
Qed.

Theorem prog_plain_model_ok : forall en inp,
valid_entry (mkImage psegs Plain.M.init_pc Plain.M.phdrs) en inp -> valid_input_core inp ->
leaves_unreachable_m nstep (prog_plain psegs RSTAGE_plain (ceil_of en) (in_argv inp)) (mo0 psegs source_alloc_limit en inp)
/\ tsafe nstep nsafe (prog_plain psegs RSTAGE_plain (ceil_of en) (in_argv inp)) (mo0 psegs source_alloc_limit en inp).
Proof. intros en inp Hv Hi. exact (prog_plain_model_okN en inp Hv Hi (prog_no_enomem_plain en inp Hv Hi)). Qed.

Theorem prog_plain_model_ok_at : forall lim en inp, LBUDGET <= lim ->
valid_entry (mkImage psegs Plain.M.init_pc Plain.M.phdrs) en inp -> valid_input_core inp ->
leaves_unreachable_m nstep (prog_plain psegs RSTAGE_plain (ceil_of en) (in_argv inp)) (mo0 psegs lim en inp)
/\ tsafe nstep nsafe (prog_plain psegs RSTAGE_plain (ceil_of en) (in_argv inp)) (mo0 psegs lim en inp).
Proof.
intros lim en inp Hlim Hv Hi. unfold prog_plain.
eapply prog_model_ok; [apply reserved_top_psegs| apply ceil_psegs| apply sbk_psegs| exact Hlim| exact Hv| exact Hi].
Qed.

Theorem prog_ubsan_model_ok : forall en inp,
valid_entry (mkImage usegs Ubsan.M.init_pc Ubsan.M.phdrs) en inp -> valid_input_core inp ->
leaves_unreachable_m nstep (prog_ubsan usegs RSTAGE_ubsan (ceil_of en) (in_argv inp)) (mo0 usegs target_alloc_limit en inp)
/\ tsafe nstep nsafe (prog_ubsan usegs RSTAGE_ubsan (ceil_of en) (in_argv inp)) (mo0 usegs target_alloc_limit en inp).
Proof. intros en inp Hv Hi. exact (prog_ubsan_model_okN en inp Hv Hi (prog_no_enomem_ubsan en inp Hv Hi)). Qed.
