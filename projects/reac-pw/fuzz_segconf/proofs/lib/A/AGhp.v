(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGhp.v (cold/c-frame-alloc-dgraw-frozen ced28ed2383, file sha256 0ebb7da8c1fa) onto omx-clap-core/fuzz_state's asan image (unstripped fuzz_state.asan, sha256 7c4afaee248b); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/omx-clap-core/fuzz_state/lib/A/AGhp.v (donor image sha256 64b53ff86172), with its module paths changed. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0l YG00.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AF0x AFhy AGhy AGhz.
Import ListNotations. Open Scope Z_scope.
Lemma sweep3 : forallb (fun i => zev (fun _ => 584 + 8 * Z.of_nat i) CL_hi =? class_id (584 + 8 * Z.of_nat i)) (seq 0 440) = true.
Proof. vm_compute. reflexivity. Qed.
