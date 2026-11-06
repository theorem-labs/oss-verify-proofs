(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGhr.v (commit 30a1993588f, c5 + memnorm; file sha256 8730081364c9) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from lib/A/AGhr.v (commit d2dafa219c1, file sha256 ee4bc46dd341) onto plugin-hostd/fuzz_reply's asan-ubsan image (unstripped fuzz_reply.asan-ubsan, sha256 3389287e1d61; pin 10ffb5f9202a) by alreloc ced0368250cb6538 (A -> B, direct map 541d2a13b9d2): 0 numerals moved; module paths lib.A -> lib.B and the image twins A<r> -> Y<r>. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0l YG00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YF0x YFhy AGhy AGhz.
Import ListNotations. Open Scope Z_scope.
Lemma sweep4b : forallb (fun i => zev (fun _ => 10312 + 8 * Z.of_nat i) CL_hi =? class_id (10312 + 8 * Z.of_nat i)) (seq 0 760) = true.
Proof. vm_compute. reflexivity. Qed.
