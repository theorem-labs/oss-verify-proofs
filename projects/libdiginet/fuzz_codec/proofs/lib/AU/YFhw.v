(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFhw.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/libreac/fuzz_knock/proofs/lib/A/AFhw.v (donor image sha256 61768cf4739b), with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/AFhw.v of this library by derive_y.py: module names A.Axyz -> AU.Yxyz, addresses moved from libdiginet/fuzz_codec's asan image to its asan-ubsan image. The Modified-by lines above describe how lib/A/AFhw.v was made and quote that file's asan-image values; the code below carries the asan-ubsan values. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0l YG00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import YF0x YFhy YFhz.
Import ListNotations. Open Scope Z_scope.
Lemma sweep6c : forallb (fun i => zev (fun _ => 49416 + 8 * Z.of_nat i) CL_hi =? class_id (49416 + 8 * Z.of_nat i)) (seq 0 1008) = true.
Proof. vm_compute. reflexivity. Qed.
