(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFhu.v (donor image sha256 7093581aab04), with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/AFhu.v (donor image sha256 43654a025fd0), with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/AFhu.v of this library by derive_y.py: module names A.Axyz -> AU.Yxyz, addresses moved from reac-pw/fuzz_role's asan image to its asan-ubsan image. The Modified-by lines above describe how lib/A/AFhu.v was made and quote that file's asan-image values; the code below carries the asan-ubsan values. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0l YG00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import YF0x YFhy YFhz.
Import ListNotations. Open Scope Z_scope.
Lemma sweep6a : forallb (fun i => zev (fun _ => 33288 + 8 * Z.of_nat i) CL_hi =? class_id (33288 + 8 * Z.of_nat i)) (seq 0 1008) = true.
Proof. vm_compute. reflexivity. Qed.
