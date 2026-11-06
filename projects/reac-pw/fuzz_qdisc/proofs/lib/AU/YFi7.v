(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFi7.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/A/AFi7.v (donor image sha256 61768cf4739b), with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/AFi7.v of this library by derive_y.py: module names A.Axyz -> AU.Yxyz, addresses moved from reac-pw/fuzz_qdisc's asan image to its asan-ubsan image. The Modified-by lines above describe how lib/A/AFi7.v was made and quote that file's asan-image values; the code below carries the asan-ubsan values. *)
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YP0m.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.AU Require Import YFi6.
Import ListNotations. Open Scope Z_scope.
Lemma sweep_lo : sweep clz_okb (Z.to_nat 32750) 18 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
