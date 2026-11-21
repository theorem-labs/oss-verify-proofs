(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: relocated from cgif_file_fuzzer.asan to omx-clap-core fuzz_manifest.asan: 13 address literal(s) rewritten, module paths changed; lib_const_addr and the TfibLib field tl_lib_consts removed: they named cgif's library constants (a .rodata word and three GOT slots of cgif functions), which fm does not have; TFIB_IMG_END is ASAN_IMG_END, imported from ImgEnd. *)
(* Modified by Theorem Labs, 2026-11: made from A/ACeg.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YP0m YP0e YP09 YP02 YP0l YP03 YP00 YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.BudgetWit.AW Require Import YA0n_w.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.BudgetWit.AW Require Import YG0n_w YG0s_w YG0d_w YCe5_w.
From OSSVerify.omx_clap_core.fuzz_manifest.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AF0l ACej.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import ImgEnd.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c.
Lemma Hwx_tfa : wx_segs_nowrap tfibsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
End c.
