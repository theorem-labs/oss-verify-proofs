(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/ACeg.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/ACeg.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YP0m YP0e YP09 YP02 YP0l YP03 YP00 YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.BudgetWit.AW Require Import YA0n_w.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG00 YG0a YG01 YG0f.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.BudgetWit.AW Require Import YG0n_w YG0s_w YG0d_w YCe5_w.
From OSSVerify.libreac.fuzz_scene.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YI09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import AB1v AF0l ACej.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c.
Lemma Hwx_tfa : wx_segs_nowrap tfibsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
End c.
