(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/ACeg.v, with its module paths changed, and its fuzz_reply.asan addresses relocated from cgif_file_fuzzer.asan (8 numerals; per-numeral report). *)
(* Modified by Theorem Labs, 2026-10: lib_const_addr named cgif's program constants (its .rodata table at 0x103b0 and .got slots 0x9ec10..0x9ec28), which have no twin in fuzz_reply.asan; it is False here (fuzz_reply's program reads its constants through the contract's read-only range RLO..RHI). *)
(* Modified by Theorem Labs, 2026-11: made from A/ACeg.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YP0m YP0e YP09 YP02 YP0l YP03 YP00 YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.BudgetWit.AW Require Import YA0n_w.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.BudgetWit.AW Require Import YG0n_w YG0s_w YG0d_w YCe5_w.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import Asan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AF0l ACej.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c.
Lemma Hwx_tfa : wx_segs_nowrap tfibsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma tfib_img_range : forall a, in_img tfibsegs a -> 0x10000 <= a < 0x5fb000.
Proof.
intros a (sg & Hin & Hr).
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg))
(map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
vm_compute in H.
destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.
End c.
