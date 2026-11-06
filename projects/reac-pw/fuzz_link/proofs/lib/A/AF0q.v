(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0q.v, with its module paths changed, names TfibSyms -> PcapSyms. pcap_afree_realizes applies afree_realizes_closed to lib/A/AD2l.v's PcapB in the form of lib/A/PcapClose.v's row 9 (H_ALLOC_FREE). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK04 YA0n YG00 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YA00.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YF0p.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AFfs.
From OSSVerify.reac_pw.fuzz_link.images Require Asan.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AD2l.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem afree_realizes_closed : forall B, PcapSyms B -> (forall t, as_dhash B t = tfib_dhash t) -> afree_realizes tfibsegs B.
Proof. intros B TS HD. exact (afree_realizes_all B TS HD). Qed.
End a.
(* lib/A/PcapClose.v row 9 (H_ALLOC_FREE) at B := PcapB (donor lib/A/AD1q.v:44 AFREE, closed by AF0q.v:12). *)
Theorem pcap_afree_realizes : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @afree_realizes fx rc OSSVerify.reac_pw.fuzz_link.images.Asan.M.loaded_segments PcapB.
Proof. intros rc fx. exact (afree_realizes_closed PcapB PcapB_syms (fun _ => eq_refl)). Qed.
