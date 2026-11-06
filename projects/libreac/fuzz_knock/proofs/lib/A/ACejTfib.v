(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer's trace facts for libreac/fuzz_knock's ASan
   image, in the form fuzz_pcap's lib/A/ACejTfib.v states them. *)
(* libreac/fuzz_knock, fuzz_knock.asan (pin sha256 61768cf4739b...): the facts about the allocation-trace universe
   (lib/A/ACej.v Tfib_universe, regenerated from that image) that cgif_file_fuzzer's TFIB_T closing takes at its entry
   points:
   - donor lib/A/AD2l.v:37 `as_universe := Tfib_universe`: ACej.Tfib_universe (re-exported here);
   - donor lib/A/AD2l.v:78, field ts_universe (donor lib/A/AF0m.v:313) `universe_ok (as_universe B)`:
     ACej.Tfib_universe_ok;
   - donor lib/A/AD2l.v:79-82, field ts_universe_drv (donor lib/A/AF0m.v:314)
     `forall t, In t DRV_TRACES -> In t (as_universe B)`: Tfib_universe_drv below, over Tfib_drv_traces, the list that
     knock's lib/A/AF0m.v DRV_TRACES is.
   This file proves no function's walk (OSS Verify rule 24). *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG00 YG01.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Export ACej.
Import ListNotations.
Local Open Scope Z_scope.
(* The driver's allocation traces, in the order and form of knock's lib/A/AF0m.v:23-31 DRV_TRACES (the same traces as
   ACej.v's TRACES_main and TRACES_target_run, with the two one-element prefixes): main's two malloc calls and
   target_run's one return to 0x7ea84 / 0x7ead8 / 0x7ed64 from the malloc wrapper at 0x5160c, main's two free calls and
   target_run's one returning to 0x7eafc / 0x7ec2c / 0x7edf8 from the free wrapper at 0x514ac, and the two one-word
   traces (the frame0_ok = false case). *)
Definition Tfib_drv_traces : list (list Z) :=
[[0x5160c; 0x7ea84]; [0x5160c; 0x7ead8]; [0x5160c; 0x7ed64]; [0x5160c];
[0x514ac; 0x7eafc]; [0x514ac; 0x7ec2c]; [0x514ac; 0x7edf8]; [0x514ac]].
Lemma Tfib_universe_drv : forall t, In t Tfib_drv_traces -> In t Tfib_universe.
Proof.
intros t H. apply memZL_In.
exact (allb_In (fun t => memZL t Tfib_universe) Tfib_drv_traces t ltac:(vm_compute; reflexivity) H).
Qed.
