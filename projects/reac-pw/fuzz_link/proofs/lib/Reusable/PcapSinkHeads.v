(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_pcap: the address of musl's ofl_head (the head of
   the open-file list) in the two ASan images, as YI16.sink_head values. They are plain Definitions, not
   instances: an ASan file names the one it uses, and the plain image's global instance (YI5b.src0_sink_head)
   must not reach an ASan file. lib/A/PcapSinkHeadCheck.v checks both values against the images' code.
   Porter ruling (fuzz_state S0's form): this file also removes YI5b.src0_sink_head, the only global
   instance of YI16.sink_head in the union, from the typeclass_instances hints, globally, so a file that loads
   this one cannot fill an implicit sink_head with the plain image's value; an ASan proof must name its head
   (asan_sink_head / asan_ubsan_sink_head). (lib/U/Reusable/YI5b.src0_sink_head is an instance of a different
   class, lib/U/Reusable/YI16.sink_head; it cannot fill a lib/Reusable/YI16.sink_head argument.) *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YI5b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YI5c.
Local Open Scope Z_scope.

(* These guards act only in the files that load PcapSinkHeads. Measured 2026-10-29 on the union of a working branch
   b1d07fd69b8 with a working branch 470849ffbd7, a working branch 5e61aac2f9d, a working branch 9be46202615, a working branch 00e92d20ef1,
   a working branch 40d00b885aa, a working branch b6db5febb7f, a working branch 9700d736a50 and a working branch 6c461415f47: they are lib/A/PcapSinkHeadCheck.v,
   lib/A/PcapDriver.v and lib/A/AD2o.v (through PcapDriver). a working branch 0d5314e654a deleted lib/Reusable/YE2k, YE26,
   YE27, YE28, YE29, YE2c and YE2d, which loaded it; lib/Reusable/YD1k does not load it. The ASan statements
   (lib/PcapAsanTop.v, on a working branch) do not load this file; the ASan-side guard is in lib/PcapAsanTop.v (on a working branch),
   kept by the composition owner. Measured 2026-10-29: no implicit sink_syms / sink_head instance in the 17
   top terms under Set Printing All, so these are protection for later edits, not a fix. *)
(* Both lines are global, not Local: the G2 sink-head guard must act in every importer (ruling of 2026-10-29
   11:35Z), since a Local form would protect only this file and leave a bare sink or sink_head argument in a
   consumer elaborating to the plain image's instance. Consumers measured 2026-10-29 on a working branch aa511e2f32b,
   same counts on a working branch cb2d4c6445d: 2 files of lib/A Require this file directly (A/PcapSinkHeadCheck.v,
   A/PcapDriver.v), 3 transitively (A/AD2o.v through PcapDriver). The lines of lib/PcapAsanTop.v:37-39 (on
   comp) are a deliberate second copy: the ASan statements do not load this file, so this guard cannot reach
   them. *)
#[global] Remove Hints YI5b.src0_sink_head : typeclass_instances.
#[global] Remove Hints YI5c.src0_sink : typeclass_instances.

(* fuzz_pcap.asan (v1.9.0): ofl_head = 0x5f4f88 (ofl_lock 0x5f4f80 + 8). *)
Definition asan_sink_head : YI16.sink_head := {| YI16.sk_ofl_head := 0x652308 |}.

(* fuzz_pcap.asan-ubsan (v1.9.0): ofl_head = 0x5f4e88 (ofl_lock 0x5f4e80 + 8). *)
Definition asan_ubsan_sink_head : YI16.sink_head := {| YI16.sk_ofl_head := 0x651888 |}.
