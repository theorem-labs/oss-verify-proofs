(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: gate 6h guard for fuzz_scene's ASan glue (lib/A/G_*.v, lib/AU/G_*.v). The released tree
   declares the plain image's sink as global instances of BOTH classes: Reusable/YI5b.v:12 src0_sink_head
   (YI16.sink_head) and Reusable/YI5c.v:15 / :45 src0_sink / src0_sink_laws (YI14.sink_syms and its laws). A file that
   Requires this one sees none of them as an instance, so a sink argument that is not given by name fails to
   elaborate instead of taking the plain image's sink. The plain image's cells are measured WRONG for the ASan
   images (a Theorem Labs lane, 2026-10-29 01:57Z): src0_sink's sk_read 0x18798 is inside __stdio_exit and sk_seek 0x18a40 inside
   __stdio_write (asan; AU 0x18b68 / 0x18e10, with __stdio_seek at 0x18e3c), so an implicit sink_syms would be
   false for every ASan statement. The lib/U/Reusable twins (U/Reusable/YI5b.v, YI5c.v) declare the same instances
   and are removed here as well. Reference: omx-clap-core/fuzz_state lib/A/FSH_Gen.v:49 at bffd3c8f802. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YI5b YI5c.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require YI5b YI5c.
#[global] Remove Hints OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
#[global] Remove Hints OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable.YI5c.src0_sink : typeclass_instances.
#[global] Remove Hints OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.
#[global] Remove Hints OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable.YI5b.src0_sink_head : typeclass_instances.
#[global] Remove Hints OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable.YI5c.src0_sink : typeclass_instances.
#[global] Remove Hints OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable.YI5c.src0_sink_laws : typeclass_instances.
