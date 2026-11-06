(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, image B' (asan-ubsan, harness fix #102 pin sha256 d663f82d7f488d30...): the PAListing
   tables of a Theorem Labs lane's whole-program listing B_prog_listing (lib/B/Listing_prog.v blob 8bcc2c9e7809,
   a working branch d42e123915ae), WITHOUT the image half: lib/B/PAImg_prog.v 4392ab2c09ba:177-181
   with the names prefixed E102B_ / PL_102_B (the twin of lib/A/Ent102PLA.v). The PAListing record reads only the
   listing, so it is the same record as PL_prog_B; the walk of LLVMFuzzerTestOneInput on B' is parametric over
   `{PA : PAImg B_prog_listing}` (parent's route (b)) and takes this record; the instance is PI_prog_B at the re-pin.
   rule 24: proves no function (kind: generated tables, copied). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l YP0b YP0a YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Definition E102B_tpi : ptree asym := ptree_of_list B_prog_listing.
Definition E102B_tw : ctable := Eval vm_compute in (tw_of 0 B_prog_listing).
Definition PL_102_B : PAListing B_prog_listing :=
{| pl_tpi := E102B_tpi; pl_tpi_eq := eq_refl; pl_tw := E102B_tw; pl_tw_eq := ltac:(vm_compute; reflexivity);
pl_lim := ltac:(vm_compute; reflexivity); pl_len := ltac:(vm_compute; discriminate); pl_slot0 := ltac:(vm_compute; exact I) |}.
