(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, image A' (asan, harness fix #102 pin sha256 1be0f53d96cb9d6c...): the PAListing tables
   of a Theorem Labs lane's whole-program listing A_prog_listing (lib/A/Listing_prog.v blob 1ab147923c5d,
   a working branch d42e123915ae), WITHOUT the image half. The four definitions below are the
   generated lib/A/PAImg_prog.v 47eeb54e93be:177-181 with the names prefixed E102_ / PL_102_: the PAListing record
   reads only the listing (ptree_of_list, tw_of, the atom and length checks), so it is the same record. PAImg_prog.v
   itself imports the image (images Asan) and checks the listing against it, so it compiles only on a facts tree of
   the #102 pins; until that build route exists the walk of LLVMFuzzerTestOneInput is parametric over
   `{PA : PAImg A_prog_listing}` and takes this PAListing (parent's route (b), 13:0xZ). At the re-pin the instance is
   PI_prog_A; this record and PL_prog_A are equal field by field (both are the listing's).
   rule 24: proves no function (kind: generated tables, copied). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l YP0b YP0a YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Definition E102_tpi : ptree asym := ptree_of_list A_prog_listing.
Definition E102_tw : ctable := Eval vm_compute in (tw_of 0 A_prog_listing).
Definition PL_102_A : PAListing A_prog_listing :=
{| pl_tpi := E102_tpi; pl_tpi_eq := eq_refl; pl_tw := E102_tw; pl_tw_eq := ltac:(vm_compute; reflexivity);
pl_lim := ltac:(vm_compute; reflexivity); pl_len := ltac:(vm_compute; discriminate); pl_slot0 := ltac:(vm_compute; exact I) |}.
