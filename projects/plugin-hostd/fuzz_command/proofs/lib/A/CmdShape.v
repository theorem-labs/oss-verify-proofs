(* The library shape of fuzz_command's agreement statements: each call of LLVMFuzzerTestOneInput returns 0, writes
   nothing and leaves the file system as it found it. It is the shape of fuzz_command's ubsan agreement
   (lib/AgreeCmd.v, ag_shape checksum_shape of lib/AgreeShape.v and lib/ZTraceSpec.v), so the plain build's proved
   realization of SPECX at that shape is the plain side of the ASan agreement. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import ZTraceSpec AgreeShape.

#[export] Instance cmd_shape : lib_shape := ag_shape checksum_shape.
