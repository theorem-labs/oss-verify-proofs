(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/CmdShape.v (origin/ossv/recipes 501c0d516c69) for reac-pw/fuzz_segconf's image A (fuzz_segconf.asan): module paths; cmd_shape -> seg_shape. segconf's lib/ZTraceSpec.v and lib/AgreeShape.v are fuzz_command's up to module paths, and segconf's ubsan agreement (the plain lane's lib/AgreeSeg.v) is at the same shape ag_shape checksum_shape. *)
(* The library shape of fuzz_command's agreement statements: each call of LLVMFuzzerTestOneInput returns 0, writes
   nothing and leaves the file system as it found it. It is the shape of fuzz_command's ubsan agreement
   (lib/AgreeCmd.v, ag_shape checksum_shape of lib/AgreeShape.v and lib/ZTraceSpec.v), so the plain build's proved
   realization of SPECX at that shape is the plain side of the ASan agreement. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import ZTraceSpec AgreeShape.

#[export] Instance seg_shape : lib_shape := ag_shape checksum_shape.
