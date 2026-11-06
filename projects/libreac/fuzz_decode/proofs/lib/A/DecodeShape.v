(* The library shape of fuzz_decode's agreement statements: each call of LLVMFuzzerTestOneInput returns 0, writes
   nothing and leaves the file system as it found it. It is the shape of fuzz_decode's ubsan agreement
   (lib/Prog/LLVMFuzzerTestOneInput_agree.v: ag_shape kept_shape, lib/AgreeShape.v and lib/FrameSlotK.v), so the plain
   build's proved realization of SPECX at that shape is the plain side of the ASan agreements. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK15 YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require Import AgreeShape FrameSlotK.
Import ListNotations.
Open Scope Z_scope.

#[export] Instance decode_shape : lib_shape := ag_shape kept_shape.
