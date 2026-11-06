(* The library shape of fuzz_boxreg's agreement statements: each call of LLVMFuzzerTestOneInput returns 0, writes
   nothing and leaves the file system as it found it. Its fields are those of the shape of fuzz_boxreg's ubsan
   agreement (lib/Prog/LLVMFuzzerTestOneInput_agree.v: ag_shape kept_shape, lib/AgreeShape.v over lib/FrameSlotK.v),
   written out here so that the ASan side does not load the ubsan library that lib/AgreeShape.v requires. The plain
   build's proved realization of SPECX at this shape is the plain side of the ASan agreement (A/AsanTop.v). *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK15 YO09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Import AllocSlots.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require SlotAgree.
Import ListNotations.
Open Scope Z_scope.

#[export] Instance box_shape : lib_shape := {|
  LIBK := fun pl fs K => K (LL 0 fs []);
  LIBK_ext := fun pl fs K K' H => H (LL 0 fs []);
  lib_delta := fun n b => b;
  lib_room := fun b n => sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\
    sb_cap b = OSSVerify.Proofs.libreac.fuzz_boxreg.lib.SlotAgree.CAP_AG |}.
