(* The library shape of fuzz_transport's agreement statements, and the plain side's claim at that shape.
   transport_shape: each call of LLVMFuzzerTestOneInput returns 0, writes nothing and leaves the file system as it found
   it (lib/FrameSlotK.v kept_shape). It is the shape of the ubsan agreement's plain side (lib/AgreeShape.v ag_shape over
   kept_shape), so the plain build's proved realization of SPECX at that shape is the plain side of the ASan agreements.
   transport_plain_rz_stmt: the plain build realizes SPECX at transport_shape from every valid start at 2^34. The image-A
   and image-B compositions take it as one named hypothesis, so both sides use the same term. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.libdiginet.fuzz_transport Require Images.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK15 YO09 YO06.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Agree AgreeShape FrameSlotK.
Import ListNotations.
Open Scope Z_scope.

#[export] Instance transport_shape : lib_shape := ag_shape kept_shape.

Definition transport_plain_rz_stmt : Prop :=
  forall en inp, valid_entry Images.plain en inp -> valid_input inp ->
    rz_run Images.plain Budgets.Standard.lim_source en inp (SPECX (LS:=transport_shape) inp).
