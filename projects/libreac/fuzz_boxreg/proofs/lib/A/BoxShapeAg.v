(* box_shape (A/BoxShape.v) is the shape of fuzz_boxreg's ubsan agreement, ag_shape kept_shape
   (lib/Prog/LLVMFuzzerTestOneInput_agree.v; lib/AgreeShape.v over lib/FrameSlotK.v), by conversion. Kept apart from
   BoxShape.v because lib/AgreeShape.v requires the ubsan library (lib/U). *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require AgreeShape FrameSlotK.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require Import BoxShape.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YI5b YI5c.
(* Guard, as lib/A/Prog/BoxPa.v:21 (a Theorem Labs lane's sweep 04:33Z, sweep/results.md line 99): this file does not Require
   BoxPa, and AgreeShape / FrameSlotK put the PLAIN sink instances in its closure. *)
(* global on purpose: keeps the plain sink instances out of every importer of this file (knock-case defect, a Theorem Labs lane's 06:30Z sweep; a Theorem Labs lane 10:42Z) *)
#[global] Remove Hints YI5b.src0_sink_head YI5c.src0_sink YI5c.src0_sink_laws : typeclass_instances.

Lemma box_shape_ag : box_shape =
  OSSVerify.Proofs.libreac.fuzz_boxreg.lib.AgreeShape.ag_shape
    OSSVerify.Proofs.libreac.fuzz_boxreg.lib.FrameSlotK.kept_shape.
Proof. reflexivity. Qed.
