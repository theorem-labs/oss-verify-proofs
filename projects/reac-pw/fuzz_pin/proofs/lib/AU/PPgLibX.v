(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program-contract part of lib/A/AD2o.v of this library (pin_bind,
   pin_lib_x_of, pin_lib_x; made there from proofs/libreac/fuzz_knock/lib/A/APgLib.v:305-312 at origin/ossv/recipes
   6ebe35ba632), taken for reac-pw/fuzz_pin's image B (fuzz_pin.asan-ubsan, sha256
   d6f83d30152279dadae39fc626707a0037090a8909a186dac3c362b12088201f): lib/AU/PPgLib.v's pin_lib_x_all, from image B's
   program walks' top lemmas (lib/AU/PPgMain.v pin_lib_x_A, PPgRow.v, PPgParse.v with PPgCat.v's reac_box_catalogue,
   PPgLeaf.v) with their wrapper, runtime and image hypotheses bound at image B's record lib/AU/YD2l.v TfibB
   (lib/AU/PinWrapBinders.v), the sink's image laws (lib/AU/YD1u.v tfib_AIL), the meter's laws (ameter_triv,
   lib/Reusable/YCbp.v) and XL0_HXL. The rest of lib/A/AD2o.v (the driver adapter and the asan Section's join) is the
   image-B join's, which consumes pin_lib_x_of here at the allocator facts PinClose's Section asan_ubsan hands
   H_DRIVER_U. pin_lib_x is the same claim closed with image B's own allocator theorems (lib/AU/YF0w.v
   tfib_amalloc_realizes, lib/AU/YF0q.v afree_realizes_closed, as lib/A/PinAllocClose.v does for image A).
   Rule 24: proves no function (kind: assembly). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YG00 YG01 YG0f YG0d YC5d YCbp YM05.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YO09.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require AWalkFw0 YD2l YD1u YF0w YF0q.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require PPgLib PPgMain PPgParse PPgCat PPgRow PPgLeaf.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require PinWrapBinders.
Local Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.
(* the read-only window below the sink head, the class the program walks take as a Context *)
#[local] Existing Instance PinWrapBinders.pin_ROB.

Ltac pin_bind AM AF LEAF :=
  first [ exact PinWrapBinders.pin_tfib_lib | exact PinWrapBinders.pin_LAWS | exact PinWrapBinders.pin_ML
        | exact PinWrapBinders.pin_ASM0 | exact PinWrapBinders.pin_ASM1 | exact PinWrapBinders.pin_SMP
        | exact PinWrapBinders.pin_ASF | exact PinWrapBinders.pin_FFL
        | exact (YD1u.tfib_AIL YD2l.TfibB YD2l.TfibB_syms)
        | exact AM | exact AF
        | exact PinWrapBinders.pin_AMEMCPY | exact PinWrapBinders.pin_AMEMCHR | exact PinWrapBinders.pin_ASTRLEN
        | exact PinWrapBinders.pin_ABCMP | exact PinWrapBinders.pin_ASTRCSPN | exact PinWrapBinders.pin_ASTRNCMP
        | exact PinWrapBinders.pin_ro_law_TfibB
        | exact ameter_triv_laws | exact ameter_triv_fs_laws | exact PPgLib.XL0_HXL | exact LEAF ].
Section f. Context {rc : YM05.RunCeil} {LS : YO09.lib_shape}.
(* the closed program contract, at the allocator facts the image-B join receives (PinClose.v Section asan_ubsan
   H_ALLOC_MALLOC_U / H_ALLOC_FREE_U at B_U := TfibB) *)
Lemma pin_lib_x_of :
  (forall fx : YK11.FPState, @amalloc_realizes fx rc AWalkFw0.tfibsegs YD2l.TfibB) ->
  (forall fx : YK11.FPState, @afree_realizes fx rc AWalkFw0.tfibsegs YD2l.TfibB) ->
  @PPgLib.pin_lib_x_all rc LS.
Proof.
intros AM AF LEAF fx.
specialize (AM fx). specialize (AF fx).
eapply PPgMain.pin_lib_x_A;
  first [ pin_bind AM AF LEAF
        | (eapply PPgRow.pin_pb_rowX; pin_bind AM AF LEAF)
        | (eapply PPgParse.pin_pb_parseX_A;
             first [ pin_bind AM AF LEAF | (eapply PPgCat.pin_pb_catalogueX; pin_bind AM AF LEAF) ])
        | (eapply PPgLeaf.pin_pb_check_knownX; pin_bind AM AF LEAF)
        | (eapply PPgLeaf.pin_pb_check_rowX; pin_bind AM AF LEAF)
        | (eapply PPgLeaf.pin_pb_check_labelX; pin_bind AM AF LEAF) ].
Qed.
(* the same claim with image B's own allocator theorems: no premise beyond LEAF, which the join discharges by
   eq_refl at the agreement shape *)
Theorem pin_lib_x : @PPgLib.pin_lib_x_all rc LS.
Proof.
exact (pin_lib_x_of
  (fun fx => @YF0w.tfib_amalloc_realizes fx rc YD2l.TfibB YD2l.TfibB_syms (fun t => eq_refl))
  (fun fx => @YF0q.afree_realizes_closed fx rc YD2l.TfibB YD2l.TfibB_syms (fun t => eq_refl))).
Qed.
End f.
