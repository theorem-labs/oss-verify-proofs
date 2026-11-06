(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-29: fuzz_preset, image A' (asan, #102 pin 1be0f53d96cb, unstripped twin bff8519bbe3e): the
   walk of check_bounded_alloc (CheckBoundedAllocA.v check_bounded_alloc_holds_A, row N10-CBAA) at the #102 DRIVER'S
   instance, so the driver's slot pcc_check_bounded_alloc (lib/A/PresetCfnA.v:996-997) is discharged by `exact`
   (h-pre-b1's request, 19:52Z). Its A-side form follows h-rw-pre-5's image-B' file lib/B/Prog/CrcBInstLive.v
   (origin/cold/h-rw-pre-5-r102-crcB 8f5bab31e565).
   rule 24: proves no function (kind: instance of an already-proved walk).
   check_bounded_alloc_holds_A_inst is check_bounded_alloc_holds_A at
   - B := AD2l.TfibB, PI := prh_img_A, L := A_prog_listing, PA := PI_prog_A, cp := CfParams_preset,
     RL := prh_room_live_a8 at CfParams_preset;
   - ARx := ARcf /\ xs_placed_cf at CfParams_preset over PI_prog_A's segments, which is PresetCfnA.v's iface_ARx
     (:983-986) at that L / PA / B, word for word;
   - LAWS by YGcallcf.AR_laws_x_xs of YG0lawscf.AR_laws_ok_cf (the discharge the B' file uses).
   It holds for every float state and every sink head, which is the slot's own quantification. No premise is left:
   check_bounded_alloc makes no call, so unlike check_reject_clean there is no callee row to carry. No numeral. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YCbqG YGcfNames YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import CheckBoundedAllocA.
Import ListNotations.
Open Scope Z_scope.

Section L. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Abbreviation CP := CfParams_preset.
#[local] Abbreviation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).
#[local] Abbreviation TB := AD2l.TfibB.
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf (cp := CP) SEGS TB ly S Hp W mem md /\ xs_placed_cf ly S).
Theorem check_bounded_alloc_holds_A_inst : forall SK : YI16.sink_head,
  tcheck_bounded_alloc_specX (cp := CP) (PI := prh_img_A) (RL := prh_room_live_a8 (cp := CP))
    (L := A_prog_listing) (PA := PI_prog_A) TB ARcfx SK.
Proof.
intros SK.
exact (check_bounded_alloc_holds_A (cp := CP) (RL := prh_room_live_a8 (cp := CP)) TB ARcfx SK
  (YGcallcf.AR_laws_x_xs (cp := CP) SEGS TB (YG0lawscf.AR_laws_ok_cf (cp := CP) SEGS TB))).
Qed.
End L.

(* ---- the Qed report: the elaborated statement, every implicit shown, and the assumptions ---- *)
Set Printing Implicit.
Unset Printing Notations.
Print check_bounded_alloc_holds_A_inst.
Unset Printing Implicit.
Set Printing Notations.
Print Assumptions check_bounded_alloc_holds_A_inst.
