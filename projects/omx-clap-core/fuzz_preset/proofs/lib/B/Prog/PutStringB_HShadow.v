(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: COPY of lib/A/Prog/PRW_HShadow.v at origin/cold/h-hpreset-7-walk-S7B 7819c4b4583 (blob
   2662d68ca36b), image-generic, with ONE removal for image B': its (2) ARx_img_shadow_vis, stated over YImgTop's image-A
   bounds, is dropped (the B' walk states the image-shadow fact over the instance's pa_lo / pa_hi, PutStringB_Base.v
   HIMGSH, whose discharge at ARx := ARcf is h-mani-a8's YGcfAmx2.img_shadow_vis_cf (ci := CfImgB.CfImg_B), the form
   of FuzzStrdupB at origin/cold/c-omx-alloc-strdup102 e8c226ad89c3). The #102 base origin/cold/h-rw-pre-4-int102
   lacks the file. *)
(* fuzz_preset, program part: generic twins of a Theorem Labs lane's cf laws not yet in YCbqG / AR_laws_x; to be adopted by a Theorem Labs lane, then this
   file is deleted. GENERIC in the allocator relation ARx. Definitions only; no proof. The texts take ARx as a Section
   Variable, so a walk cannot use a law stated over the concrete `ARcf segs B`; it takes the twin over its ARx as a
   hypothesis, and at assembly (ARx := ARcf segs B) the twin is convertible to the cf owner's law and the cf owner's proof discharges it.
   (1) ARx_hshadow_law: ADOPTED as YCbqG.v's ARx_hshadow_law / AR_laws_x field 14 alx_hshadow; cite LAWS's alx_hshadow.
   Numerals: none. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
Import ListNotations.
Local Open Scope Z_scope.

Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.

(* (3) the frame hull: every live fake frame's shadow hull is visible (asked by BPnoting; a8 discharges it at ARcf) *)
Definition ARx_frame_hull_vis : Prop :=
  forall ly S Hp (W : world segs) mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  shadow_hull_vis (aview segs (w_H W) mem) (frame_addr ly cid pos) (fs_frame_bytes cid).
End h.
