(* fuzz_preset, program part: generic twins of a Theorem Labs lane's cf laws not yet in YCbqG / AR_laws_x; to be adopted by a Theorem Labs lane, then this
   file is deleted. GENERIC in the allocator relation ARx (WalkS7b of h-rw-pre-5, the one copy every walk lane imports
   by path). Definitions only; no proof. The texts take ARx as a Section Variable, so a walk cannot use a law stated
   over the concrete `ARcf segs B`; it takes the twin over its ARx as a hypothesis, and at assembly (ARx := ARcf segs B)
   the twin is convertible to a Theorem Labs lane's law (unfold both; the bodies are the same term) and that lane's proof discharges it.
   (1) ARx_hshadow_law: ADOPTED as YCbqG.v's ARx_hshadow_law / AR_laws_x field 14 alx_hshadow (journal blob
       83da015952be, engine c-omx-alloc 63997a07aa6), so it is REMOVED here; cite LAWS's alx_hshadow.
   (2) ARx_img_shadow_vis segs B ARx: h-mani-a8's img_shadow_vis_cf (origin/cold/h-mani-a8-preset-alloc 91d0544ad13,
       lib/Reusable/YGcfAmx2.v:47-49, the text taken verbatim with ARcf segs B -> ARx; bounds YImgTop's IMG_LO /
       IMG_TOP by name): the image's shadow bytes are present in the view. a8 states it as a unit-supplied fact (not
       proved in YGcfAmx2.v); its discharge is the unit's supply of img_shadow_vis_cf.
   Numerals: none. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop.
Import ListNotations.
Local Open Scope Z_scope.

Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.

Definition ARx_img_shadow_vis : Prop :=
  forall ly S Hp (W : world segs) mem md a, ARx ly S Hp W mem md -> IMG_LO <= a < IMG_TOP ->
  aview segs (w_H W) mem (shadow_addr a) <> None.

(* (3) the frame hull: every live fake frame's shadow hull is visible (asked by BPnoting; a8 discharges it at ARcf) *)
Definition ARx_frame_hull_vis : Prop :=
  forall ly S Hp (W : world segs) mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  shadow_hull_vis (aview segs (w_H W) mem) (frame_addr ly cid pos) (fs_frame_bytes cid).
End h.
