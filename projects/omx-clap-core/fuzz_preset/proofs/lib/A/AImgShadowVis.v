(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: written for omx-clap-core/fuzz_preset's ASan image A. The shadow map of the whole image range
   [IMG_LO, IMG_TOP) (YImgTop.v, generated from the pinned image) is present in the view in every state AR holds:
   img_shadow_vis, the donor's statement (proofs/libreac/fuzz_grant/lib/A/Prog/GrantRo.v at a970a282587, a fact there
   that a unit supplies), is PROVED here from the zero-shadow law, the const law and the cover check of
   lib/Reusable/YImgShadowCover.v, instantiated with the generated lists of A/AF0m.v: the zero-shadow ranges
   Tfib_zero_shadow and the shadow cells Tfib_const_shadow. tfib_img_shadow_cover is the cover check of those two lists,
   decided by vm_compute; no count of granules, ranges or cells is written here. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n YK08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YImgTop YImgShadowCover.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* The cover check of image A's own lists. *)
Lemma tfib_img_shadow_cover : img_shadow_cover Tfib_zero_shadow Tfib_const_shadow IMG_LO IMG_TOP = true.
Proof. vm_compute. reflexivity. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The donor's statement (GrantRo.v:45-47), at image A's bounds. *)
Definition img_shadow_vis (segs : list Segment) (B : asyms) : Prop :=
forall ly S (W : world segs) mem md a,
AR segs B ly S W mem md -> IMG_LO <= a < IMG_TOP -> aview segs (w_H W) mem (shadow_addr a) <> None.

(* The two list facts the composition needs from an image binding of B. *)
Lemma tfib_zsh_incl : forall B, as_zero_shadow B = Tfib_zero_shadow -> incl Tfib_zero_shadow (as_zero_shadow B).
Proof. intros B E. rewrite E. apply incl_refl. Qed.
Lemma tfib_const_shadow_incl : forall B, (forall ly, as_const B ly = Tfib_const ly) ->
forall ly, incl Tfib_const_shadow (as_const B ly).
Proof. intros B E ly. rewrite E. unfold Tfib_const. apply incl_appr, incl_appr, incl_refl. Qed.

(* From the two list equations alone (what TfibSyms' ts_zsh and ts_const give). *)
Theorem img_shadow_vis_A : forall segs B,
as_zero_shadow B = Tfib_zero_shadow -> (forall ly, as_const B ly = Tfib_const ly) -> img_shadow_vis segs B.
Proof.
intros segs B Ez Ec.
exact (img_shadow_vis_of_cover segs B Tfib_zero_shadow Tfib_const_shadow IMG_LO IMG_TOP tfib_img_shadow_cover
(tfib_zsh_incl B Ez) (tfib_const_shadow_incl B Ec)).
Qed.

(* At the image binding TfibSyms (A/AF0m.v), which TfibB (A/AD2l.v) satisfies. *)
Theorem tfib_img_shadow_vis : forall segs B, TfibSyms B -> img_shadow_vis segs B.
Proof. intros segs B HB. exact (img_shadow_vis_A segs B (ts_zsh B HB) (ts_const B HB)). Qed.
End a.
