(* lib/A/ACtlRtC.v -- route (C) (a Theorem Labs lane DECISION 09:20Z): the DEFINITIONS of the stage-variable cut form, BELOW
   lib/A/ACtlCut.v so ctl_from can Require it (a Theorem Labs lane 09:37Z: "Requires ShadowRwOn + the core and NOT ACtlCut").
   ONE WRITER: a Theorem Labs lane.  Moved text-unchanged from lib/A/ACtlCutC.v, which keeps the lemmas that need ACtlCut /
   ProgWorld (ctl_rt_C_of_ctl_rt, cut_shadow_of_AR, cut_shadow_at_cut, img_shadow_cover, img_shadow_of_AR,
   img_shadow_at_cut, ctrl_img_shadow_vis) and Requires this file.  rule 24: no function proved.

   ctl_rt_C B ly3 S3 mem3 replaces ACtlCut.ctl_rt mem3 (ACtlCut.v:224) at ctl_from's own binders; the regions are
   (F) the shadow of every frame in frames S, (L) the 8-aligned shadow-word cover of every live block in ablocks B ly S,
   (Z) the shadow of every zero_shadow_ranges B ly entry, and (I) img_shadow, the image hull's shadow. *)
(* This delivery then edited comment text only: the code is unchanged from release c5e779efe8c, the comments are not. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG01 Reusable.YG0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0n Reusable.YG0d Reusable.YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlK A.Prog.CtrlRo A.ShadowRwOn.
Local Open Scope Z_scope.

Section CtlRtC.
Variable B : lib.Reusable.YG0f.asyms.

(* The regions of the cut's own state: (F) owned frames' shadow, (L) live blocks' shadow-word cover, (Z) zero shadow,
   (A) the fake stack's FRAMES AREA shadow [shadow_addr (F + kFakeFramesOff), shadow_addr (F + kFakeStackSize)), which
   AR's am_areas states visible (YG0n.v:139 / :220): announced addition 10:5xZ (two Theorem Labs lanes 10:57Z,
   side-stack-shadow.md (a working note, not in this delivery); the 4608-byte header shadow is NOT included). *)
Definition cut_shadow ly (S : lib.Reusable.YG00.astate) (a : Z) : Prop :=
  (exists cid pos, In (cid, pos) (lib.Reusable.YG01.frames S) /\
     lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.frame_addr ly cid pos) <= a <
     lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.frame_addr ly cid pos) + lib.Reusable.YG00.fs_frame_bytes cid / 8)
  \/ (exists p n, In (p, n) (lib.Reusable.YG0d.ablocks B ly S) /\
     lib.Reusable.YG0f.shadow_addr p / 8 * 8 <= a <
     lib.Reusable.YG0f.shadow_addr (p + lib.Reusable.YG00.req_size n - 1) / 8 * 8 + 8)
  \/ (exists r, In r (lib.Reusable.YG0n.zero_shadow_ranges B ly) /\
     lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF (fst r) <= a <
     lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF (fst r) + snd r / 8)
  \/ (lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.ly_F ly + lib.Reusable.YG0f.kFakeFramesOff) <= a <
      lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.ly_F ly + lib.Reusable.YG0f.kFakeStackSize)).

(* (I) the image's shadow: a fixed range, so arity (m) is enough. *)
Definition img_shadow (a : Z) : Prop :=
  exists x, A.Prog.CtrlRo.IMG_LO <= x < A.Prog.CtrlRo.IMG_HI /\ a = lib.Reusable.YG0f.shadow_addr x.

(* The replacement of ACtlCut.ctl_rt, stated at ctl_from's binders: `ctl_rt_C B ly3 S3 mem3` in place of
   `ctl_rt mem3` (ACtlCut.v:224). *)
Definition ctl_rt_C ly (S : lib.Reusable.YG00.astate) (m : word -> option byte) : Prop :=
  A.ACtlK.asan_cells_at m /\ A.ShadowRwOn.shadow_rw_on (cut_shadow ly S) m /\ A.ShadowRwOn.shadow_rw_on img_shadow m
  /\ A.ACtlK.ro_agree_at m.

End CtlRtC.
