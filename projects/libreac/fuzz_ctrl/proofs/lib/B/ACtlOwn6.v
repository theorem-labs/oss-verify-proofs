(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2422 of its 2466 lines of code are new or changed and 984 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3a.v, with its module names changed; 1977 of its 2075 lines of code are new or changed and 2368 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3b.v, with its module names changed; 32 of its 55 lines of code are new or changed and 2052 lines of the source are left out. *)
(* lib/B/ACtlOwn6.v -- own6_frame_proved: the placement and presence of the own class-6 fake frame at an own6 cut of
   fuzz_ctrl image B's (asan-ubsan) walk of LLVMFuzzerTestOneInput.  Owner a Theorem Labs lane.
   rule 24: no function proved
   proves no function (kind: segment lemma) -- a cut-side bridge fact of the image-B walk; no function is proved.

   STATEMENT: lib/B/ACtlW3b.v's Hypothesis own6_frame in the corrected form of W3b's writer a Theorem Labs lane (10:43Z): the
   third conjunct bounds the frame by lib.Reusable.YM05.alloc_ceiling, as lib/B/ACtlW0.v w0_own6_frame and image A's
   twin do.  Token for token, under W3b's Section context {fx rc LS SK}, B, FP and its `segs` / ART names.

   ROUTE (no Section hypothesis; every fact is a proved lemma):
   1. fr = frame_addr ly3 6 (c_fpos cx): the journal's layout_le gives ly_F ly3 = ly_F (c_ly cx)
      (as lib/B/ACtlW0.v w0_own6_frame :302-304).
   2. IMG_TOP <= fr: B.ProgWorld_Fs.ctl_frame_above_img (premise-free) at the journal's AR state.
   3. fr + 4096 <= alloc_ceiling: Reusable.YCbq.frames_bounds at the journal's AR state.
   4. the 4096 frame bytes and their 512 shadow bytes are present: Reusable.YG0d.al_frames of the core's AR laws
      Reusable.YG0q.AR_laws_ok; ART.shadow_addr fr = Reusable.YG0f.shadow_addr fr (both fr / 8 + 0x7fff8000).
   The frame (6, c_fpos cx) is in frames S3 because frames S3 = own6 cx = [(6, c_fpos cx)]. *)

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
(* The modules that exist twice (core lib/Reusable and the unit's lib/B/Reusable) are Required through the CORE
   prefix, never as `Reusable.X`: YK11 YM05 YO09 YI16. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YO09 YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YB1v Reusable.YCfn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG01 Reusable.YG0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0n Reusable.YG0d Reusable.YG0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YCbq Reusable.YImgTop.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.AsanRT B.ACtlCut B.ProgWorld_Fs.
Import ListNotations.
Local Open Scope Z_scope.

Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.AsanRT.

Section Own6.

Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Context {SK : lib.Reusable.YI16.sink_head}.
Variable B : Reusable.YG0f.asyms.
Variable FP : list (Z * Z).

Local Notation segs := Reusable.YB1v.tfibsegs.

Lemma own6_frame_proved : forall (cx : B.ACtlCut.ctlcx) ly3 S3 (W3 : Reusable.YA0n.world segs) mem3 md3 k fr,
  Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (B.ACtlCut.c_sp cx) FP
    (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx)
    (B.ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  Reusable.YG01.frames S3 = B.ACtlCut.own6 cx ->
  fr = Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) 6 (B.ACtlCut.c_fpos cx) ->
  fr = Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx) /\
  Reusable.YImgTop.IMG_TOP <= fr /\ fr + 4096 <= lib.Reusable.YM05.alloc_ceiling /\
  (forall a, fr <= a < fr + 4096 \/ ART.shadow_addr fr <= a < ART.shadow_addr fr + 512 ->
     Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a).
Proof.
  intros cx ly3 S3 W3 mem3 md3 k fr HJ Hfr Efr.
  pose proof (Reusable.YG0q.AR_laws_ok segs B) as LAWS.
  assert (Hin : In (6, B.ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite Hfr; left; reflexivity).
  destruct HJ as (HAR & Hly & _).
  assert (EF : Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx) =
               Reusable.YG0f.frame_addr (B.ACtlCut.c_ly cx) 6 (B.ACtlCut.c_fpos cx)).
  { unfold Reusable.YG0f.frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  rewrite <- EF in Efr. subst fr.
  pose proof (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (B.ACtlCut.c_fpos cx) HAR Hin)
    as (_ & Hc & _).
  pose proof (Reusable.YG0d.al_frames segs B LAWS ly3 S3 W3 mem3 md3 6 (B.ACtlCut.c_fpos cx) HAR Hin)
    as (_ & _ & Hfb & Hsh).
  pose proof (B.ProgWorld_Fs.ctl_frame_above_img B ly3 S3 W3 mem3 md3 6 (B.ACtlCut.c_fpos cx) HAR Hin) as Himg.
  change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512 in Hsh.
  change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hc, Hfb.
  set (f := Reusable.YG0f.frame_addr ly3 6 (B.ACtlCut.c_fpos cx)) in *.
  split; [reflexivity|]. split; [exact Himg|]. split; [exact Hc|].
  intros a [Ha|Ha].
  - exact (proj1 (Hfb a Ha)).
  - assert (Esh : ART.shadow_addr f = Reusable.YG0f.shadow_addr f).
    { unfold ART.shadow_addr, ART.ASAN_K, Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. lia. }
    rewrite Esh in Ha.
    specialize (Hsh (a - Reusable.YG0f.shadow_addr f) ltac:(lia)).
    replace (Reusable.YG0f.shadow_addr f + (a - Reusable.YG0f.shadow_addr f)) with a in Hsh by lia.
    exact (proj1 Hsh).
Qed.

End Own6.
