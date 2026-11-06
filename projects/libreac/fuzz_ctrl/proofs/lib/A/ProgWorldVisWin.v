(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 3018 of its 3112 lines of code are new or changed and 934 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4e1.v, with its module paths and module names changed; 2867 of its 3071 lines of code are new or changed and 2908 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW1.v, with its module paths and module names changed; 43 of its 75 lines of code are new or changed and 3039 lines of the source are left out. *)
(* lib/A/ProgWorldVisWin.v -- fuzz_ctrl image A (libreac v1.9.0): proofs of two statements of lib/A/ProgWorld.v
   Section Visible (a Theorem Labs lane's statements file, a working branch c03ce1627b6, lines 297-313):
     win_vis     : win_vis_stmt     -- the callee's stack window is visible at the cut world, from the journal's
                                       presence conjunct (YCbq.v:368) and its stack bounds astk_ok (YCbq.v:333-335).
     win_sh_vis  : win_sh_vis_stmt  -- the 8-aligned shadow word cover of a stack sub-range is visible, from the
                                       stack entry of zero_shadow_ranges (YG0n.v:188-189) through AR_zshadow_law
                                       (YG0d.v:435-438); the stack bounds are page-aligned (layout_ok lo_top,
                                       YG0f.v:322-324), so the aligned cover stays inside the stack's shadow.
   img_vis (V2) is not stated in ProgWorld.v any more: ProgBridge.img_vis_W proves it for every world.

   This file CARRIED word-for-word copies of the two _stmt definitions from ProgWorld.v c03ce1627b6 while ProgWorld.v
   could not compile on this base: lib/A/AE2k.v:11 and lib/A/AF0l.v:13 name undefined `port_core_refused_*` addresses
   (the planning core's relocation run 5a85b67a5d8 refused them), and ProgWorld Requires A.AE2k.  ProgWorld fixes the
   journal's sink_head to A.AE2k.tfib_sink_head (ProgWorld.v:76); here it is a section Context, so the lemmas hold for
   every sink_head, that instance included.
   RE-POINTED 10-29 05:4xZ (a Theorem Labs lane's order, after a Theorem Labs lane measured with About that the lemmas proved LOCAL
   look-alikes that would not plug into ProgWorld's top): this file now Requires A.ProgWorld and states the record
   text, `A.ProgWorld.win_vis_stmt B` / `A.ProgWorld.win_sh_vis_stmt B`.  The six statements were diffed against
   ProgWorld.v first and were character-identical, so no bridge lemma exists or is needed, and the proofs did not
   change.  Replay verified on a Theorem Labs lane's integration head a48c4068c6e, where A.ProgWorld compiles. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04 Reusable.YA0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0f Reusable.YG0n Reusable.YG0d Reusable.YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorld A.AB1v A.AsanRT A.ProgBridge A.Prog.rng_asan.
Local Open Scope Z_scope.
Notation segs := A.AB1v.tfibsegs (only parsing).           (* as ProgWorld.v:80 *)

Section Visible.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : lib.Reusable.YG0f.asyms.

(* The window [lo, lo + len) lies in the journal's stack window [sp0 - STK, sp0), every byte of which is present
   (so not hidden) at the cut; astk_ok puts the window between alloc_ceiling > 0 and 2 ^ 47. *)
Lemma win_vis : A.ProgWorld.win_vis_stmt B.
Proof.
  unfold A.ProgWorld.win_vis_stmt.
  intros STK sp0 FPj ly S W mem md own lyc Sc Wc memc mdc k lo len HJ Hlo Hhi.
  destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  destruct Hstk as (_ & HSTK & Hceil & Hsp0 & Hsphi & H47 & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_value rc) as [[Hc0 _] _].
  change (2 ^ 47) with 140737488355328 in H47.
  unfold A.ProgBridge.range_visible. change (2 ^ 64) with 18446744073709551616.
  split; [lia |]. split; [lia |].
  intros a Ha. exact (proj1 (Hpres a ltac:(lia))).
Qed.

(* The stack's zero shadow covers the shadow bytes [SHADOW_OFF + L / 8, SHADOW_OFF + H / 8) of [L, H) =
   [ly_stk_lo, ly_stk_hi).  Both ends are page-aligned and SHADOW_OFF = ASAN_K is a multiple of 8, so rounding the
   first shadow byte of [lo, lo + len) down and the last one up to a multiple of 8 stays in that range.  A byte the
   view reads as Some 0 is not hidden: a hidden byte is in no segment (w_Hoff), so the view reads None there. *)
Lemma win_sh_vis : A.ProgWorld.win_sh_vis_stmt B.
Proof.
  unfold A.ProgWorld.win_sh_vis_stmt.
  intros LAWS ly S W mem md lo len HAR Hlo Hhi Hlen.
  destruct (Z.eq_dec len 0) as [E0 | Hne]; [left; exact E0 | right].
  pose proof (lib.Reusable.YG0n.am_layout B ly S _ (proj1 HAR)) as HLY.
  pose proof (lib.Reusable.YG0f.lo_top ly HLY) as (_ & _ & _ & Lhi & Plo & Phi & Lbeg).
  pose proof (lib.Reusable.YG0d.al_zshadow _ _ LAWS ly S W mem md
    (lib.Reusable.YG0f.ly_stk_lo ly, lib.Reusable.YG0f.ly_stk_hi ly - lib.Reusable.YG0f.ly_stk_lo ly) HAR
    ltac:(unfold lib.Reusable.YG0n.zero_shadow_ranges; left; reflexivity)) as HZ.
  cbn [fst snd] in HZ. unfold lib.Reusable.YG0v.zero_shadow in HZ.
  unfold lib.Reusable.YG0f.page_aligned, lib.Reusable.YG0f.kHighMemBeg, lib.Reusable.YG0f.kHighMemEnd in *.
  unfold A.ProgBridge.range_visible, A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi,
    A.AsanRT.shadow_addr, A.AsanRT.ASAN_K.
  change (2 ^ 64) with 18446744073709551616.
  set (L := lib.Reusable.YG0f.ly_stk_lo ly) in *.
  set (Hh := lib.Reusable.YG0f.ly_stk_hi ly) in *.
  assert (EL : L = 4096 * (L / 4096)) by (pose proof (Z.div_mod L 4096 ltac:(lia)); lia).
  assert (EH : Hh = 4096 * (Hh / 4096)) by (pose proof (Z.div_mod Hh 4096 ltac:(lia)); lia).
  set (l := L / 4096) in *. set (h := Hh / 4096) in *.
  assert (EL8 : L / 8 = 512 * l)
    by (rewrite EL; replace (4096 * l) with (512 * l * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
  assert (EHL8 : (Hh - L) / 8 = 512 * (h - l))
    by (rewrite EL, EH; replace (4096 * h - 4096 * l) with (512 * (h - l) * 8) by lia;
        rewrite Z.div_mul by lia; reflexivity).
  pose proof (Z.div_mod lo 8 ltac:(lia)) as D0. pose proof (Z.mod_pos_bound lo 8 ltac:(lia)) as D0'.
  pose proof (Z.div_mod (lo + len - 1) 8 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (lo + len - 1) 8 ltac:(lia)) as D1'.
  pose proof (Z.div_mod (lo / 8 + 0x7fff8000) 8 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound (lo / 8 + 0x7fff8000) 8 ltac:(lia)) as D2'.
  pose proof (Z.div_mod ((lo + len - 1) / 8 + 0x7fff8000) 8 ltac:(lia)) as D3.
  pose proof (Z.mod_pos_bound ((lo + len - 1) / 8 + 0x7fff8000) 8 ltac:(lia)) as D3'.
  split; [lia |]. split; [lia |].
  intros a Ha.
  assert (HZa : lib.Reusable.YG0n.aview A.AB1v.tfibsegs (lib.Reusable.YA0n.w_H W) mem a = Some 0).
  { replace a with (lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF L +
                    (a - lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF L)) by lia.
    apply HZ. unfold lib.Reusable.YG0v.shadow_of_addr, lib.Reusable.YG0f.SHADOW_OFF.
    rewrite EL8, EHL8. lia. }
  unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict in HZa.
  destruct (lib.Reusable.YA0n.w_H W (Z_to_bv 64 a)) eqn:EHa; [exfalso | reflexivity].
  unfold lib.Reusable.YK11.seg_rom in HZa.
  rewrite (lib.Reusable.YK04.memory_read1_hidden A.AB1v.tfibsegs (lib.Reusable.YA0n.w_H W)
             (lib.Reusable.YA0n.w_Hoff W) _ EHa) in HZa.
  discriminate HZa.
Qed.

End Visible.

Print Assumptions win_vis.
Print Assumptions win_sh_vis.
