(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 3018 of its 3112 lines of code are new or changed and 934 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4e1.v, with its module paths and module names changed; 2867 of its 3071 lines of code are new or changed and 2908 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW1.v, with its module names changed; 70 of its 100 lines of code are new or changed and 3041 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/ProgWorldVisWin.v (a working branch
   26edf006f53, byte-identical to a Theorem Labs lane's copy on a working branch 5c587a76cbc; re-synced to
   a working branch 1d23ced37fd = a working branch b3abb4ad52d, where A drops its two copied _stmt
   Definitions, Requires A.ProgWorld and states `A.ProgWorld.win_vis_stmt B` / `A.ProgWorld.win_sh_vis_stmt B`,
   which this twin already did).  What differs from A:
   - the two statements are lib.B.ProgWorld's own, `lib.B.ProgWorld.win_vis_stmt B` /
     `lib.B.ProgWorld.win_sh_vis_stmt B`, as A's are A.ProgWorld's.  lib.B.ProgWorld fixes the journal's sink_head to
     lib.Reusable.YE2k.tfib_sink_head (the twin of A.AE2k's); here it stays a Section Context, as in A, so the lemmas
     hold for EVERY sink_head instance, that one included.
   - YP09, which also exists as lib/B/Reusable/YP09.v, is Required by its CORE path (`From ...fuzz_ctrl.lib.Reusable
     Require YP09`, fix_require6.py, as lib/B/ProgWorld.v on the base), where A writes `Require ... Reusable.YP09`.
   - module names: A.ProgBridge -> lib.B.ProgBridge, A.Prog.rng_asan -> lib.B.Prog.rng_asan, A.AsanRT ->
     lib.B.AsanRT, A.AB1v -> lib.Reusable.YB1v (tfibsegs = AsanUbsan.M.loaded_segments, YB1v.v:12).
   NO image-A number is carried over.  Every constant in the proofs is the core's or image-independent:
     0x7fff8000  = lib.B.AsanRT.ASAN_K (B/AsanRT.v:8) = lib.Reusable.YG0f.SHADOW_OFF (YG0f.v:12), the ASan shadow
                   offset, the same in both images;
     140737488355328 = 2 ^ 47, the core's astk_ok stack bound (lib.Reusable.YCbq.v:333);
     18446744073709551616 = 2 ^ 64, the address space;
     4096 / 8 / 512 are the page size and the ASan granule, core (lib.Reusable.YG0f.page_aligned, YG0v.v:35).
   The proofs are A's, step for step: every fact they use lives in lib.Reusable, which both images share.
     win_vis     : the callee's stack window is visible at the cut world, from the journal's presence conjunct
                   (YCbq.v:365) and its stack bounds astk_ok (YCbq.v:332-334).
     win_sh_vis  : the 8-aligned shadow word cover of a stack sub-range is visible, from the stack entry of
                   zero_shadow_ranges (YG0n.v:188-189) through AR_zshadow_law (YG0d.v:435-438); the stack bounds
                   are page-aligned (layout_ok lo_top, YG0f.v:322-324), so the aligned cover stays inside the
                   stack's shadow.
   img_vis (V2) is not stated in ProgWorld.v: lib.B.ProgBridge.img_vis_W proves it for every world. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04 Reusable.YA0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0f Reusable.YG0n Reusable.YG0d Reusable.YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YB1v B.AsanRT B.ProgBridge B.Prog.rng_asan.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgWorld.
(* The six collided modules (porter's gate, a Theorem Labs lane via a Theorem Labs lane 04:23Z, amendment (b) 04:33Z): Required
   by the unambiguous `lib.Reusable` path, never by `From ...lib Require Reusable.X` (that partial path matches
   lib.Reusable.X AND lib.B.Reusable.X).  This file takes the CORE copies, the ones lib/A/ProgWorldVisWin.v takes
   and the ones lib.Reusable.YCbq / YG0n / YG0d are built on, never lib.B.Reusable.*.  Their uses below carry the
   full logical path. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YI16.
Local Open Scope Z_scope.

Section Visible.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
        {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}
        {SK : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.sink_head}.
Variable B : lib.Reusable.YG0f.asyms.

(* The window [lo, lo + len) lies in the journal's stack window [sp0 - STK, sp0), every byte of which is present
   (so not hidden) at the cut; astk_ok puts the window between alloc_ceiling > 0 and 2 ^ 47. *)
Lemma win_vis : lib.B.ProgWorld.win_vis_stmt B.
Proof.
  unfold lib.B.ProgWorld.win_vis_stmt.
  intros STK sp0 FPj ly S W mem md own lyc Sc Wc memc mdc k lo len HJ Hlo Hhi.
  destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  destruct Hstk as (_ & HSTK & Hceil & Hsp0 & Hsphi & H47 & _).
  pose proof (@OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.alloc_ceiling_value rc) as [[Hc0 _] _].
  change (2 ^ 47) with 140737488355328 in H47.
  unfold lib.B.ProgBridge.range_visible. change (2 ^ 64) with 18446744073709551616.
  split; [lia |]. split; [lia |].
  intros a Ha. exact (proj1 (Hpres a ltac:(lia))).
Qed.

(* The stack's zero shadow covers the shadow bytes [SHADOW_OFF + L / 8, SHADOW_OFF + H / 8) of [L, H) =
   [ly_stk_lo, ly_stk_hi).  Both ends are page-aligned and SHADOW_OFF = ASAN_K is a multiple of 8, so rounding the
   first shadow byte of [lo, lo + len) down and the last one up to a multiple of 8 stays in that range.  A byte the
   view reads as Some 0 is not hidden: a hidden byte is in no segment (w_Hoff), so the view reads None there. *)
Lemma win_sh_vis : lib.B.ProgWorld.win_sh_vis_stmt B.
Proof.
  unfold lib.B.ProgWorld.win_sh_vis_stmt.
  intros LAWS ly S W mem md lo len HAR Hlo Hhi Hlen.
  destruct (Z.eq_dec len 0) as [E0 | Hne]; [left; exact E0 | right].
  pose proof (lib.Reusable.YG0n.am_layout B ly S _ (proj1 HAR)) as HLY.
  pose proof (lib.Reusable.YG0f.lo_top ly HLY) as (_ & _ & _ & Lhi & Plo & Phi & Lbeg).
  pose proof (lib.Reusable.YG0d.al_zshadow _ _ LAWS ly S W mem md
    (lib.Reusable.YG0f.ly_stk_lo ly, lib.Reusable.YG0f.ly_stk_hi ly - lib.Reusable.YG0f.ly_stk_lo ly) HAR
    ltac:(unfold lib.Reusable.YG0n.zero_shadow_ranges; left; reflexivity)) as HZ.
  cbn [fst snd] in HZ. unfold lib.Reusable.YG0v.zero_shadow in HZ.
  unfold lib.Reusable.YG0f.page_aligned, lib.Reusable.YG0f.kHighMemBeg, lib.Reusable.YG0f.kHighMemEnd in *.
  unfold lib.B.ProgBridge.range_visible, lib.B.Prog.rng_asan.sh_al8_lo, lib.B.Prog.rng_asan.sh_al8_hi,
    lib.B.AsanRT.shadow_addr, lib.B.AsanRT.ASAN_K.
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
  assert (HZa : lib.Reusable.YG0n.aview lib.Reusable.YB1v.tfibsegs (lib.Reusable.YA0n.w_H W) mem a = Some 0).
  { replace a with (lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF L +
                    (a - lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF L)) by lia.
    apply HZ. unfold lib.Reusable.YG0v.shadow_of_addr, lib.Reusable.YG0f.SHADOW_OFF.
    rewrite EL8, EHL8. lia. }
  unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict in HZa.
  destruct (lib.Reusable.YA0n.w_H W (Z_to_bv 64 a)) eqn:EHa; [exfalso | reflexivity].
  unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom in HZa.
  rewrite (lib.Reusable.YK04.memory_read1_hidden lib.Reusable.YB1v.tfibsegs (lib.Reusable.YA0n.w_H W)
             (lib.Reusable.YA0n.w_Hoff W) _ EHa) in HZa.
  discriminate HZa.
Qed.

End Visible.
