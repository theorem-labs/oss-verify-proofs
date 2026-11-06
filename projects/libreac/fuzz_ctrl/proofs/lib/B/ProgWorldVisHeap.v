(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/ProgWorldVisHeap.v (a working branch
   26edf006f53, byte-identical to a Theorem Labs lane's copy on a working branch 5c587a76cbc; re-synced to
   a working branch 1d23ced37fd = a working branch b3abb4ad52d, where A drops its two copied _stmt
   Definitions, Requires A.ProgWorld and states `A.ProgWorld.heap_vis_stmt B` / `A.ProgWorld.heap_sh_vis_stmt B`,
   which this twin already did).  What differs from A:
   - the two statements are lib.B.ProgWorld's own, `lib.B.ProgWorld.heap_vis_stmt B` /
     `lib.B.ProgWorld.heap_sh_vis_stmt B`, as A's are A.ProgWorld's.
   - YP09, which also exists as lib/B/Reusable/YP09.v, is Required by its CORE path (`From ...fuzz_ctrl.lib.Reusable
     Require YP09`, fix_require6.py, as lib/B/ProgWorld.v on the base), where A writes `Require ... Reusable.YP09`.
   - module names: A.ProgBridge -> lib.B.ProgBridge, A.Prog.rng_asan -> lib.B.Prog.rng_asan, A.AsanRT ->
     lib.B.AsanRT, A.AB1v -> lib.Reusable.YB1v (not Required here: the segment list is the statements' own).
   NO image-A number is carried over; the proofs name no literal at all.  lib.B.AsanRT.ASAN_K (B/AsanRT.v:8,
   0x7fff8000) and lib.Reusable.YG0f.SHADOW_OFF (YG0f.v:12) are shown equal by EA, as in A; the ASan shadow offset
   is the same in both images.
   The proofs are A's, step for step: every fact they use lives in lib.Reusable, which both images share.
     heap_vis (plan row V3): every byte of a sub-range of a live heap block is visible.  Source: AR_blocks_law
     (YG0d.v:423-429), whose apresent conjunct hides no byte of the block and whose placement facts
     4096 <= p, p + req_size n <= alloc_ceiling (< 2 ^ 47, lib.Reusable.YM05.alloc_ceiling_lt) give the bounds.
     heap_sh_vis (V4): the shadow word cover of such a sub-range is visible.  Source: AR_shadow_law's
     shadow_hull_vis (YG0d.v:430-434), over the whole block; the cover of a sub-range lies in the block's cover.
     A byte the view reads is visible: a hidden byte is masked out of mem by mrestrict and, by the world's w_Hoff,
     lies in no segment, so seg_rom has no byte for it either. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YP09.
(* The six collided modules (porter's gate, a Theorem Labs lane via a Theorem Labs lane 04:23Z, amendment (b) 04:33Z): Required by
   the unambiguous `lib.Reusable` path, never by `From ...lib Require Reusable.X`, and used by their full logical
   path.  This file takes the CORE copies, as lib/A/ProgWorldVisHeap.v does. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YG00 Reusable.YG0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0n Reusable.YG0d Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.AsanRT B.ProgBridge B.Prog.rng_asan B.ProgWorld.
Local Open Scope Z_scope.

Section Visible.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
        {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}.
Variable B : lib.Reusable.YG0f.asyms.

Lemma heap_vis : lib.B.ProgWorld.heap_vis_stmt B.
Proof.
  unfold lib.B.ProgWorld.heap_vis_stmt.
  intros HL ly S W mem md p n lo len HAR Hin Hlo Hhi.
  destruct (lib.Reusable.YG0d.al_blocks _ _ HL ly S W mem md p n HAR Hin) as (_ & H4096 & Hceil & _ & Hpres & _).
  pose proof (@OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.alloc_ceiling_lt rc) as Hc.
  split; [lia|]. split; [lia|].
  intros a Ha. destruct (Hpres a ltac:(lia)) as [[Hv _] _]. exact Hv.
Qed.

Lemma heap_sh_vis : lib.B.ProgWorld.heap_sh_vis_stmt B.
Proof.
  unfold lib.B.ProgWorld.heap_sh_vis_stmt.
  intros HL ly S W mem md p n lo len HAR Hin Hlo Hhi Hlen.
  destruct (Z.eq_dec len 0) as [->|Hne]; [left; reflexivity|right].
  destruct (lib.Reusable.YG0d.al_blocks _ _ HL ly S W mem md p n HAR Hin) as (_ & H4096 & Hceil & _).
  destruct (lib.Reusable.YG0d.al_shadow _ _ HL ly S W mem md p n HAR Hin) as [_ Hh].
  pose proof (@OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.alloc_ceiling_lt rc) as Hc.
  assert (EA : forall x, lib.B.AsanRT.shadow_addr x = lib.Reusable.YG0f.shadow_addr x).
  { intros x. unfold lib.B.AsanRT.shadow_addr, lib.B.AsanRT.ASAN_K, lib.Reusable.YG0f.shadow_addr,
      lib.Reusable.YG0f.SHADOW_OFF. lia. }
  unfold lib.B.Prog.rng_asan.sh_al8_lo, lib.B.Prog.rng_asan.sh_al8_hi. rewrite !EA.
  assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8).
  { intros u v Huv. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia. }
  pose proof (R8 _ _ (lib.Reusable.YCbq.shadow_mono p lo Hlo)) as M1.
  pose proof (R8 _ _ (lib.Reusable.YCbq.shadow_mono (lo + len - 1) (p + lib.Reusable.YG00.req_size n - 1)
                        ltac:(lia))) as M2.
  set (sl := lib.Reusable.YG0f.shadow_addr lo) in *.
  set (sh := lib.Reusable.YG0f.shadow_addr (lo + len - 1)) in *.
  assert (Hsl : 0 <= sl).
  { subst sl. unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF.
    pose proof (Z.div_pos lo 8 ltac:(lia) ltac:(lia)). lia. }
  assert (Hsh : sh <= lib.Reusable.YG0f.SHADOW_OFF + (lo + len - 1)).
  { subst sh. unfold lib.Reusable.YG0f.shadow_addr.
    pose proof (Z.div_le_upper_bound (lo + len - 1) 8 (lo + len - 1) ltac:(lia) ltac:(lia)). lia. }
  pose proof (Z.div_pos sl 8 ltac:(lia) ltac:(lia)) as D1.
  pose proof (Z.mul_div_le sh 8 ltac:(lia)) as D2.
  unfold lib.Reusable.YG0f.SHADOW_OFF in Hsh.
  split; [lia|]. split; [lia|].
  intros s Hs.
  destruct (lib.Reusable.YA0n.w_H W (Z_to_bv 64 s)) eqn:EH; [exfalso|reflexivity].
  apply (Hh s ltac:(lia)).
  unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict. rewrite EH.
  unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom.
  rewrite (lib.Reusable.YK04.memory_read1_hidden _ _ (lib.Reusable.YA0n.w_Hoff W) _ EH). reflexivity.
Qed.

End Visible.
