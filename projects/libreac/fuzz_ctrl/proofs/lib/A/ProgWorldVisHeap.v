(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* lib/A/ProgWorldVisHeap.v -- fuzz_ctrl image A: the two heap rows of lib/A/ProgWorld.v Section Visible, proved.
   heap_vis (plan row V3): every byte of a sub-range of a live heap block is visible.  Source: AR_blocks_law
   (YG0d.v:423-429), whose apresent conjunct hides no byte of the block and whose placement facts
   4096 <= p, p + req_size n <= alloc_ceiling (< 2^47, YM05.alloc_ceiling_lt) give the two bounds.
   heap_sh_vis (V4): the shadow word cover of such a sub-range is visible.  Source: AR_shadow_law's
   shadow_hull_vis (YG0d.v:430-434, :310-311) over the whole block; the cover of a sub-range lies in the block's
   cover.  sh_al8_lo / sh_al8_hi are stated over A.AsanRT.shadow_addr (a / 8 + ASAN_K), shadow_hull_vis over
   YG0f.shadow_addr (SHADOW_OFF + a / 8); both offsets are 0x7fff8000.  A byte the view reads is visible: a
   hidden byte is masked out of mem by mrestrict and, by the world's w_Hoff, lies in no segment, so seg_rom has
   no byte for it either.

   STATEMENT TEXT: this file states a Theorem Labs lane's record text directly - `A.ProgWorld.heap_vis_stmt B` and
   `A.ProgWorld.heap_sh_vis_stmt B` - having been re-pointed on 10-29 at 05:4xZ from the local word-for-word copies
   it carried while A.ProgWorld could not compile here (lib/A/AE2k.v and AF0l.v carry undefined
   `port_core_refused_*` names from the planning core's relocation run 5a85b67a5d8).  The copies were diffed against
   ProgWorld.v at c03ce1627b6 before the change and were character-identical, so the proofs did not change and there
   is no bridge lemma.  Replay verified on a Theorem Labs lane's integration head a48c4068c6e. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YG00 Reusable.YG0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0n Reusable.YG0d Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorld A.AB1v A.AsanRT A.ProgBridge A.Prog.rng_asan.
Local Open Scope Z_scope.
Notation segs := A.AB1v.tfibsegs (only parsing).           (* as lib/A/ProgWorld.v:80 *)

Section Visible.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : lib.Reusable.YG0f.asyms.

Lemma heap_vis : A.ProgWorld.heap_vis_stmt B.
Proof.
  intros HL ly S W mem md p n lo len HAR Hin Hlo Hhi.
  destruct (lib.Reusable.YG0d.al_blocks _ _ HL ly S W mem md p n HAR Hin) as (_ & H4096 & Hceil & _ & Hpres & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_lt rc) as Hc.
  split; [lia|]. split; [lia|].
  intros a Ha. destruct (Hpres a ltac:(lia)) as [[Hv _] _]. exact Hv.
Qed.

Lemma heap_sh_vis : A.ProgWorld.heap_sh_vis_stmt B.
Proof.
  intros HL ly S W mem md p n lo len HAR Hin Hlo Hhi Hlen.
  destruct (Z.eq_dec len 0) as [->|Hne]; [left; reflexivity|right].
  destruct (lib.Reusable.YG0d.al_blocks _ _ HL ly S W mem md p n HAR Hin) as (_ & H4096 & Hceil & _).
  destruct (lib.Reusable.YG0d.al_shadow _ _ HL ly S W mem md p n HAR Hin) as [_ Hh].
  pose proof (@lib.Reusable.YM05.alloc_ceiling_lt rc) as Hc.
  assert (EA : forall x, A.AsanRT.shadow_addr x = lib.Reusable.YG0f.shadow_addr x).
  { intros x. unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K, lib.Reusable.YG0f.shadow_addr,
      lib.Reusable.YG0f.SHADOW_OFF. lia. }
  unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi. rewrite !EA.
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
  unfold lib.Reusable.YK11.seg_rom.
  rewrite (lib.Reusable.YK04.memory_read1_hidden _ _ (lib.Reusable.YA0n.w_Hoff W) _ EH). reflexivity.
Qed.

End Visible.

Print Assumptions heap_vis.
Print Assumptions heap_sh_vis.
