(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, the R form of lib/Prog/PvMain0.v's pv_fd_zero (:187) over lib/A/PRH_Reader.v's
   reader predicates: a zeroed node is freeable by pj_free to any depth with no block (the all-zero struct a skipped
   reading leaves; the tpj_free_specX `v <> 0` arm with D = [], PRH_FnPj.v blob 43642538e741 :327). #102 point 9
   (the internal file PLAN-cno-caw-102.md section 4), written once by a Theorem Labs lane; the cno / caw walk lanes cite it.
   rule 24: no function proved. rule 24: proves no function (kind: segment-kit lemma).
   THIS LEAF IS IMAGE-FREE: it Requires only lib.A.PRH_Reader (and Stdlib / LinuxProcessSemantics), states no image
   value, and runs no vm_compute over rsegs or any segment list. THE MOVE WAS FORCED, not chosen: the lemma was first
   written in PvMain0.v (afdd7e86e67b), and a #102 file that Requires PvMain0.v cannot build on the new-pin route
   #102 pins, because PvMain0.v:68 rsegs_in (a plain-image fact, `vm_compute` over rsegs) fails on the #102 binaries
   (the #102 pins route, commit 9ee3c8f2403d, build log of 2026-10-29T13:37Z:
   "Unable to unify true with false"). Moved here by a Theorem Labs lane's yes (13:43Z, relayed by the lead); deleted from
   PvMain0.v in the same commit.
   THE pj_rwR PREMISE: PRH_Reader.pj_zeroR is garr8 of 56 zero bytes ALONE (PRH_Reader.v blob 91d2dbd40054 :98), unlike
   plain pj_zero (PjStruct.v:106, which carries pj_rw), while pj_fdR -> pj_fshapeR -> pj_hdrR asks pj_rwR (v mod 8 = 0
   and 56 writable bytes). The bare form `pj_zeroR -> pj_fdR n v []` is FALSE: at v = 1 with 56 zero bytes at 1 .. 56,
   pj_zeroR holds and pj_fdR fails (1 mod 8 <> 0). At a pj_free call the premise is prhPj_slot's own pj_rwR conjunct
   (PRH_FnPj.v:149), so the caller pays nothing.
   Numerals: 56 (LENGTH: the node), 4 / 8 (LENGTH: header field widths). No ADDRESS. *)
From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
Import ListNotations.
Local Open Scope Z_scope.

Lemma pv_fd_zeroR : forall (sg : list Segment) (m : word -> option byte) (lblk : Z -> Z -> Prop) (n : nat) (v : Z),
  PRH_Reader.pj_rwR sg m v -> PRH_Reader.pj_zeroR sg m v -> PRH_Reader.pj_fdR sg m lblk n v [].
Proof.
  intros sg m lblk n v Hrw Hz.
  assert (L0 : forall w k, YO0f.le_byte 0 w k = 0).
  { intros w k. unfold YO0f.le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l.
    reflexivity. }
  assert (V : forall a w, v <= a -> a + Z.of_nat w <= v + 56 -> YI04.val_mem sg m a w 0).
  { intros a w H1 H2 k Hk.
    assert (Hj : (Z.to_nat (a - v) + k < length (repeat 0 56))%nat) by (rewrite repeat_length; lia).
    destruct (Hz _ Hj) as [Hb _]. specialize (Hb 0%nat ltac:(lia)). rewrite nth_repeat, L0 in Hb. rewrite L0.
    replace (a + Z.of_nat k) with (v + Z.of_nat (Z.to_nat (a - v) + k) + Z.of_nat 0) by lia. exact Hb. }
  assert (HH : PRH_Reader.pj_hdrR sg m v 0 0 0 0 0 0 0).
  { split; [exact Hrw|].
    split; [split; [lia | apply V; cbn; lia]|].
    repeat (split; [split; [lia | apply V; cbn; lia]|]).
    split; [lia | apply V; cbn; lia]. }
  destruct n as [|n]; cbn [PRH_Reader.pj_fdR]; unfold PRH_Reader.pj_fshapeR;
    (split; [constructor|]); (split; [intros b x Hb; destruct Hb|]);
    exists 0, 0, 0, 0, 0, 0, 0, false, [], [], [], [];
    (split; [exact HH|]); (split; [left; split; reflexivity|]);
    (split; [left; split; [reflexivity | split; reflexivity]|]);
    (split; [left; split; [reflexivity | split; reflexivity]|]);
    (split; [exact (Permutation_refl [])|]).
  - split; reflexivity.
  - exact eq_refl.
Qed.
