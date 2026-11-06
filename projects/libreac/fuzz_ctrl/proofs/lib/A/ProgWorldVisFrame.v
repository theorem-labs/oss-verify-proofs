(* lib/A/ProgWorldVisFrame.v -- fuzz_ctrl image A (libreac v1.9.0): two visibility statements of lib/A/ProgWorld.v
   Section Visible, proved.  Written by a Theorem Labs lane.
   STATEMENT TEXT: this file states a Theorem Labs lane's record text directly, `A.ProgWorld.frame_vis_stmt B` and
   `A.ProgWorld.glob_sh_vis_stmt B`.  It carried local word-for-word copies of those two Definitions (from
   ProgWorld.v (a version not in this delivery; from a working branch c03ce1627b6)) while A.ProgWorld could not
   compile on this base, and was re-pointed on 10-29 at 05:4xZ once it could.  The copies were character-identical
   to ProgWorld's, so the proofs did not change and no bridge lemma exists.  Replay verified on a Theorem Labs lane's integration
   head a48c4068c6e.
     frame_vis    from AR_frames_law (lib/Reusable/YG0d.v:447-455): the frame bytes and the frame's shadow bytes
                  are present, so visible.  The law gives only frame_addr mod 32 = 0; the proof uses only its
                  consequence frame_addr mod 8 = 0, which makes frame_addr / 8 + fs_frame_bytes / 8 =
                  (frame_addr + fs_frame_bytes) / 8 for every size.
     glob_sh_vis  from AR_zshadow_law (YG0d.v:435-438) at an as_zero_shadow entry (zero_shadow_ranges, YG0n.v:188-189):
                  each shadow byte of the range reads Some 0 through the view, and a byte the view reads is visible
                  (vis_of_aview, through w_Hoff).  The range bounds are asyms_ok's aso_zshadow (YG0f.v:191), in ARm.
   In both, the 64-byte hull premise puts the 8-aligned shadow word cover [sh_al8_lo lo, sh_al8_hi lo len) =
   [ASAN_K + 8 * (lo / 64), ASAN_K + 8 * ((lo + len - 1) / 64) + 8) inside the shadow bytes the law states. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04 Reusable.YA0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG01 Reusable.YG0f Reusable.YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0n Reusable.YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorld A.AB1v A.AsanRT A.ProgBridge A.Prog.rng_asan.
Local Open Scope Z_scope.
Local Notation segs := A.AB1v.tfibsegs (only parsing).   (* as ProgWorld.v:80 *)

(* A byte the view reads is visible: a hidden byte lies in no segment (w_Hoff), so the view reads None there. *)
Lemma vis_of_aview : forall (sg : list Segment) (W : lib.Reusable.YA0n.world sg) (mem : word -> option byte) (a : Z),
  lib.Reusable.YG0n.aview sg (lib.Reusable.YA0n.w_H W) mem a <> None ->
  lib.Reusable.YA0n.w_H W (Z_to_bv 64 a) = false.
Proof.
  intros sg W mem a Hv.
  destruct (lib.Reusable.YA0n.w_H W (Z_to_bv 64 a)) eqn:Hh; [exfalso; apply Hv | reflexivity].
  unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict. rewrite Hh.
  unfold lib.Reusable.YK11.seg_rom, memory_read. change (Z.of_N 1) with 1.
  rewrite (lib.Reusable.YA0n.w_Hoff W _ Hh). reflexivity.
Qed.

(* The 8-aligned shadow word of a byte x (A.AsanRT.shadow_addr x = x / 8 + ASAN_K, ASAN_K = 0x7fff8000 =
   8 * 268431360), the form sh_al8_lo / sh_al8_hi round to. *)
Lemma shadow_word_floor : forall x, (x / 8 + 0x7fff8000) / 8 * 8 = 0x7fff8000 + 8 * (x / 64).
Proof.
  intros x. change 0x7fff8000 with (268431360 * 8) at 1. rewrite Z.div_add by lia.
  rewrite Z.div_div by lia. change (8 * 8) with 64. lia.
Qed.

Section Visible.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : lib.Reusable.YG0f.asyms.

(* ---- copied from ProgWorld.v c03ce1627b6 :336-362, word for word ---- *)
(* ---- end of the copied text ---- *)

Lemma frame_vis : A.ProgWorld.frame_vis_stmt B.
Proof.
  intros HL ly S W mem md cid pos lo len HAR Hin Hlo Hhi.
  assert (Hfl : lib.Reusable.YG0d.AR_frames_law segs B) by (destruct HL; assumption).
  destruct (Hfl ly S W mem md cid pos HAR Hin) as (Hal & Happ & Hby & Hsh).
  destruct (@lib.Reusable.YG0f.ASAN_CEIL_range rc) as [Hce _].
  unfold lib.Reusable.YG0f.in_app, lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg in Happ.
  set (F := lib.Reusable.YG0f.frame_addr ly cid pos) in *.
  set (sz := lib.Reusable.YG00.fs_frame_bytes cid) in *.
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HF : 4096 <= F /\ F + sz <= 0x7fffff800000) by lia.
  split.
  - (* the frame bytes: present, so visible *)
    split; [lia |]. split; [rewrite P64; lia |]. intros a Ha.
    destruct (Hby a ltac:(lia)) as [[Hv _] _]. exact Hv.
  - (* the shadow word cover lies in the frame's shadow bytes [shadow_addr F, shadow_addr F + sz / 8) *)
    intros Hlen HqL HqH.
    destruct (Z.eq_dec len 0) as [E0 | Hn]; [left; exact E0 | right].
    unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K.
    rewrite !shadow_word_floor.
    pose proof (Z.div_mod lo 64 ltac:(lia)) as Dq. pose proof (Z.mod_pos_bound lo 64 ltac:(lia)) as Mq.
    pose proof (Z.div_mod (lo + len - 1) 64 ltac:(lia)) as Dh.
    pose proof (Z.mod_pos_bound (lo + len - 1) 64 ltac:(lia)) as Mh.
    pose proof (Z.div_mod F 32 ltac:(lia)) as D32.
    pose proof (Z.div_mod F 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M8.
    pose proof (Z.div_mod sz 8 ltac:(lia)) as Ds. pose proof (Z.mod_pos_bound sz 8 ltac:(lia)) as Ms.
    assert (HF8 : F mod 8 = 0) by lia.
    split; [lia |]. split; [rewrite P64; lia |]. intros s Hs.
    assert (Hi : 0 <= s - lib.Reusable.YG0f.shadow_addr F < sz / 8).
    { unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF. lia. }
    destruct (Hsh _ Hi) as [[Hv _] _].
    replace (lib.Reusable.YG0f.shadow_addr F + (s - lib.Reusable.YG0f.shadow_addr F)) with s in Hv by ring.
    exact Hv.
Qed.

Lemma glob_sh_vis : A.ProgWorld.glob_sh_vis_stmt B.
Proof.
  intros HL ly S W mem md r lo len HAR Hr Hlen HqL HqH.
  destruct (Z.eq_dec len 0) as [E0 | Hn]; [left; exact E0 | right].
  assert (Hzl : lib.Reusable.YG0d.AR_zshadow_law segs B) by (destruct HL; assumption).
  assert (Hr' : In r (lib.Reusable.YG0n.zero_shadow_ranges B ly))
    by (unfold lib.Reusable.YG0n.zero_shadow_ranges; right; exact Hr).
  pose proof (Hzl ly S W mem md r HAR Hr') as Hz.
  assert (Hok : lib.Reusable.YG0f.asyms_ok B) by (destruct HAR as [[] _]; assumption).
  destruct (proj1 (Forall_forall _ _) (lib.Reusable.YG0f.aso_zshadow _ Hok) r Hr) as (Hr0 & Hr1 & Hr2 & Hr3 & Hr4).
  unfold lib.Reusable.YG0f.kLowMemEnd in Hr4.
  unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K.
  rewrite !shadow_word_floor.
  pose proof (Z.div_mod lo 64 ltac:(lia)) as Dq. pose proof (Z.mod_pos_bound lo 64 ltac:(lia)) as Mq.
  pose proof (Z.div_mod (lo + len - 1) 64 ltac:(lia)) as Dh.
  pose proof (Z.mod_pos_bound (lo + len - 1) 64 ltac:(lia)) as Mh.
  pose proof (Z.div_mod (fst r) 8 ltac:(lia)) as Df. pose proof (Z.mod_pos_bound (fst r) 8 ltac:(lia)) as Mf.
  pose proof (Z.div_mod (snd r) 8 ltac:(lia)) as Dn. pose proof (Z.mod_pos_bound (snd r) 8 ltac:(lia)) as Mn.
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  split; [lia |]. split; [rewrite P64; lia |]. intros s Hs.
  apply (vis_of_aview _ W mem).
  assert (Hi : 0 <= s - (lib.Reusable.YG0f.SHADOW_OFF + fst r / 8) < snd r / 8).
  { unfold lib.Reusable.YG0f.SHADOW_OFF. lia. }
  pose proof (Hz _ Hi) as Hzi. unfold lib.Reusable.YG0v.shadow_of_addr in Hzi.
  replace (lib.Reusable.YG0f.SHADOW_OFF + fst r / 8 + (s - (lib.Reusable.YG0f.SHADOW_OFF + fst r / 8))) with s
    in Hzi by ring.
  rewrite Hzi. discriminate.
Qed.
End Visible.

Print Assumptions frame_vis.
Print Assumptions glob_sh_vis.
