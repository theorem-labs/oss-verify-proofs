(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/ProgWorldVisFrame.v (a working branch
   26edf006f53, byte-identical to a Theorem Labs lane's copy on a working branch 5c587a76cbc; re-synced to
   a working branch 1d23ced37fd = a working branch b3abb4ad52d, where A drops its two copied _stmt
   Definitions, Requires A.ProgWorld and states `A.ProgWorld.frame_vis_stmt B` / `A.ProgWorld.glob_sh_vis_stmt B`,
   which this twin already did).  What differs from A:
   - the two statements are lib.B.ProgWorld's own, `lib.B.ProgWorld.frame_vis_stmt B` /
     `lib.B.ProgWorld.glob_sh_vis_stmt B`, as A's are A.ProgWorld's.
   - YP09, which also exists as lib/B/Reusable/YP09.v, is Required by its CORE path (`From ...fuzz_ctrl.lib.Reusable
     Require YP09`, fix_require6.py, as lib/B/ProgWorld.v on the base), where A writes `Require ... Reusable.YP09`.
   - module names: A.ProgBridge -> lib.B.ProgBridge, A.Prog.rng_asan -> lib.B.Prog.rng_asan, A.AsanRT ->
     lib.B.AsanRT, A.AB1v -> lib.Reusable.YB1v (not Required here: vis_of_aview holds for every segment list, and
     the statements carry their own).
   NO image-A number is carried over.  The two literals are image-independent:
     0x7fff8000 = lib.B.AsanRT.ASAN_K (B/AsanRT.v:8) = lib.Reusable.YG0f.SHADOW_OFF (YG0f.v:12), the ASan shadow
                  offset, the same in both images, and 0x7fff8000 = 268431360 * 8 in shadow_word_floor;
     0x7fffff800000 is the core's ASAN_CEIL upper bound (lib.Reusable.YG0f.ASAN_CEIL_range, YG0f.v:16).
   The proofs are A's, step for step: every fact they use lives in lib.Reusable, which both images share.
     frame_vis    from AR_frames_law (lib/Reusable/YG0d.v:447-455): the frame bytes and the frame's shadow bytes
                  are present, so visible.  The law gives only frame_addr mod 32 = 0; the proof uses only its
                  consequence frame_addr mod 8 = 0, which makes frame_addr / 8 + fs_frame_bytes / 8 =
                  (frame_addr + fs_frame_bytes) / 8 for every size.
     glob_sh_vis  from AR_zshadow_law (YG0d.v:435-438) at an as_zero_shadow entry (zero_shadow_ranges,
                  YG0n.v:188-189): each shadow byte of the range reads Some 0 through the view, and a byte the
                  view reads is visible (vis_of_aview, through w_Hoff).  The range bounds are asyms_ok's
                  aso_zshadow (YG0f.v:191), in ARm.
   In both, the 64-byte hull premise puts the 8-aligned shadow word cover [sh_al8_lo lo, sh_al8_hi lo len) =
   [ASAN_K + 8 * (lo / 64), ASAN_K + 8 * ((lo + len - 1) / 64) + 8) inside the shadow bytes the law states. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04 Reusable.YA0n.
(* The six collided modules (porter's gate, a Theorem Labs lane via a Theorem Labs lane 04:23Z, amendment (b) 04:33Z): Required by
   the unambiguous `lib.Reusable` path, never by `From ...lib Require Reusable.X`, and used by their full logical
   path.  This file takes the CORE copies, as lib/A/ProgWorldVisFrame.v does. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG01 Reusable.YG0f Reusable.YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0n Reusable.YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.AsanRT B.ProgBridge B.Prog.rng_asan B.ProgWorld.
Local Open Scope Z_scope.

(* A byte the view reads is visible: a hidden byte lies in no segment (w_Hoff), so the view reads None there. *)
Lemma vis_of_aview : forall (sg : list Segment) (W : lib.Reusable.YA0n.world sg) (mem : word -> option byte) (a : Z),
  lib.Reusable.YG0n.aview sg (lib.Reusable.YA0n.w_H W) mem a <> None ->
  lib.Reusable.YA0n.w_H W (Z_to_bv 64 a) = false.
Proof.
  intros sg W mem a Hv.
  destruct (lib.Reusable.YA0n.w_H W (Z_to_bv 64 a)) eqn:Hh; [exfalso; apply Hv | reflexivity].
  unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict. rewrite Hh.
  unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom, memory_read.
  change (Z.of_N 1) with 1.
  rewrite (lib.Reusable.YA0n.w_Hoff W _ Hh). reflexivity.
Qed.

(* The 8-aligned shadow word of a byte x (lib.B.AsanRT.shadow_addr x = x / 8 + ASAN_K, ASAN_K = 0x7fff8000 =
   8 * 268431360, B/AsanRT.v:8), the form sh_al8_lo / sh_al8_hi round to. *)
Lemma shadow_word_floor : forall x, (x / 8 + 0x7fff8000) / 8 * 8 = 0x7fff8000 + 8 * (x / 64).
Proof.
  intros x. change 0x7fff8000 with (268431360 * 8) at 1. rewrite Z.div_add by lia.
  rewrite Z.div_div by lia. change (8 * 8) with 64. lia.
Qed.

Section Visible.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
        {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}.
Variable B : lib.Reusable.YG0f.asyms.

Lemma frame_vis : lib.B.ProgWorld.frame_vis_stmt B.
Proof.
  unfold lib.B.ProgWorld.frame_vis_stmt.
  intros HL ly S W mem md cid pos lo len HAR Hin Hlo Hhi.
  pose proof (lib.Reusable.YG0d.al_frames _ _ HL) as Hfl.   (* A: assert (AR_frames_law segs B) by destruct HL *)
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
    unfold lib.B.Prog.rng_asan.sh_al8_lo, lib.B.Prog.rng_asan.sh_al8_hi, lib.B.AsanRT.shadow_addr,
      lib.B.AsanRT.ASAN_K.
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

Lemma glob_sh_vis : lib.B.ProgWorld.glob_sh_vis_stmt B.
Proof.
  unfold lib.B.ProgWorld.glob_sh_vis_stmt.
  intros HL ly S W mem md r lo len HAR Hr Hlen HqL HqH.
  destruct (Z.eq_dec len 0) as [E0 | Hn]; [left; exact E0 | right].
  pose proof (lib.Reusable.YG0d.al_zshadow _ _ HL) as Hzl.  (* A: assert (AR_zshadow_law segs B) by destruct HL *)
  assert (Hr' : In r (lib.Reusable.YG0n.zero_shadow_ranges B ly))
    by (unfold lib.Reusable.YG0n.zero_shadow_ranges; right; exact Hr).
  pose proof (Hzl ly S W mem md r HAR Hr') as Hz.
  assert (Hok : lib.Reusable.YG0f.asyms_ok B) by (destruct HAR as [[] _]; assumption).
  destruct (proj1 (Forall_forall _ _) (lib.Reusable.YG0f.aso_zshadow _ Hok) r Hr) as (Hr0 & Hr1 & Hr2 & Hr3 & Hr4).
  unfold lib.Reusable.YG0f.kLowMemEnd in Hr4.
  unfold lib.B.Prog.rng_asan.sh_al8_lo, lib.B.Prog.rng_asan.sh_al8_hi, lib.B.AsanRT.shadow_addr,
    lib.B.AsanRT.ASAN_K.
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
