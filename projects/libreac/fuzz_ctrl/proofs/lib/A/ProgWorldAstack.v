(* lib/A/ProgWorldAstack.v -- fuzz_ctrl image A: proofs of two FROZEN statements of lib/A/ProgWorld.v Section FsOfAstack
   (a Theorem Labs lane's file, one writer; this file only proves them):
     ctl_fs_of_astack         : forall cid, A.ProgWorld.ctl_fs_of_astack_stmt B cid
     ctl_release_of_free_law  : forall cid, A.ProgWorld.ctl_release_of_free_law_stmt (SK := SK) B cid
   for every sink_head SK (Section Fs's Context, as ProgWorld.v's Section FsOfAstack); no instance is fixed here.
   Written by a Theorem Labs lane.  rule 24: no function proved.  These are bridge lemmas over the
   core's world (AR / ajournal / aview), not proofs of any binary function.  Type-check evidence is on the planning
   core only, never acceptance.

   Sources followed:
   - ctl_fs_of_astack: the premises are astack_malloc_realizes' post pieces (lib/Reusable/YG0d.v:291-300).  The frame
     facts come from AR at S' (YG0s.frame_facts, AR_frames_law, fs_flags_ok); ProgWorld.ctl_fs_geom_stmt turns
     ctrl's fs_frame / fs_flag / fs_B / fs_M / FS_SIZE into the core's frame_addr / flag_addr / fs_frame_bytes /
     fs_frames / kFakeStackSize; view -> mrd through ProgWorld.aview_vis_mrd.  The caller's stack below the callee
     window stays present by the post's frame condition (AR_stack_law at S and S') and YG0s.aview_present.
   - ctl_release_of_free_law: the fsteps twin of the core's aj_flag_store (YCbq.v:2362-2439), in the shape of
     ProgWorld.ajournal_of_fsteps: the machine side is ProgWorld.pws_fsteps_mem (no byte removed, every hidden byte
     kept), AR at stack_free_state from astack_free_law, the journal from YCbq.ajournal_after_write.  aj_flag_store's
     frame_flag_lawP and model_laws premises are not needed: the flag byte's facts are AR_flag_law and
     AR_client_img_law, and the new frame list is del_pos computed on the journal's frames.

   Byte-level helpers copied (renamed pw_ -> pwfs_) from a Theorem Labs lane's working file
   lib/A/ProgWorld_Fs.v, snapshot sha256
   394ad727c5b0... (03:10Z), lines named at each lemma. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorld.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YK1b YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04 Reusable.YK04R.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YG00 Reusable.YG01 Reusable.YG0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0n Reusable.YG0d Reusable.YCbq Reusable.YG0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG0v YP09 YO0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.asan_stack_malloc_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AsanRT A.Img0 A.ProgBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem Frame.
Local Open Scope Z_scope.
#[local] Notation segs := A.AB1v.tfibsegs (only parsing).

(* ---------------------------------------------------------------------------------------------------------
   Byte-level glue: the core's view (aview) against ctrl's mrd / bytes_at / stk. *)

(* scratch ProgWorld_Fs.v:25-26 pw_bv8 *)
Lemma pwfs_bv8 : forall z, bv_unsigned (Z_to_bv 8 z) = z mod 256.
Proof. intros z. rewrite Z_to_bv_unsigned. reflexivity. Qed.

(* scratch ProgWorld_Fs.v:34-41 pw_nth_le_bytes *)
Lemma pwfs_nth_le_bytes : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|].
  destruct k as [|k]; cbn [Z_to_le_bytes nth_error].
  - change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
  - rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. f_equal. lia.
Qed.

(* scratch ProgWorld_Fs.v:77-94 pw_view_mrd: a byte the view reads is visible, and mrd reads it. *)
Lemma pwfs_view_mrd : forall (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) (a v : Z),
  lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m a = Some v ->
  lib.Reusable.YA0n.w_H W (Z_to_bv 64 a) = false /\
  lib.Lib.Mem.mrd A.Img0.rsegs m (Z_to_bv 64 a) = Some (Z_to_bv 8 v).
Proof.
  intros W m a v Hv.
  assert (Hh : lib.Reusable.YA0n.w_H W (Z_to_bv 64 a) = false).
  { destruct (lib.Reusable.YA0n.w_H W (Z_to_bv 64 a)) eqn:Hh; [|reflexivity]. exfalso.
    unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict in Hv. rewrite Hh in Hv.
    unfold lib.Reusable.YK11.seg_rom in Hv.
    rewrite (lib.Reusable.YK04.memory_read1_hidden segs (lib.Reusable.YA0n.w_H W) (lib.Reusable.YA0n.w_Hoff W) _ Hh)
      in Hv.
    cbn [option_map] in Hv. discriminate Hv. }
  split; [exact Hh|].
  rewrite (A.ProgWorld.aview_vis_mrd W m a Hh) in Hv.
  destruct (lib.Lib.Mem.mrd A.Img0.rsegs m (Z_to_bv 64 a)) as [b|]; cbn [option_map] in Hv; [|discriminate Hv].
  injection Hv as <-. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* scratch ProgWorld_Fs.v:96-101 pw_present_view *)
Lemma pwfs_present_view : forall (H : word -> bool) (m : word -> option byte) (a : Z),
  lib.Reusable.YG0n.apresent H m a -> lib.Reusable.YG0n.aview segs H m a <> None.
Proof.
  intros H m a [Hh (b & Hb)]. unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict.
  rewrite Hh, Hb. cbn [option_map]. discriminate.
Qed.

(* scratch ProgWorld_Fs.v:103-112 pw_bytes_of_view *)
Lemma pwfs_bytes_of_view : forall (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) (a : Z) (bs : list byte),
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall i, (i < length bs)%nat -> exists b, nth_error bs i = Some b /\
     lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m (a + Z.of_nat i) = Some (bv_unsigned b)) ->
  lib.Lib.Mem.bytes_at A.Img0.rsegs m a bs.
Proof.
  intros W m a bs Ha Hb H. split; [exact Ha|]. split; [exact Hb|].
  intros i Hi. destruct (H i Hi) as (b & Hn & Hv). rewrite Hn.
  destruct (pwfs_view_mrd W m _ _ Hv) as [_ Hm]. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hm. exact Hm.
Qed.

(* scratch ProgWorld_Fs.v:114-122 pw_byte_of_view *)
Lemma pwfs_byte_of_view : forall (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) (a v : Z),
  lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m a = Some v -> 0 <= a < 2 ^ 64 -> 0 <= v < 256 ->
  lib.Lib.Mem.bytes_at A.Img0.rsegs m a (Z_to_bv 8 v :: nil).
Proof.
  intros W m a v Hv Ha Hr. apply (pwfs_bytes_of_view W); [lia | cbn [length]; lia |].
  intros i Hi. cbn [length] in Hi. destruct i as [|i]; [|lia].
  exists (Z_to_bv 8 v). split; [reflexivity|]. rewrite pwfs_bv8, Z.mod_small by lia.
  replace (a + Z.of_nat 0) with a by lia. exact Hv.
Qed.

(* scratch ProgWorld_Fs.v:125-137 pw_word_of_view: an 8-byte cell the view reads, as ctrl's le8 word. *)
Lemma pwfs_word_of_view : forall (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) (a v : Z),
  (forall k, (k < 8)%nat ->
     lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m (a + Z.of_nat k) = Some (lib.Reusable.YG0f.le_byte v 8 k)) ->
  0 <= a -> a + 8 <= 2 ^ 64 ->
  lib.Lib.Mem.bytes_at A.Img0.rsegs m a (lib.Lib.Mem.le8 (Z_to_bv 64 v)).
Proof.
  intros W m a v Hv Ha Hb. apply (pwfs_bytes_of_view W); [exact Ha | rewrite lib.Lib.Mem.length_le8; cbn; lia |].
  intros i Hi. rewrite lib.Lib.Mem.length_le8 in Hi.
  exists (Z_to_bv 8 (Z.shiftr (bv_unsigned (Z_to_bv 64 v)) (8 * Z.of_nat i))). split.
  - unfold lib.Lib.Mem.le8, word_to_le_bytes. apply pwfs_nth_le_bytes. exact Hi.
  - rewrite (Hv i Hi). apply f_equal. rewrite pwfs_bv8, Z_to_bv_unsigned. unfold lib.Reusable.YG0f.le_byte.
    change (8 * Z.of_nat 8) with 64. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). reflexivity.
Qed.

(* scratch ProgWorld_Fs.v:153-164 pw_rdword_bytes: rdword over the view, as ctrl's le8 word (astack's back-pointer). *)
Lemma pwfs_rdword_bytes : forall (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) (a v : Z),
  lib.Reusable.YG0d.rdword (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m) a = Some v ->
  0 <= a -> a + 8 <= 2 ^ 64 ->
  lib.Lib.Mem.bytes_at A.Img0.rsegs m a (lib.Lib.Mem.le8 (Z_to_bv 64 v)).
Proof.
  intros W m a v Hw Ha Hb.
  pose proof (lib.Reusable.YCbq.val_mem_of_rdword segs _ _ _ _ Hw) as Hv.
  apply (pwfs_word_of_view W m a v); [|exact Ha | exact Hb].
  intros k Hk. specialize (Hv k Hk).
  unfold lib.Reusable.YG0n.aview. rewrite Hv. cbn [option_map]. apply f_equal. rewrite pwfs_bv8.
  unfold lib.Reusable.YO0f.le_byte, lib.Reusable.YG0f.le_byte. apply Z.mod_mod. lia.
Qed.

(* scratch ProgWorld_Fs.v:179-188 pw_stk_of_present *)
Lemma pwfs_stk_of_present : forall (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) (lo hi : Z),
  0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) m a) ->
  lib.Lib.Frame.stk A.Img0.rsegs m lo hi.
Proof.
  intros W m lo hi Hlo Hhi Hp. split; [exact Hlo|]. split; [exact Hhi|].
  intros a Ha. destruct (Hp a Ha) as [_ (b & Hb)]. unfold lib.Lib.Mem.wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold lib.Lib.Mem.mrd. rewrite Hb. reflexivity.
Qed.

Lemma pwfs_mod8 : forall x, x mod 64 = 0 -> x mod 8 = 0.
Proof.
  intros x H. pose proof (Z.div_mod x 64 ltac:(lia)) as D. rewrite H in D. rewrite D.
  replace (64 * (x / 64) + 0) with ((8 * (x / 64)) * 8) by lia. apply Z.mod_mul. lia.
Qed.

Lemma pwfs_view_some0 : option_map (fun b : byte => bv_unsigned b) (Some (Z_to_bv 8 0)) = Some 0.
Proof. cbn [option_map]. rewrite pwfs_bv8. reflexivity. Qed.

Section Fs.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : lib.Reusable.YG0f.asyms.

(* scratch ProgWorld_Fs.v:204-210 pw_F_range: the side stack lies in application memory. *)
Lemma pwfs_F_range : forall ly, lib.Reusable.YG0f.in_app (lib.Reusable.YG0f.ly_F ly) lib.Reusable.YG0f.kFakeStackSize ->
  4096 <= lib.Reusable.YG0f.ly_F ly /\
  lib.Reusable.YG0f.ly_F ly + lib.Reusable.YG0f.kFakeStackSize <= 0x7fffff800000.
Proof.
  intros ly [H0 H]. pose proof lib.Reusable.YG0f.ASAN_CEIL_range as [CR _].
  unfold lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg in H. lia.
Qed.

(* scratch ProgWorld_Fs.v:212-219 pw_app_mem_F *)
Lemma pwfs_app_mem_F : forall ly a,
  lib.Reusable.YG0f.in_app (lib.Reusable.YG0f.ly_F ly) lib.Reusable.YG0f.kFakeStackSize ->
  lib.Reusable.YG0f.ly_F ly <= a < lib.Reusable.YG0f.ly_F ly + lib.Reusable.YG0f.kFakeStackSize -> A.AsanRT.app_mem a.
Proof.
  intros ly a [H0 H] Ha. pose proof lib.Reusable.YG0f.ASAN_CEIL_range as [CR _].
  unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END.
  unfold lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg in H. lia.
Qed.

(* scratch ProgWorld_Fs.v:221-223 pw_F_in_owned *)
Lemma pwfs_F_in_owned : forall ly,
  In (lib.Reusable.YG0f.ly_F ly, lib.Reusable.YG0f.kFakeStackSize) (lib.Reusable.YG0f.owned_extents ly).
Proof. intros ly. unfold lib.Reusable.YG0f.owned_extents. right; right; right; left. reflexivity. Qed.

(* scratch ProgWorld_Fs.v:225-234 pw_F_not_img *)
Lemma pwfs_F_not_img : forall ly a, lib.Reusable.YG0f.layout_ok ly ->
  lib.Reusable.YG0f.ly_F ly <= a < lib.Reusable.YG0f.ly_F ly + lib.Reusable.YG0f.kFakeStackSize ->
  ~ lib.Reusable.YG0n.in_zr a (lib.Reusable.YG0f.ly_img ly).
Proof.
  intros ly a LO Ha.
  assert (EX : Exists (lib.Reusable.YG0n.in_zr a) (lib.Reusable.YG0f.owned_extents ly)).
  { apply Exists_exists. exists (lib.Reusable.YG0f.ly_F ly, lib.Reusable.YG0f.kFakeStackSize).
    split; [apply pwfs_F_in_owned | unfold lib.Reusable.YG0n.in_zr; cbn [fst snd]; lia]. }
  exact (proj2 (proj2 (lib.Reusable.YG0s.owned_extents_bound ly a LO EX))).
Qed.

(* scratch ProgWorld_Fs.v:239-260 pw_F_above: the side stack is above the image (AR's layout keeps (ly_F,
   kFakeStackSize) apart from ly_img; ALedger's al_img puts every segment of A, the last ending at 0x5fe000 =
   ASAN_GT (A.ProgBridge.rsegs_spans), inside ly_img). *)
Lemma pwfs_F_above : forall ly S (W : lib.Reusable.YA0n.world segs) m md,
  lib.Reusable.YG0n.AR segs B ly S W m md -> A.Prog.asan_stack_malloc_c.ASAN_GT <= lib.Reusable.YG0f.ly_F ly.
Proof.
  intros ly S W m md (M & L & _).
  pose proof (lib.Reusable.YG0n.am_layout _ _ _ _ M) as LO.
  pose proof (lib.Reusable.YG0f.lo_img _ LO) as (I1 & I2 & I3 & I4).
  pose proof (proj1 (Forall_forall _ _) (lib.Reusable.YG0f.lo_app _ LO) _ (pwfs_F_in_owned ly)) as F1.
  cbn [fst snd] in F1. destruct (pwfs_F_range ly F1) as [F0 _].
  assert (Hm : In (659456, 5623808) (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) A.Img0.rsegs)).
  { rewrite A.ProgBridge.rsegs_spans. right; right; right; left. reflexivity. }
  apply in_map_iff in Hm as (sg & Es & Hsg). injection Es as E1 E2.
  pose proof (lib.Reusable.YG0n.al_img _ _ _ _ L sg Hsg) as [_ J2]. rewrite E1, E2 in J2.
  unfold A.Prog.asan_stack_malloc_c.ASAN_GT. unfold lib.Reusable.YG0f.kImgLo in I1.
  destruct (Z_lt_le_dec (lib.Reusable.YG0f.ly_F ly) 65536) as [Hlt|Hge].
  - exfalso. apply (pwfs_F_not_img ly 65536 LO); [unfold lib.Reusable.YG0f.kFakeStackSize; lia|].
    unfold lib.Reusable.YG0n.in_zr. lia.
  - destruct (Z_lt_le_dec (lib.Reusable.YG0f.ly_F ly)
      (fst (lib.Reusable.YG0f.ly_img ly) + snd (lib.Reusable.YG0f.ly_img ly))) as [Hlt2|Hge2].
    + exfalso. apply (pwfs_F_not_img ly (lib.Reusable.YG0f.ly_F ly) LO); [unfold lib.Reusable.YG0f.kFakeStackSize; lia|].
      unfold lib.Reusable.YG0n.in_zr. lia.
    + lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   ctl_fs_of_astack: after __asan_stack_malloc_<cid>, the frame facts ctrl's stretch takes at the return memory. *)
Lemma ctl_fs_of_astack : forall cid, A.ProgWorld.ctl_fs_of_astack_stmt B cid.
Proof.
  intros cid Hgeom ARL Hcid ly S S' W regs regs' mem mem' md md' pos lo L
    Hpre Hlo1 Hlo2 Hplo Hfr' Hnin HAR' Hr10 Hzs Hrdw Hpw Hframe HL.
  cbv zeta.
  pose proof Hpre as (HAR & _ & _ & Hsp1 & Hsp2 & _).
  assert (Hin' : In (cid, pos) (lib.Reusable.YG01.frames S')) by (rewrite Hfr'; left; reflexivity).
  pose proof HAR' as (M' & L' & _).
  destruct (lib.Reusable.YG0s.frame_facts B ly S' _ cid pos M' Hin')
    as (Hc10 & Hpos & HFapp & _ & HFal & Hfo1 & Hfo2 & Hfo64 & Hfb64 & Hfbm & Hflb).
  destruct (Hgeom (lib.Reusable.YG0f.ly_F ly) cid pos ltac:(lia)) as (G1 & G2 & G3 & G4 & _ & G6 & _).
  rewrite G1, G2, G3, G4, G6.
  change (lib.Reusable.YG0f.ly_F ly + lib.Reusable.YG0f.fs_frame_off cid pos)
    with (lib.Reusable.YG0f.frame_addr ly cid pos).
  change (lib.Reusable.YG0f.ly_F ly + lib.Reusable.YG0f.fs_flag_off cid pos)
    with (lib.Reusable.YG0f.flag_addr ly cid pos).
  assert (Efa : lib.Reusable.YG0f.frame_addr ly cid pos =
                lib.Reusable.YG0f.ly_F ly + lib.Reusable.YG0f.fs_frame_off cid pos) by reflexivity.
  assert (Efl : lib.Reusable.YG0f.flag_addr ly cid pos =
                lib.Reusable.YG0f.ly_F ly + lib.Reusable.YG0f.fs_flag_off cid pos) by reflexivity.
  destruct (pwfs_F_range ly HFapp) as [HF0 HF1].
  assert (Hfa64 : lib.Reusable.YG0f.frame_addr ly cid pos mod 64 = 0).
  { rewrite Efa. unfold lib.Reusable.YG0f.page_aligned in HFal.
    pose proof (Z.div_mod (lib.Reusable.YG0f.ly_F ly) 4096 ltac:(lia)) as D1.
    pose proof (Z.div_mod (lib.Reusable.YG0f.fs_frame_off cid pos) 64 ltac:(lia)) as D2.
    rewrite HFal in D1. rewrite Hfo64 in D2.
    replace (lib.Reusable.YG0f.ly_F ly + lib.Reusable.YG0f.fs_frame_off cid pos)
      with ((64 * (lib.Reusable.YG0f.ly_F ly / 4096) + lib.Reusable.YG0f.fs_frame_off cid pos / 64) * 64) by lia.
    apply Z.mod_mul. lia. }
  pose proof (pwfs_mod8 _ Hfa64) as Hfa8.
  pose proof (pwfs_mod8 _ Hfbm) as Hfb8.
  replace (2 ^ 20) with 1048576 in Hfo1 by reflexivity.
  unfold lib.Reusable.YG0f.kFakeStackSize, lib.Reusable.YG0f.kFakeFlagsOff, lib.Reusable.YG0f.kFakeFramesOff in *.
  set (fa := lib.Reusable.YG0f.frame_addr ly cid pos) in *.
  set (fl := lib.Reusable.YG0f.flag_addr ly cid pos) in *.
  set (n := lib.Reusable.YG00.fs_frame_bytes cid) in *.
  (* the frame's shadow bytes, used twice *)
  assert (Hsh : lib.Lib.Mem.bytes_at A.Img0.rsegs mem' (A.AsanRT.shadow_addr fa)
                  (repeat (Z_to_bv 8 0) (Z.to_nat (n / 8)))).
  { assert (Hd1 : fa / 8 <= fa) by (apply Z.div_le_upper_bound; lia).
    assert (Hd2 : n / 8 <= n) by (apply Z.div_le_upper_bound; lia).
    assert (Hd3 : 0 <= fa / 8) by (apply Z.div_pos; lia).
    assert (Hd4 : 0 <= n / 8) by (apply Z.div_pos; lia).
    apply (pwfs_bytes_of_view W).
    - unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K. lia.
    - rewrite repeat_length, Z2Nat.id by exact Hd4. unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K. lia.
    - intros i Hi. rewrite repeat_length in Hi. exists (Z_to_bv 8 0).
      split; [apply nth_error_repeat; exact Hi|].
      replace (A.AsanRT.shadow_addr fa) with (lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF fa)
        by (unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K, lib.Reusable.YG0v.shadow_of_addr,
              lib.Reusable.YG0f.SHADOW_OFF; lia).
      rewrite (Hzs (Z.of_nat i) ltac:(lia)). rewrite pwfs_bv8. reflexivity. }
  destruct (lib.Reusable.YG0d.al_frames _ _ ARL ly S' W mem' md' cid pos HAR' Hin') as (_ & _ & Hfb & _).
  split; [exact Hpos|].
  split; [exact Hr10|].
  split.
  { (* the flag byte reads 1: fs_flags_ok at S', where (cid, pos) is live *)
    assert (Hfl : lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) mem' fl = Some 1).
    { pose proof (lib.Reusable.YG0n.am_flags _ _ _ _ M' cid pos ltac:(lia) Hpos) as Hf.
      rewrite Hfr' in Hf. cbn [lib.Reusable.YG00.mem_pos] in Hf. rewrite !Z.eqb_refl in Hf. exact Hf. }
    apply (pwfs_byte_of_view W mem' _ 1 Hfl); lia. }
  split; [exact (pwfs_rdword_bytes W mem' _ _ Hrdw ltac:(lia) ltac:(lia))|].
  split; [exact Hsh|].
  split.
  { (* addressable: every shadow byte of [fa, fa + L) is 0 *)
    split; [lia|]. split; [lia|]. split; [unfold A.AsanRT.APPMEM_END; lia|].
    intros i Hi. split; [apply (pwfs_app_mem_F ly _ HFapp); unfold lib.Reusable.YG0f.kFakeStackSize; lia|].
    exists (Z_to_bv 8 0). split; [|left; vm_compute; reflexivity].
    pose proof Hsh as (_ & _ & Hs).
    assert (Hi8 : (Z.to_nat (i / 8) < length (repeat (Z_to_bv 8 0) (Z.to_nat (n / 8))))%nat).
    { rewrite repeat_length.
      assert (0 <= i / 8) by (apply Z.div_pos; lia).
      assert (i / 8 < n / 8).
      { apply Z.div_lt_upper_bound; [lia|].
        pose proof (Z.div_mod n 8 ltac:(lia)) as D. rewrite Hfb8 in D. lia. }
      lia. }
    replace (A.AsanRT.shadow_addr (fa + i)) with (A.AsanRT.shadow_addr fa + Z.of_nat (Z.to_nat (i / 8))).
    - rewrite (Hs _ Hi8). apply nth_error_repeat. rewrite repeat_length in Hi8. exact Hi8.
    - rewrite Z2Nat.id by (apply Z.div_pos; lia). unfold A.AsanRT.shadow_addr.
      pose proof (Z.div_mod fa 8 ltac:(lia)) as D. rewrite Hfa8 in D.
      replace (fa + i) with (i + (fa / 8) * 8) by lia. rewrite Z.div_add by lia. lia. }
  split; [apply (pwfs_stk_of_present W); [lia | lia | intros a Ha; exact (proj1 (Hfb a Ha))]|].
  split; [intros a Ha; apply (pwfs_app_mem_F ly _ HFapp); unfold lib.Reusable.YG0f.kFakeStackSize; lia|].
  split; [exact Hfa64|].
  split; [lia|].
  split; [lia|].
  split; [pose proof (pwfs_F_above ly S' W mem' md' HAR'); lia|].
  (* the caller's stack [lo, sp): the window by the post's presence clause, the rest by its frame condition *)
  pose proof (lib.Reusable.YG0n.am_layout _ _ _ _ M') as LO.
  destruct (lib.Reusable.YG0f.lo_top _ LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
  destruct (lib.Reusable.YG0f.lo_img _ LO) as (I1 & I2 & I3 & I4).
  unfold lib.Reusable.YG0f.kHighMemBeg, lib.Reusable.YG0f.kHighMemEnd, lib.Reusable.YG0f.kImgLo,
    lib.Reusable.YG0f.kImgEnd, lib.Reusable.YG0d.ESTACK in *.
  apply (pwfs_stk_of_present W); [lia | lia |].
  intros a Ha.
  destruct (Z_lt_le_dec a (lib.Reusable.YG0d.spZ regs - 4096)) as [Hlt|Hge];
    [|apply Hpw; lia].
  assert (Hst : lib.Reusable.YG0f.ly_stk_lo ly <= a < lib.Reusable.YG0f.ly_stk_hi ly) by lia.
  assert (Ha64 : 0 <= a < 2 ^ 64) by lia.
  pose proof (Hframe a Ha64 (lib.Reusable.YG0d.al_stack _ _ ARL ly S W mem md a HAR Hst)
    (lib.Reusable.YG0d.al_stack _ _ ARL ly S' W mem' md' a HAR' Hst) ltac:(lia)) as Ev.
  apply (lib.Reusable.YG0s.aview_present segs ly S' md' _ mem' a L' Ha64).
  - unfold lib.Reusable.YG0n.in_zr. lia.
  - rewrite Ev. exact (pwfs_present_view _ _ _ (Hplo a ltac:(lia))).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   ctl_release_of_free_law: the inline release as a journal step across a lifted silent run. *)
Lemma ctl_release_of_free_law : forall cid, A.ProgWorld.ctl_release_of_free_law_stmt (SK := SK) B cid.
Proof.
  intros cid ARL ASF _ _ STK sp0 FPj ly S W0 mem md own' lyc Sc W ms ms' mdc mdc' k pos RNG WR
    HJ Hrun Hfp Hm Hs Hwr Hflag0.
  destruct (A.ProgWorld.pws_fsteps_mem segs (lib.Reusable.YA0n.w_H W) RNG ms ms' Hrun Hfp) as [Hgr Hhid].
  pose proof (A.ProgWorld.pws_grows_mrestrict (lib.Reusable.YA0n.w_H W) _ _ Hgr) as Hgr'.
  pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
  assert (Hin : In (cid, pos) (lib.Reusable.YG01.frames Sc)) by (rewrite Hfrs; left; reflexivity).
  destruct (lib.Reusable.YG0d.al_flag _ _ ARL lyc Sc W (ms_mem ms) mdc cid pos HAR Hin) as (Hfp0 & Hfo & Hfapp & _).
  (* off the run's write set the view is kept (munch + footprint) *)
  assert (Heqw : forall a, 0 <= a < 2 ^ 64 -> ~ (0 <= a < 2 ^ 64 /\ ~ lib.Lib.Frame.outside WR a) ->
    lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) (ms_mem ms') a =
    lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) (ms_mem ms) a).
  { intros a Ha HWa. apply lib.Reusable.YCbq.aview_eq_of. unfold lib.Reusable.YK04.mrestrict.
    rewrite (Hm (Z_to_bv 64 a)); [reflexivity|]. rewrite (A.ProgWorld.pws_u64 a Ha).
    destruct (A.ProgWorld.pws_outside_dec WR a) as [Ho|Ho]; [exact Ho|].
    exfalso. apply HWa. split; [exact Ha | exact Ho]. }
  (* AR at the release state: astack_free_law (aj_flag_store's HAR', YCbq.v:2412-2422) *)
  assert (HAR' : lib.Reusable.YG0n.AR segs B lyc (lib.Reusable.YG01.stack_free_state cid pos Sc) W (ms_mem ms') mdc').
  { apply (ASF lyc Sc W (ms_mem ms) mdc (ms_mem ms') mdc' cid pos HAR Hin).
    - destruct Hfp0 as [Hh _].
      assert (E : lib.Reusable.YP09.mbyte segs (lib.Reusable.YK04.mrestrict (lib.Reusable.YA0n.w_H W) (ms_mem ms'))
                    (lib.Reusable.YG0f.flag_addr lyc cid pos) =
                  lib.Reusable.YP09.mbyte segs (ms_mem ms') (lib.Reusable.YG0f.flag_addr lyc cid pos)).
      { unfold lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict. rewrite Hh. reflexivity. }
      unfold lib.Reusable.YG0n.aview. rewrite E, Hflag0. exact pwfs_view_some0.
    - intros a Ha Ho Hne. apply Heqw; [exact Ha|]. intros [_ HWa].
      destruct (Hwr a Ha HWa) as [Hw | Hw]; [|exact (Hne Hw)].
      exact (proj1 (lib.Reusable.YCbq.awr_byte_cases (SK := SK) segs B ARL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) Ho).
    - intros a Hv. exact (lib.Reusable.YCbq.aview_keeps_vis segs _ _ _ a Hgr' Hv).
    - rewrite Hs. reflexivity.
    - rewrite Hs. reflexivity.
    - rewrite Hs. unfold lib.Reusable.YK04.eager_used. reflexivity.
    - intros a _ Hh. exact (Hhid _ Hh). }
  (* the journal at the store (aj_flag_store's ajournal_after_write, YCbq.v:2425-2435) *)
  apply (lib.Reusable.YCbq.ajournal_after_write (SK := SK) segs B ARL A.ProgWorld.pws_segs_low STK sp0 FPj ly S W0 mem md
    ((cid, pos) :: own') lyc Sc W (ms_mem ms) mdc k (ms_mem ms') mdc'
    (fun a => 0 <= a < 2 ^ 64 /\ ~ lib.Lib.Frame.outside WR a) (lib.Reusable.YG01.stack_free_state cid pos Sc) own'
    HJ Heqw).
  - intros a Ha. eapply lib.Reusable.YCbq.apresent_grows; [exact Hgr' | exact Ha].
  - exact Hs.
  - intros a [Ha Ho]. destruct (Hwr a Ha Ho) as [Hw | ->]; [left; exact Hw|].
    right. split; [exact Hfo|]. split.
    + apply (lib.Reusable.YG0f.in_app_addr _ 1 _ Hfapp). lia.
    + exact (proj2 (lib.Reusable.YG0d.al_client_img _ _ ARL lyc Sc W (ms_mem ms) mdc _ HAR
        (or_intror (or_intror (ex_intro _ cid (ex_intro _ pos (conj Hin eq_refl))))))).
  - exact HAR'.
  - unfold lib.Reusable.YG0d.ablocks. rewrite lib.Reusable.YG01.blocks_stack_free_state. reflexivity.
  - reflexivity.
  - cbn. lia.
  - change (lib.Reusable.YG01.frames (lib.Reusable.YG01.stack_free_state cid pos Sc))
      with (lib.Reusable.YG00.del_pos (lib.Reusable.YG01.frames Sc) cid pos).
    rewrite Hfrs. cbn [app lib.Reusable.YG00.del_pos]. rewrite !Z.eqb_refl. reflexivity.
  - apply (lib.Reusable.YG01.qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact HQT].
Qed.

End Fs.
