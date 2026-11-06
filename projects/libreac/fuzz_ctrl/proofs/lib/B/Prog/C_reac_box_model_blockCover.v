(* reac_box_model_block (image B, asan-ubsan, libreac v1.9.0), route (C): the REGION COVER of the glue switch.

   The narrowed run reac_box_model_block_holds_F takes `shadow_rw_on (reac_box_model_block_shadow_R (bv_unsigned sp) FS p
   b o row nb) m` (lib/B/Prog/reac_box_model_block_c_on.v), FS = ly_F ly.  At the class-0 return the glue holds
   B.ACtlRtC.ctl_rt_C B ly S m, whose 2nd and 3rd conjuncts are `shadow_rw_on (cut_shadow B ly S) m` and
   `shadow_rw_on img_shadow m` (lib/B/ACtlRtC.v).  mbB_R_cover puts every byte of R in cut_shadow B ly S or in
   img_shadow; mbB_R_on is the corollary the glue calls (ShadowRwOn's union and mono).

   R's disjunct                    covered by                     why
     window [S - 4272, S)          (Z), the stack's zero shadow   the window lies in the stack; the stack bounds are
                                                                  page-aligned (lo_top), so the 8-aligned word cover
                                                                  stays in the stack's shadow (the method of
                                                                  C_reac_box_model_blockVis.v:302-315)
     class-0 block of the side     (FA), the frames area          [sh (FS + 36864), + 131072) is inside
       stack (asan_stack_malloc_                                  [sh (FS + kFakeFramesOff), sh (FS + kFakeStackSize))
       shadow_R FS 0)
     row p, name, JOIN blocks      img_shadow                     image globals with 64-byte margins: the word cover
                                                                  of [x, x + n) lies in the shadow of
                                                                  [x - 64, x + n + 64)
     o in a frame of S             (F), that frame's shadow       0 <= cid (Wf), so the frame base and its size are
                                                                  multiples of 64 (ly_F page-aligned, lo_F_al) and the
                                                                  word cover stays in the frame's shadow
     o on the machine stack        (Z)                            as the window

   rule 24: no function proved (glue of the proved run reac_box_model_block_holds_F; lookup of record
   lookup-reac_box_model_block.txt (a working note, not in this delivery), CONFIRM in lookup-check.md (a working note, not in this delivery)). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YM05 YG00 YG01 YG0f YG0v YG0n YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require AsanRT ShadowRwOn ACtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcSynth.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require CtrlRo rng_asan sh_word_on asan_stack_malloc_c
  asan_stack_malloc_c_on reac_box_model_block_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_box_model_block_c_on.
Local Open Scope Z_scope.

(* ---- Word covers ------------------------------------------------------------------------------------------------ *)

(* The 8-aligned shadow word cover of [x, x + n) inside a 64-aligned zone [lo, lo + len) lies in the zone's shadow. *)
Lemma mbC_word_in : forall lo len x n a,
  lo mod 64 = 0 -> len mod 64 = 0 -> lo <= x -> x + n <= lo + len -> 0 <= n ->
  B.Prog.sh_word_on.sh_word_on x n a ->
  lib.Reusable.YG0f.SHADOW_OFF + lo / 8 <= a < lib.Reusable.YG0f.SHADOW_OFF + lo / 8 + len / 8.
Proof.
  intros lo len x n a Hlo Hlen H1 H2 H3 [Hn [Ha1 Ha2]].
  unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha1, Ha2.
  unfold lib.Reusable.YG0f.SHADOW_OFF.
  Z.div_mod_to_equations. lia.
Qed.

(* The same inside a page-aligned zone [lo, hi), in the form of a zero_shadow_ranges entry. *)
Lemma mbC_zone : forall lo hi x n a,
  lo mod 4096 = 0 -> hi mod 4096 = 0 -> lo <= x -> x + n <= hi -> 0 <= n ->
  B.Prog.sh_word_on.sh_word_on x n a ->
  lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF lo <= a <
  lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF lo + (hi - lo) / 8.
Proof.
  intros lo hi x n a Hlo Hhi H1 H2 H3 Hsw. unfold lib.Reusable.YG0v.shadow_of_addr.
  apply (mbC_word_in lo (hi - lo) x n a); [lia | lia | lia | lia | lia | exact Hsw].
Qed.

(* An image global with 64-byte margins: its word cover is image shadow. *)
Lemma mbC_img : forall x n a,
  B.Prog.CtrlRo.IMG_LO + 64 <= x -> x + n + 64 <= B.Prog.CtrlRo.IMG_HI -> 0 <= n ->
  B.Prog.sh_word_on.sh_word_on x n a -> B.ACtlRtC.img_shadow a.
Proof.
  intros x n a H1 H2 H3 [Hn [Ha1 Ha2]]. unfold B.ACtlRtC.img_shadow.
  exists (8 * (a - lib.Reusable.YG0f.SHADOW_OFF)).
  unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha1, Ha2.
  unfold B.Prog.CtrlRo.IMG_LO, B.Prog.CtrlRo.IMG_HI in *.
  unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF.
  split; [split|]; Z.div_mod_to_equations; lia.
Qed.

(* A frame of class cid >= 0: its base and its size are multiples of 64 (the side stack is page-aligned). *)
Lemma mbC_frame_al : forall ly cid pos,
  lib.Reusable.YG0f.page_aligned (lib.Reusable.YG0f.ly_F ly) -> 0 <= cid ->
  lib.Reusable.YG0f.frame_addr ly cid pos mod 64 = 0 /\ lib.Reusable.YG00.fs_frame_bytes cid mod 64 = 0.
Proof.
  intros ly cid pos HF Hc.
  unfold lib.Reusable.YG0f.frame_addr, lib.Reusable.YG0f.fs_frame_off, lib.Reusable.YG00.fs_frame_bytes,
    lib.Reusable.YG0f.kFakeFramesOff, lib.Reusable.YG00.kStackSizeLog, lib.Reusable.YG0f.page_aligned in *.
  replace (Z.shiftl 1 20) with 1048576 by reflexivity.
  rewrite Z.shiftl_mul_pow2 by lia.
  replace (pos * (64 * 2 ^ cid)) with (64 * (pos * 2 ^ cid)) by ring.
  set (j := pos * 2 ^ cid). set (k := 2 ^ cid).
  split; lia.
Qed.

Section Cover.
Context {rc : lib.Reusable.YM05.RunCeil}.
Variable B : lib.Reusable.YG0f.asyms.

(* A word cover inside the machine stack is (Z): the first zero_shadow_ranges entry (lib/Reusable/YG0n.v:188-189). *)
Lemma mbC_stk : forall ly S x n a,
  lib.Reusable.YG0f.layout_ok ly ->
  lib.Reusable.YG0f.ly_stk_lo ly <= x -> x + n <= lib.Reusable.YG0f.ly_stk_hi ly -> 0 <= n ->
  B.Prog.sh_word_on.sh_word_on x n a -> B.ACtlRtC.cut_shadow B ly S a.
Proof.
  intros ly S x n a LY H1 H2 H3 Hsw.
  pose proof (lib.Reusable.YG0f.lo_top _ LY) as (_ & _ & _ & _ & HALo & HAHi & _).
  unfold lib.Reusable.YG0f.page_aligned in HALo, HAHi.
  unfold B.ACtlRtC.cut_shadow. right; right; left.
  exists (lib.Reusable.YG0f.ly_stk_lo ly, lib.Reusable.YG0f.ly_stk_hi ly - lib.Reusable.YG0f.ly_stk_lo ly).
  split.
  - unfold lib.Reusable.YG0n.zero_shadow_ranges. left. reflexivity.
  - cbn [fst snd]. exact (mbC_zone _ _ x n a HALo HAHi H1 H2 H3 Hsw).
Qed.

(* A word cover of 32 bytes inside a frame of S of class cid >= 0 is (F): that frame's shadow. *)
Lemma mbC_frame : forall ly S cid pos o a,
  lib.Reusable.YG0f.layout_ok ly -> 0 <= cid -> In (cid, pos) (lib.Reusable.YG01.frames S) ->
  (forall x, o <= x < o + 32 -> lib.Reusable.YG0n.in_zr x (lib.Reusable.YCbq.frame_rng ly (cid, pos))) ->
  B.Prog.sh_word_on.sh_word_on o 32 a -> B.ACtlRtC.cut_shadow B ly S a.
Proof.
  intros ly S cid pos o a LY Hc Hin Hx Hsw.
  unfold B.ACtlRtC.cut_shadow. left. exists cid, pos. split; [exact Hin|].
  pose proof (Hx o ltac:(lia)) as X0. pose proof (Hx (o + 31) ltac:(lia)) as X1.
  unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YCbq.frame_rng in X0, X1. cbn [fst snd] in X0, X1.
  destruct (mbC_frame_al ly cid pos (lib.Reusable.YG0f.lo_F_al _ LY) Hc) as [A1 A2].
  unfold lib.Reusable.YG0f.shadow_addr.
  exact (mbC_word_in _ _ o 32 a A1 A2 ltac:(lia) ltac:(lia) ltac:(lia) Hsw).
Qed.

(* THE COVER.  Facts, as the glue holds them at the class-0 return (S = the state after the class-0 request):
     LY   layout_ok ly                               AR at (ly, S): ARm's am_layout (lib/Reusable/YG0n.v:209)
     WF   Wf (as_universe B) S                       AR at (ly, S): ARm's am_wf (lib/Reusable/YG0n.v:206)
     HWlo, HWhi  the window lies in the stack        spec fact (the window inside the machine stack)
     HP   the row's 64-byte image margins            spec fact
     HN   the name's 64-byte image margins           spec fact (under the name's guard)
     HO   o's home: a frame of S of class <> 0, or   spec fact, C_reac_box_model_block.tbmb_o_home's text with
          the machine stack                          frames S for frames Sc (frames S = (0, pos) :: frames Sc) *)
Lemma mbB_R_cover : forall ly S (sp : word) p b o (row nb : list byte) a
  (LY : lib.Reusable.YG0f.layout_ok ly)
  (WF : lib.Reusable.YG01.Wf (lib.Reusable.YG0f.as_universe B) S)
  (HWlo : lib.Reusable.YG0f.ly_stk_lo ly <= bv_unsigned sp - 4272)
  (HWhi : bv_unsigned sp <= lib.Reusable.YG0f.ly_stk_hi ly)
  (HP : p <> 0 -> B.Prog.CtrlRo.IMG_LO + 64 <= p /\ p + 296 + 64 <= B.Prog.CtrlRo.IMG_HI)
  (HN : p <> 0 -> (b = 5 \/ b = 6) -> lib.Prog.RcSynth.has row <> 0 -> lib.Prog.RcSynth.rname row <> 0 ->
        B.Prog.CtrlRo.IMG_LO + 64 <= lib.Prog.RcSynth.rname row /\
        lib.Prog.RcSynth.rname row + Z.of_nat (length nb) + 64 <= B.Prog.CtrlRo.IMG_HI)
  (HO : o <> 0 ->
        (exists cid pos, In (cid, pos) (lib.Reusable.YG01.frames S) /\ cid <> 0 /\
           forall x, o <= x < o + 32 -> lib.Reusable.YG0n.in_zr x (lib.Reusable.YCbq.frame_rng ly (cid, pos))) \/
        (lib.Reusable.YG0f.ly_stk_lo ly <= o /\ o + 32 <= lib.Reusable.YG0f.ly_stk_hi ly)),
  reac_box_model_block_shadow_R (bv_unsigned sp) (lib.Reusable.YG0f.ly_F ly) p b o row nb a ->
  B.ACtlRtC.cut_shadow B ly S a \/ B.ACtlRtC.img_shadow a.
Proof.
  intros ly S sp p b o row nb a LY WF HWlo HWhi HP HN HO HR.
  unfold reac_box_model_block_shadow_R, B.Prog.reac_box_model_block_c.REAC_BOX_MODEL_BLOCK_K in HR.
  destruct HR as [W | [C0 | [[Hp R] | [[Hp [Hb [Hh [Hr R]]]] | [[Ho R] | [[Hb R] | [Hb R]]]]]]].
  - (* the window: (Z) *)
    left. exact (mbC_stk ly S _ 4272 a LY HWlo ltac:(lia) ltac:(lia) W).
  - (* the class-0 block: (FA) *)
    left. unfold B.ACtlRtC.cut_shadow. right; right; right.
    unfold B.Prog.asan_stack_malloc_c_on.asan_stack_malloc_shadow_R, B.Prog.asan_stack_malloc_c.fs_frame,
      B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in C0.
    cbn [Z.of_nat] in C0. rewrite !Z.mul_0_l, !Z.add_0_r in C0.
    unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF, lib.Reusable.YG0f.kFakeFramesOff,
      lib.Reusable.YG0f.kFakeStackSize.
    Z.div_mod_to_equations. lia.
  - (* the row: image *)
    right. destruct (HP Hp) as [H1 H2]. exact (mbC_img p 296 a H1 ltac:(lia) ltac:(lia) R).
  - (* the name: image *)
    right. destruct (HN Hp Hb Hh Hr) as [H1 H2]. exact (mbC_img _ _ a H1 H2 ltac:(lia) R).
  - (* o: (F) in a frame of S, or (Z) on the machine stack *)
    left. destruct (HO Ho) as [(cid & pos & Hin & _ & Hx) | (H1 & H2)].
    + assert (LIVE := WF). unfold lib.Reusable.YG01.Wf in LIVE.
      apply lib.Reusable.YG01.wf_fakestack, lib.Reusable.YG01.wfs_live in LIVE.
      rewrite Forall_forall in LIVE. destruct (LIVE (cid, pos) Hin) as [[Hc _] _]. cbn [fst] in Hc.
      exact (mbC_frame ly S cid pos o a LY Hc Hin Hx R).
    + exact (mbC_stk ly S o 32 a LY H1 H2 ltac:(lia) R).
  - (* JOIN_0014: image *)
    right. refine (mbC_img _ 32 a _ _ ltac:(lia) R);
      unfold B.Prog.reac_box_model_block_c.JOIN_0014, B.Prog.CtrlRo.IMG_LO, B.Prog.CtrlRo.IMG_HI; lia.
  - (* JOIN_0013: image *)
    right. refine (mbC_img _ 32 a _ _ ltac:(lia) R);
      unfold B.Prog.reac_box_model_block_c.JOIN_0013, B.Prog.CtrlRo.IMG_LO, B.Prog.CtrlRo.IMG_HI; lia.
Qed.

(* The corollary the glue calls: ctl_rt_C's 2nd and 3rd conjuncts give the run's narrowed premise. *)
Lemma mbB_R_on : forall ly S (sp : word) p b o (row nb : list byte) (m : word -> option byte)
  (LY : lib.Reusable.YG0f.layout_ok ly)
  (WF : lib.Reusable.YG01.Wf (lib.Reusable.YG0f.as_universe B) S)
  (HWlo : lib.Reusable.YG0f.ly_stk_lo ly <= bv_unsigned sp - 4272)
  (HWhi : bv_unsigned sp <= lib.Reusable.YG0f.ly_stk_hi ly)
  (HP : p <> 0 -> B.Prog.CtrlRo.IMG_LO + 64 <= p /\ p + 296 + 64 <= B.Prog.CtrlRo.IMG_HI)
  (HN : p <> 0 -> (b = 5 \/ b = 6) -> lib.Prog.RcSynth.has row <> 0 -> lib.Prog.RcSynth.rname row <> 0 ->
        B.Prog.CtrlRo.IMG_LO + 64 <= lib.Prog.RcSynth.rname row /\
        lib.Prog.RcSynth.rname row + Z.of_nat (length nb) + 64 <= B.Prog.CtrlRo.IMG_HI)
  (HO : o <> 0 ->
        (exists cid pos, In (cid, pos) (lib.Reusable.YG01.frames S) /\ cid <> 0 /\
           forall x, o <= x < o + 32 -> lib.Reusable.YG0n.in_zr x (lib.Reusable.YCbq.frame_rng ly (cid, pos))) \/
        (lib.Reusable.YG0f.ly_stk_lo ly <= o /\ o + 32 <= lib.Reusable.YG0f.ly_stk_hi ly)),
  B.ShadowRwOn.shadow_rw_on (B.ACtlRtC.cut_shadow B ly S) m ->
  B.ShadowRwOn.shadow_rw_on B.ACtlRtC.img_shadow m ->
  B.ShadowRwOn.shadow_rw_on (reac_box_model_block_shadow_R (bv_unsigned sp) (lib.Reusable.YG0f.ly_F ly) p b o row nb) m.
Proof.
  intros ly S sp p b o row nb m LY WF HWlo HWhi HP HN HO HC HI.
  exact (B.ShadowRwOn.shadow_rw_on_mono _ _ m
           (fun a => mbB_R_cover ly S sp p b o row nb a LY WF HWlo HWhi HP HN HO)
           (B.ShadowRwOn.shadow_rw_on_union _ _ m HC HI)).
Qed.

End Cover.

Print Assumptions mbB_R_cover.
Print Assumptions mbB_R_on.
